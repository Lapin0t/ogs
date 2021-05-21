Require Import RelationClasses.
From ExtLib.Structures Require Import Functor Monad.
From ExtLib.Data Require Import Nat Fin.
From ITree Require Import
     ITree
     Events.Dependent
     Eq.Eq
     Interp.InterpFacts
     Interp.RecursionFacts
     Interp.TranslateFacts.
Import Monads.
Import MonadNotation.
Open Scope monad_scope.

From Paco Require paco2 paconotation.
From Equations Require Import Equations.

Set Primitive Projections.

From OGS Require Import Utils.



(* ======================================= *)
(* Terms, contexts, substitution, renaming *)
(* ======================================= *)

Variant termF (X : Type) : Type :=
| VarF : nat -> termF X
| AppF : X -> X -> termF X
| LamF : X -> termF X
.

Arguments VarF {X}.
Arguments AppF {X}.
Arguments LamF {X}.

Equations tmap {X Y} (f : X -> Y) (t : termF X) : termF Y :=
  tmap f (VarF i) := VarF i;
  tmap f (AppF u v) := AppF (f u) (f v);
  tmap f (LamF u) := LamF (f u).

Inductive term : Type := T : termF term -> term.

Notation Var i := (T (VarF i)).
Notation App u v := (T (AppF u v)).
Notation Lam u := (T (LamF u)).

Inductive t_ctx (X : Type) : Type :=
| CHole : t_ctx X
| CApp_l : X -> t_ctx X -> t_ctx X
| CApp_r : t_ctx X -> X -> t_ctx X
| CLam : t_ctx X -> t_ctx X
.

(* /!\ not capture avoiding, rename beforehand or use t_subst *)
Equations plug (C : t_ctx term) (x : term) : term :=
  plug CHole        t := t ;  (* dumb *)
  plug (CApp_l u C) t := App u (plug C t) ;
  plug (CApp_r C u) t := App (plug C t) u ;
  plug (CLam C)     t := Lam (plug C t).

(* multi-renaming *)
Equations t_rename (f : nat -> nat) (t : term) : term :=
  t_rename f (Var i)   := Var (f i) ;
  t_rename f (App u v) := App (t_rename f u) (t_rename f v) ;
  t_rename f (Lam u)   := Lam (t_rename f' u)
    where f' : nat -> nat := {
          f' O     := O ;
          f' (S i) := S (f i) }.

(* multi-substitution *)
Equations t_subst (f : nat -> term) (t : term) : term :=
  t_subst f (Var i)   := f i ;
  t_subst f (App u v) := App (t_subst f u) (t_subst f v) ;
  t_subst f (Lam u)   := Lam (t_subst f' u)
    where f' : nat -> term := {
          f' O     := Var O ;
          f' (S i) := t_rename S (f i) }.

Equations env1 (u : term) : nat -> term :=
  env1 u O     := u ;
  env1 u (S i) := Var i.

(* mono-substitution *)
Definition t_subst1 u v := t_subst (env1 v) u.

(* 'app_many t [u_0, u_1, ... u_n]' == 't u_n ... u_1 u_0' *)
Equations app_many : term -> list term -> term :=
  app_many a nil         := a ;
  app_many a (cons x xs) := App (app_many a xs) x.


Section normal_cbv.

(* =============================== *)
(* evaluation to normal form (CBV) *)
(* =============================== *)

Variant normF (X : Type) : Type :=
| NLamF : X -> normF X
| NAppF : nat -> list X -> normF X.
Arguments NLamF {X}.
Arguments NAppF {X}.

Inductive nf : Type := N : normF nf -> nf.
Notation NLam u := (N (NLamF u)).
Notation NApp i xs := (N (NAppF i xs)).

Equations term_of_nf (u : nf) : term :=
  term_of_nf (NLam u)    := Lam (term_of_nf u) ;
  term_of_nf (NApp i xs) := app_many (Var i) (List.map term_of_nf xs).

Equations eval_nf' (t : term) : itree (callE term nf +' void1) nf :=
  eval_nf' (Var i) := ret (NApp i nil) ;
  eval_nf' (App u v) :=
    u' <- call u ;;
    v' <- call v ;;
    match u' with
    | NLam w => call (t_subst1 (term_of_nf w) (term_of_nf v'))
    | NApp i xs => ret (NApp i (cons v' xs))
    end ;
  eval_nf' (Lam u) := u' <- call u ;; ret (NLam u').

Definition eval_nf : term -> itree void1 nf := rec eval_nf'.

Definition eutt_bind_eq {E R U} (t1 t2 : itree E U) (k : U -> itree E R) 
             (h : t1 ≈ t2) : t1 >>= k ≈ t2 >>= k.
  eapply eutt_clo_bind.
  exact h.
  intros ? ? e; rewrite e; reflexivity.
Qed.

#[local] Transparent plug.
#[local] Transparent eval_nf'.

Lemma eval_nf_congr (s t : term) (p : eval_nf s ≈ eval_nf t) (C : t_ctx term)
  : eval_nf (plug C s) ≈ eval_nf (plug C t).
  induction C; cbn.
  + (* CHole *) exact p.
  + (* CApp_l x C *)
    unfold eval_nf; rewrite 2 rec_as_interp; cbn.
    rewrite 2 interp_bind; apply eutt_eq_bind; intro u.
    rewrite 2 interp_bind; eapply eutt_bind_eq.
    rewrite 2 interp_recursive_call; exact IHC.
  + (* CApp_r C x *)
    unfold eval_nf; rewrite 2 rec_as_interp; cbn.
    rewrite 2 interp_bind; eapply eutt_bind_eq.
    rewrite 2 interp_recursive_call; exact IHC.
  + (* CLam C *)
    unfold eval_nf; rewrite 2 rec_as_interp; cbn.
    rewrite 2 interp_bind; eapply eutt_bind_eq.
    rewrite 2 interp_recursive_call; exact IHC.
Qed.
End normal_cbv.


Section eager_lassen.

(* =============================================== *)
(* eager normal form bisimulation, ie Lassen trees *)
(* =============================================== *)

Inductive value : Type :=
| VVar : nat -> value
| VLam : term -> value
.

Equations term_of_value (v : value) : term :=
  term_of_value (VVar i) := Var i ;
  term_of_value (VLam t) := Lam t .

Definition val_app_fresh (v : value) : term :=
  App (t_rename S (term_of_value v)) (Var O).

Inductive eager_ctx : Type :=
| ECHole : eager_ctx
| ECApp_l : term -> eager_ctx -> eager_ctx
| ECApp_r : eager_ctx -> value -> eager_ctx
.

Equations ec_plug (C : eager_ctx) (t : term) : term :=
  ec_plug ECHole t := t ;
  ec_plug (ECApp_l u C) t := App u (ec_plug C t) ;
  ec_plug (ECApp_r C v) t := App (ec_plug C t) (term_of_value v) .

(* fill the hole (metavar) with a fresh variable *)
Equations ec_fresh (C : eager_ctx) : term :=
  ec_fresh ECHole        := Var 0;
  ec_fresh (ECApp_l t C) := App (t_rename S t) (ec_fresh C) ;
  ec_fresh (ECApp_r C v) := App (ec_fresh C) (t_rename S (term_of_value v)).

(* decomposition of a term as either a value or E[v1 v2] *)
Inductive eager_term : Type :=
| EValue : value -> eager_term
| ERedex : eager_ctx -> value -> value -> eager_term
.
Derive NoConfusion for eager_term.

Equations term_of_eterm (e : eager_term) : term :=
  term_of_eterm (EValue v)       := term_of_value v ;
  term_of_eterm (ERedex C v0 v1) :=
    ec_plug C (App (term_of_value v0) (term_of_value v1)) .

Equations ectx_split (t : term) : eager_term :=
  ectx_split (Var i)   := EValue (VVar i) ;
  ectx_split (Lam u)   := EValue (VLam u) ;
  ectx_split (App u v) with ectx_split v := {
    | EValue v0 with ectx_split u := {
      | EValue u0 := ERedex ECHole u0 v0 ;
      | ERedex C u0 u1 := ERedex (ECApp_r C v0) u0 u1 } ;
    | ERedex C v0 v1 := ERedex (ECApp_l u C) v0 v1 }.
#[local] Transparent ectx_split.

Lemma ectx_split_val (v : value) : ectx_split (term_of_value v) = EValue v.
  destruct v; auto.
Qed.

Lemma ectx_split_app u v : { C : _ & { v0 : _ & { v1 : _ & ectx_split (App u v) = ERedex C v0 v1 }}}.
  cbn; destruct (ectx_split v) eqn:d1;
  cbn; [destruct (ectx_split u) eqn:d2|];
  cbn; repeat econstructor; auto.
Qed.

#[local] Transparent term_of_eterm.
#[local] Transparent term_of_value.
#[local] Transparent ec_plug.
Lemma ectx_split_correct (t : term) : term_of_eterm (ectx_split t) = t.
  funelim (ectx_split t);
  intros; cbn; repeat f_equal;
  first [ rewrite Heq in Hind;   exact Hind
        | rewrite Heq0 in Hind0; exact Hind0 ].
Qed.

Lemma ectx_split_coherent (t : eager_term) : ectx_split (term_of_eterm t) = t.
funelim (term_of_eterm t).
+ exact (ectx_split_val v).
+ revert v0 v1.
  induction e; intros v0 v1; cbn.
  destruct (ectx_split (term_of_value v1)) eqn:?; cbn;
    rewrite (ectx_split_val v1) in Heqe;
    try (discriminate Heqe); 
    injection Heqe as H; rewrite H.
  - destruct (ectx_split (term_of_value v0)) eqn:?; cbn;
      rewrite (ectx_split_val v0) in Heqe;
      try (discriminate Heqe).
    injection Heqe as H0.
    rewrite H0; reflexivity.
  - rewrite (IHe v0 v1); reflexivity.
  - destruct (ectx_split (term_of_value v)) eqn:He; cbn;
      rewrite (ectx_split_val v) in He;
      try (discriminate He).
    injection He as H; rewrite H.
    rewrite (IHe v0 v1); reflexivity.
Qed.

Lemma ectx_split_unique {x y} : x = term_of_eterm y <-> ectx_split x = y.
  econstructor; intro p.
  rewrite<- (ectx_split_coherent y); f_equal; exact p.
  rewrite<- (ectx_split_correct x); f_equal; exact p.
Qed.

Lemma ectx_split_inj {x y} (p : ectx_split x = ectx_split y) : x = y.
  rewrite<- ectx_split_correct, ectx_split_unique.
  exact p.
Qed.

Equations ec_compose (C D : eager_ctx) : eager_ctx :=
  ec_compose ECHole        D := D ;
  ec_compose (ECApp_l t C) D := ECApp_l t (ec_compose C D) ;
  ec_compose (ECApp_r C v) D := ECApp_r (ec_compose C D) v .
#[local] Transparent ec_compose.

Equations ec_plug_e (C : eager_ctx) (x : eager_term) : eager_term :=
  ec_plug_e C (EValue v)        := ectx_split (ec_plug C (term_of_value v)) ;
  ec_plug_e C (ERedex C' v0 v1) := ERedex (ec_compose C C') v0 v1.
#[local] Transparent ec_plug_e.

Lemma ec_plug_e_hole {x} : ec_plug_e ECHole x = x.
  destruct x.
  exact (ectx_split_val _).
  auto.
Qed.

Lemma ectx_split_plug (C : eager_ctx) (t : term) : ectx_split (ec_plug C t) = ec_plug_e C (ectx_split t).
destruct (ectx_split t) eqn:He; cbn; rewrite<- ectx_split_unique in He.
- rewrite He; reflexivity.
- rewrite<- ectx_split_unique.
  induction C; cbn; try (f_equal; f_equal); auto.
Qed.

Lemma ec_plug_e_inv_val {C x v} (p : ec_plug_e C x = EValue v) : C = ECHole /\ x = EValue v.
  rewrite<- (@ectx_split_coherent x) in p.
  rewrite<- ectx_split_plug in p.
  rewrite<- ectx_split_unique in p; cbn in p.
  induction C; try (destruct v; cbn in p; discriminate p).
  cbn in p; symmetry in p; rewrite ectx_split_unique in p.
  rewrite ectx_split_val in p.
  rewrite p; auto.
Qed.

(*Lemma ec_plug_e_inv_red {C x C' i v} (p : ec_plug_e C x = ERedex C' i v) :*)
  


Variant enf : Type :=
| ENValue : value -> enf
| ENRedex : eager_ctx -> nat -> value -> enf.

Equations term_of_enf (e : enf) : term :=
  term_of_enf (ENValue v)     := term_of_value v ;
  term_of_enf (ENRedex C i v) := ec_plug C (App (Var i) (term_of_value v)) .

Equations eval_enf' (t : term) : itree (callE term enf +' void1) enf :=
  eval_enf' t with ectx_split t := {
    | EValue v            := ret (ENValue v) ;
    | ERedex C (VVar i) v := ret (ENRedex C i v) ;
    | ERedex C (VLam u) v := call (ec_plug C (t_subst1 u (term_of_value v)))
  }.
Definition eval_enf : term -> itree void1 enf := rec eval_enf'.

Lemma eval_enf_congr (C : eager_ctx) {t1 t2} (p : eval_enf t1 ≈ eval_enf t2)
  : eval_enf (ec_plug C t1) ≈ eval_enf (ec_plug C t2).
Admitted.

Inductive enfE : Type -> Type :=
| ENValE : enfE T1
| ENRedexE : nat -> enfE T2.

(* helpers for lassen-tree events *)
Definition ENValT {X} (t : itree enfE X) : itree enfE X :=
  Vis ENValE (fun x : T1 => match x with t1_0 => t end).
Definition ENRedexT {X} (i : nat) (t0 t1 : itree enfE X) : itree enfE X :=
  Vis (ENRedexE i) (fun x : T2 => match x with t2_0 => t0 | t2_1 => t1 end).

Definition lassen_val (v : value) : itree enfE (term + T0) :=
  ENValT (ret (inl (App (t_rename S (term_of_value v)) (Var O)))) .

Equations lassen_enf (t : enf) : itree enfE (term + T0) :=
  lassen_enf (ENValue v)     := lassen_val v ;
  lassen_enf (ENRedex C i v) := ENRedexT i (ret (inl (ec_fresh C))) (lassen_val v).

Definition eval_lassen : term -> itree enfE T0 :=
  ITree.iter (fun t => translate elim_void1 (eval_enf t) >>= lassen_enf).

Definition eqv_lassen (x y : term) : Prop := eval_lassen x ≈ eval_lassen y.

(* ============================= *)
(* representing values as leaves *)
(* ============================= *)

Inductive enfE_v : Type -> Type := ENRedexE_v : nat -> enfE_v T2.
Definition ENRedexT_v {X} (i : nat) (t0 t1 : itree enfE_v X) : itree enfE_v X :=
  Vis (ENRedexE_v i) (fun x : T2 => match x with t2_0 => t0 | t2_1 => t1 end).

Equations enfE_v_inj {X} : enfE_v X -> enfE X :=
  enfE_v_inj (ENRedexE_v i) := ENRedexE i.
Definition lassen_v_inj {X} : itree enfE_v X -> itree enfE X :=
  @translate _ _ (@enfE_v_inj) X.

Equations lassen_enf_v (t : enf) : itree enfE_v (term + value) :=
  lassen_enf_v (ENValue v)     := Ret (inr v) ;
  lassen_enf_v (ENRedex C i v) := ENRedexT_v i (Ret (inl (ec_fresh C)))
                                               (Ret (inr v)).

Definition eval_lassen_v : term -> itree enfE_v value :=
  ITree.iter (fun t => translate elim_void1 (eval_enf t) >>= lassen_enf_v).

(* unfold leaves by coinductively eta-expanding values *)
Definition expand_v : itree enfE_v value -> itree enfE T0 :=
  ITree.iter (fun t => v <- lassen_v_inj t ;;
                       Ret (inl (eval_lassen_v (val_app_fresh v)))).
  (*cofix expand_ t := ITree.bind (lassen_v_inj t)
                                (tau # expand_ # eval_lassen_v # val_app_fresh).*)

Equations _expand_v : itree' enfE_v value -> itree enfE T0 :=
  _expand_v (RetF r) := tau (expand_v (eval_lassen_v (val_app_fresh r))) ;
  _expand_v (TauF t) := tau (expand_v t) ;
  _expand_v (VisF e k) := Vis (enfE_v_inj e) (fun r => expand_v (k r)).

Lemma unfold_expand_v (x : itree enfE_v value) : expand_v x ≅ _expand_v (observe x).
  unfold expand_v ; rewrite unfold_iter; cbn.
  change (ITree.iter _) with (expand_v).
  unfold lassen_v_inj.
  rewrite unfold_translate.
  rewrite unfold_bind.
  destruct (observe x) eqn:?; cbn.
  + reflexivity.
  + unfold expand_v; change (translate _ _) with (lassen_v_inj t); cbn.
    rewrite<- (unfold_iter (fun t => ITree.bind (lassen_v_inj t) _)).
    change (ITree.iter _ t) with (expand_v t).
    reflexivity.
  + rewrite _expand_v_equation_3.
    apply eqit_Vis; intro r.
    unfold expand_v; change (translate _ _) with (lassen_v_inj (k r)); cbn.
    rewrite<- (unfold_iter (fun t => ITree.bind (lassen_v_inj t) _) (k r)).
    reflexivity.
Qed.

Lemma eval_lassen_v_lem (x : term) : eval_lassen x ≈ expand_v (eval_lassen_v x).
  Admitted.

(* LassenV trees are bisimilar and coinductively, leaves (values) applied to 
   a fresh variable have bisimilar lassen' trees. *)
Definition eqv_lassen_v : term -> term -> Prop :=
  paco2.paco2 (fun R x y => eutt (fun v1 v2 => R (val_app_fresh v1) (val_app_fresh v2))
                           (eval_lassen_v x)
                           (eval_lassen_v y))
        paconotation.bot2.

Lemma eqv_lassen_v_lem (x y : term) :
  eqv_lassen_v x y <-> expand_v (eval_lassen_v x) ≈ expand_v (eval_lassen_v y).
Admitted.

Lemma eqv_lassen_v_correct (x y : term) : eqv_lassen_v x y <-> eqv_lassen x y.
  unfold eqv_lassen; rewrite 2 eval_lassen_v_lem.
  exact (eqv_lassen_v_lem x y).
Qed.

End eager_lassen.

Section OGS.
  Variable idx : Type.           (* contexte de typage des configurations *)
  Variable conf : idx -> Type.    (* configurations *)
  Variable PA : idx -> Type.      (* actions joueur *)
  Variable OA : idx -> Type.      (* actions opposant *)
  Variable Pnxt : forall i, PA i -> idx.  (* évolution du contexte de typage, joueur *)
  Variable Onxt : forall i, OA i -> idx.  (* évolution du contexte de typage, opposant *)

  Definition NEXT i : Type := { pa : PA i & conf (Pnxt i pa) }.

  (* stratégie: étant donné une configuration et une action opposant,
     donner un calcul ([itree void1]) retournant une action joueur ainsi
     qu'une nouvelle configuration *)
  Definition STRAT : Type :=
    forall {i} (c : conf i) (oa : OA i), itree void1 (NEXT (Onxt i oa)). 

  Variant ogsE : Type -> Type :=
  | StepE i (pa : PA i) : ogsE (OA (Pnxt i pa)).
  (*| StepP : PA -> ogsE T1.*)

  Definition eval_ogs (f : STRAT) : { i & (conf i * OA i)%type } -> itree ogsE T0.
  refine (rec (fun c => _ )).
  destruct c as [i [c o]].
  refine (x <- translate elim_void1 (f i c o) ;; _).
  refine (Vis (inr1 (StepE _ (projT1 x))) (fun o' => _)).
  refine (call (existT _ _ ((projT2 x) , o'))).
  Defined.
End OGS.    

Section OGS_cbv.

Variant K_ty : Type := KCtx | KVal. 
Equations kty_e : K_ty -> Type :=
  kty_e KCtx := eager_ctx ;
  kty_e KVal := value.
Variant PA_cbv : Type := PVal | PRed (i : nat).

Definition idx_cbv : Type := list K_ty.
Definition conf_cbv : idx_cbv -> Type := dvec kty_e.

Definition OA_cbv (c : idx_cbv) : Type := fin (length c).
Equations nxt_cbv i (oa : OA_cbv i) : PA_cbv -> idx_cbv :=
  nxt_cbv xs _ PVal     := cons KVal xs ;
  nxt_cbv xs _ (PRed i) := cons KCtx (cons KVal xs).
#[local] Transparent nxt_cbv.

(*
Definition ogsE_cbv := ogsE idx_cbv OA_cbv PA_cbv.
Definition STRAT_cbv := STRAT _ conf_cbv OA_cbv PA_cbv nxt_cbv.
Definition NEXT_cbv {i} oa := @NEXT _ conf_cbv OA_cbv PA_cbv nxt_cbv i oa.

Equations strat_enf {i} (c : conf_cbv i) oa : enf -> @NEXT_cbv i oa :=
  strat_enf c _ (ENValue v)     := {| N_play := PVal ; N_conf := _ |} ;
  strat_enf c _ (ENRedex C i v) := {| N_play := (PRed i) ; N_conf := _ |}.
Obligation 1.
unfold conf_cbv; rewrite dvec_equation_2.
exact (v , c).
Defined.
Obligation 2.
unfold conf_cbv. rewrite 2 dvec_equation_2.
exact (C , (v , c)).
Defined.

Definition strat_cbv : STRAT _ conf_cbv OA_cbv PA_cbv nxt_cbv.
  unfold STRAT; intros; unfold OA_cbv in oa.
  destruct (l_get i oa) eqn:H; set (x := d_get i c oa); rewrite H in x.
  + exact (ITree.map (strat_enf c oa) (eval_enf (ec_fresh x))).
  + exact (ITree.map (strat_enf c oa) (eval_enf (App (t_rename S (term_of_value x))
                                                     (Var O)))).
Defined.

Definition eval_ogs_cbv (t : term) : itree ogsE_cbv T0.
  refine (ITree.bind (translate elim_void1 (eval_enf t)) (fun e => _)).
  refine (eval_ogs _ _ _ _ _ strat_cbv _).
  destruct e eqn:?.
  + exact (existT _ (cons KVal nil) (v , t1_0)).
  + refine (existT _ (cons KCtx (cons KVal xs))).
  destruct (@strat_enf nil e).

bad
*)
End OGS_cbv.
(* ================ *)



Variant FreeF (E : Type -> Type) (A : Type) (X : Type) : Type :=
| FRetF : forall (r : X), FreeF E A X
| FVisF : forall {R} (e : E R) (k : R -> A), FreeF E A X
.
Arguments FRetF {_} {_} {_}.
Arguments FVisF {_} {_} {_} {_}.

Inductive Free (E : Type -> Type) (X : Type) : Type :=
| F : FreeF E (Free E X) X -> Free E X
.
Arguments F {_} {_}.
Notation FRet r := (F (FRetF r)).
Notation FVis e k := (F (FVisF e k)).

Definition unfold1 {E X} : itree E X -> itree void1 (FreeF E (itree E X) X) :=
  cofix _unfold x :=
    match observe x with
    | RetF r => Ret (FRetF r)
    | TauF t => Tau (_unfold t)
    | VisF e k => Ret (FVisF e k)
    end.



  
    
  




(*Definition explore {E}*)

(* ============== *)
(* old left-overs *)
(* ============== *)

(** comment until EOF

(* Weak Head Normal Form *)
Variant whnf : Type := W : normF term -> whnf.
Notation WLam u := (W (NLamF u)).
Notation WApp i xs := (W (NAppF i xs)).

(* boehm tree encoded as itrees *)
Variant boehmE : Type -> Type :=
| BLamE : boehmE T1
| BAppE : forall i j : nat, boehmE (fin j).

Definition boehm_tree := itree boehmE T0.

Definition BLam {X} u : itree boehmE X :=
  Vis BLamE (fun x => match x with t1_0 => u end).
Definition BApp {X} i xs : itree boehmE X :=
  Vis (BAppE i (length xs)) (l_get xs).

Equations term_of_whnf (w : whnf) : term :=
  term_of_whnf (WLam u) := Lam u ;
  term_of_whnf (WApp i xs) := app_many (Var i) xs.

(* Non-total function computing the whnf of a term by CBN reduction *)
Equations eval_whnf' (t : term) : itree (callE term whnf +' void1) whnf :=
  eval_whnf' (Var i) := ret (WApp i nil) ;
  eval_whnf' (App u v) :=
    u' <- call u ;;
    match u' with
    | WLam w => call (t_subst1 w v)
    | WApp i xs => ret (WApp i (cons v xs))
    end ;
  eval_whnf' (Lam u) := ret (WLam u).

Definition eval_whnf : term -> itree void1 whnf := rec eval_whnf'.


(* w_inj k (W x) := wrap (F2E (fmap k x)) *)
(* this is because normF == [ boehmE ]e *)
Equations w_inj {X} : (term -> itree boehmE X) -> whn -> itree boehmE X :=
  w_inj k (WLam u) := Vis BLamC (fun x => match x with t1_0 => k u end);
  w_inj k (WApp i xs) := Vis (BAppC i (length xs)) (k # l_get xs).

(* magic :D *)
Definition lassen' (t : term) : itree boehmE (term + T0) :=
  ITree.bind (translate elim_void1 (ev_whn t)) (w_inj (ret # inl)).
Definition lassen : term -> normT := iter lassen'.

Variant eqv_whn : whn -> whn -> Prop :=
  | Eqv_wlam : forall u v, eutt eq (lassen u) (lassen v) -> eqv_whn (WLam u) (WLam v)
  | Eqv_wapp : forall i n f g, (forall j, eutt eq (lassen (f j)) (lassen (g j)))
             -> eqv_whn (WApp i (l_acc n f)) (WApp i (l_acc n g))
.

Equations elim_r {T} (x : T + T0) : T := elim_r (inl t) := t.

(*
Lemma boehmE'_cong {C : t_ctx term} (s t : term) (p : lassen s ≈ lassen t)
  : eutt (fun a b => lassen (elim_r a) ≈ lassen (elim_r b))
         (lassen' (plug C s))
         (lassen' (plug C t)).
  induction C.
  + rewrite 2 plug_equation_1.
*)

Lemma boehmE_cong {C : t_ctx term} (s t : term) (p : lassen s ≈ lassen t)
  : lassen (plug C s) ≈ lassen (plug C t).
  induction C.
  + rewrite 2 plug_equation_1.
    exact p.
  + rewrite 2 plug_equation_2.
    reflexivity.
  + rewrite 2 plug_equation_3.
    unfold lassen, ";;", iter, MonadIter_itree; simpl.
    rewrite 2 unfold_iter.
    eapply eutt_clo_bind.
    * unfold lassen', ev_whn.
      rewrite 2 rec_as_interp.
      eapply eutt_clo_bind.
      - eapply eutt_translate'.
        rewrite 2 ev_whn'_equation_2; unfold ";;"; simpl.
        rewrite 2 interp_bind.
        eapply eutt_clo_bind.
          reflexivity.
          intros u1 u2 e.
          rewrite 2 interp_bind.
          eapply eutt_clo_bind.
          rewrite 2 interp_recursive_call.
          fold ev_whn.
          
      eapply eutt_clo_bind.
      - rewrite 2 interp_bind.
        Search translate.
        eapply eutt_translate'.
      Search translate.
  unfold lassen, ";;", iter, MonadIter_itree; simpl.
  rewrite 2 unfold_iter.
  rewrite 2 bind_bind.
  + 
  Search ITree.iter.
  induction C.
    Search ITree.iter.
    rewrite 2 unfold_iter.
    rewrite 2 bind_bind; simpl.
  
  + rewrite plug_equation_1,plug_equation_1.
    exact (@RelationClasses.reflexivity _ _ (Reflexive_eqit eq _ _ _) _).
  + rewrite plug_equation_2,plug_equation_2.
    compute [lassen].
    rewrite unfold_iter,unfold_iter.
    Search ITree.iter.

**)
