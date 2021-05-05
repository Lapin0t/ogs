From Coq.Logic Require Import FunctionalExtensionality.
Require Import RelationClasses.
From ExtLib.Structures Require Import Functor Monad.
From ExtLib.Data Require Import Nat Fin.
From ITree Require Import
     ITree
     Events.Dependent
     Basics.Basics
     Eq.Eq
     Interp.InterpFacts
     Interp.RecursionFacts
     Interp.TranslateFacts.
Import Monads.
Import MonadNotation.
Open Scope monad_scope.

From Paco Require Import paco.
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
    | EValue v1 with ectx_split u := {
      | EValue u0 := ERedex ECHole u0 v1 ;
      | ERedex C u0 u1 := ERedex (ECApp_r C v1) u0 u1 } ;
    | ERedex C v0 v1 := ERedex (ECApp_l u C) v0 v1 }.

Lemma ectx_split_val (v : value) : ectx_split (term_of_value v) = EValue v.
  destruct v; auto.
Qed.

#[local] Transparent ectx_split.
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
  econstructor.
  - intro p.
    rewrite<- ectx_split_coherent.
    f_equal; exact p.
  - intro p.
    rewrite<- ectx_split_correct at 1.
    f_equal; exact p.
Qed.

Lemma ectx_split_inj {x y} : ectx_split x = ectx_split y -> x = y.
  intro p.
  rewrite<- ectx_split_unique in p.
  rewrite ectx_split_correct in p.
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
  + exact (ectx_split_val _).
  + auto.
Qed.

Lemma ectx_split_plug (C : eager_ctx) (t : term) : ectx_split (ec_plug C t) = ec_plug_e C (ectx_split t).
destruct (ectx_split t) eqn:He; cbn;
  rewrite<- ectx_split_unique in He.
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
  


Inductive enf : Type :=
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
unfold eval_enf in *.
rewrite 2 rec_as_interp in *.
rewrite 2 eval_enf'_equation_1 in *.
rewrite 2 ectx_split_plug.

destruct (ectx_split t1) eqn:H, (ectx_split t2) eqn:H1; cbn.
+ cbn in p.
  rewrite 2 interp_ret in p; apply eqit_Ret in p; injection p as peq.
  rewrite peq in H.
  rewrite<- H in H1.
  apply ectx_split_inj in H1.
  rewrite H1, peq.
  reflexivity.
+ cbn in p.
  destruct v0.
  - rewrite 2 interp_ret in p.
    apply eqit_Ret in p.
    discriminate p.
  - shelve.
+ shelve.
+ cbn in p.
  destruct v, v1; cbn.
  - rewrite 2 interp_ret in p; apply eqit_Ret in p; injection p; intros.
    rewrite H0, H2, H3; reflexivity.
  - 
    * 
  - induction C; cbn.
    * rewrite ectx_split_val; exact p.
    * 
    
  destruct (ectx_split (ec_plug C (term_of_value v))) eqn:H2,
           (ectx_split (ec_plug C (term_of_value v0))) eqn:H3; cbn.
  - rewrite 2 interp_ret; apply eqit_Ret.
                               
  induction C; cbn.
  - rewrite 2 ectx_split_val; cbn.
    rewrite 2 interp_ret; apply eqit_Ret.    
    exact p.
  - 
+ rewrite<- ectx_split_unique in H; cbn in H.
  rewrite<- ectx_split_unique in H1; cbn in H1.
  cbn in p.
+ destruct (ec_plug_e_inv_val H).
  rewrite<- ectx_split_unique in H1; cbn in H1.
  rewrite H1 in p.
  rewrite (ectx_split_val v) in p.
  cbn in p.
  rewrite interp_ret in p.
  destruct (ectx_split t2) eqn:H2; cbn.
  - rewrite H0; cbn; rewrite (ectx_split_val v0); cbn.
    rewrite 2 interp_ret; apply eqit_Ret.
    cbn in p; rewrite interp_ret in p; apply eqit_Ret in p.
    exact p.
  - cbn in p.
    destruct v0; cbn in p.
    rewrite interp_ret in p.
    apply eqit_Ret in p.
    discriminate p.
    rewrite H0; cbn.
    rewrite interp_ret.
    exact p.
+ destruct (ec_plug_e C (ectx_split t2)) eqn:H1; cbn.
  - destruct (ec_plug_e_inv_val H1).
    destruct (ectx_split t1) eqn:?.
    * rewrite H0 in H; cbn in H. rewrite ectx_split_val in H.
      discriminate H.
    * cbn in H.
      injection H; intros.
      rewrite H2, H3, H4, H5 in *.
      cbn in *.
      destruct v; cbn in *.
      rewrite 2 interp_ret in p.
      apply eqit_Ret in p; discriminate p.
      Search recursive.
      rewrite interp_recursive_call in p.
      rewrite rec_as_interp in p.
      rewrite<- ectx_split_coherent in H2; cbn in H2.
      rewrite ectx_split_val in H2.
      rewrite H2 in H1
      rewrite H2 in p.
      cbn in p.
      rewrite 2 interp_ret in p.
      apply eqit_Ret in p.
      destruct v.
    rewrite 
    * 
    * cbn.
    
    Search "interp" "ret".
induction C; cbn.



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
  iter (fun t => translate elim_void1 (eval_enf t) >>= lassen_enf).

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
  iter (fun t => translate elim_void1 (eval_enf t) >>= lassen_enf_v).

(* unfold leaves by coinductively eta-expanding values *)
Definition expand_v : itree enfE_v value -> itree enfE T0 :=
  ITree.iter (fun t => v <- lassen_v_inj t ;;
                       Ret (inl (Ret v))).
  (*cofix expand_ t := ITree.bind (lassen_v_inj t)
                                (tau # expand_ # eval_lassen_v # val_app_fresh).*)

Equations _expand_v : itree' enfE_v value -> itree enfE T0 :=
  _expand_v (RetF r) := expand_v (eval_lassen_v (val_app_fresh r)) ;
  _expand_v (TauF t) := tau (expand_v t) ;
  _expand_v (VisF e k) := Vis (enfE_v_inj e) (fun r => expand_v (k r)).

Lemma unfold_expand_v (x : itree enfE_v value) : expand_v x ≅ _expand_v (observe x).
  unfold expand_v.
  rewrite unfold_iter; cbn.
  rewrite bind_bind; cbn.
  unfold lassen_v_inj.
  Search "bind".
  bind_translate.
  destruct (observe x); cbn.

Lemma eval_lassen_v_lem (x : term) : eval_lassen x ≈ expand_v (eval_lassen_v x).
  induction x; induction t; cbn.
  Admitted.

(* LassenV trees are bisimilar and coinductively, leaves (values) applied to 
   a fresh variable have bisimilar lassen' trees.
   We
*)
Definition eqv_lassen_v : term -> term -> Prop :=
  paco2 (fun R x y => eutt (fun v1 v2 => R (val_app_fresh v1) (val_app_fresh v2))
                           (eval_lassen_v x)
                           (eval_lassen_v y))
        bot2.

Lemma eqv_lassen_v_lem (x y : term) :
  eqv_lassen_v x y <-> expand_v (eval_lassen_v x) ≈ expand_v (eval_lassen_v y).
econstructor.
+ einit.
  ecofix H.
  intro e.
  unfold expand_v.
  econstructor.
  Search gpaco2.
  eapply gpaco2_step.
  - shelve.
  - unfold eqit_. cbn.
    econstructor.
Admitted.

Lemma eqv_lassen_v_correct (x y : term) : eqv_lassen x y <-> eqv_lassen_v x y.
constructor;
  unfold eqv_lassen;
  rewrite (eval_lassen_v_lem x), (eval_lassen_v_lem y);
  [ exact (proj2 (eqv_lassen_v_lem x y)) |
    exact (proj1 (eqv_lassen_v_lem x y)) ].
Qed.
End eager_lassen.

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
