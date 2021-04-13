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

(*************************)
(* notations and prelude *)
Notation endo T := (T -> T).
Arguments depE : clear implicits.  (* index is usually hard to infer *)
Notation "f # g" := (Basics.compose f g) (at level 60) : function_scope. 

Variant T0 := .
Variant T1 := t1_0.
Variant T2 := t2_0 | t2_1.
Variant T3 := t3_0 | t3_1 | t3_2.

Equations l_get {X} (xs : list X) : fin (length xs) -> X :=
  l_get (cons x xs) F0     := x ;
  l_get (cons x xs) (FS i) := l_get xs i.

Equations l_acc {X} (n : nat) (f : fin n -> X) : list X :=
  l_acc O     f := nil ;
  l_acc (S n) f := cons (f F0) (l_acc n (f # FS)).

Equations len_acc {X} n (f : fin n -> X) : length (l_acc n f) = n :=
  len_acc O     f := eq_refl ;
  len_acc (S n) f := f_equal S (len_acc n (f # FS)).

Definition ex_falso {A : Type} (bot : T0) : A := match bot with end.

Variant prod1 (D E : Type -> Type) : Type -> Type :=
  | pair1 : forall {X Y}, D X -> E Y -> prod1 D E (X * Y).

Notation "D *' E" := (prod1 D E) (at level 50).

(********************************************************)
(* Dependent version of stuff in ITree.Interp.Recursion *)
Section dep_rec.

Equations dcalling' {A B} {F : Type -> Type}
          (f : forall a, itree F (B a)) : depE A B ~> itree F :=
dcalling' f _ (Dep a) := f a.

Definition drec {E : Type -> Type} {A B}
           (body : forall a, itree (depE A B +' E) (B a)) :
  forall a, itree E (B a) :=
  fun a => mrec (dcalling' body) (Dep a).

Definition dcall {E A B} (a : A) : itree (depE A B +' E) (B a) :=
  ITree.trigger (inl1 (Dep a)).

(*Definition drec_fix {E : Type -> Type} {A B}
           (body : endo (forall a, itree E (B a)))
  : forall a, itree E (B a)
  := drec (body dcall).*)
End dep_rec.



(**************************)
(* terms and substitution *)

Record eF (E : Type -> Type) (X : Type) := EF {
  eF_R : Type ;
  eF_q : E eF_R ;
  eF_k : eF_R -> X
}.

Notation "[ E ]e" := (eF E).
Arguments EF {E} {X} {eF_R}.
Arguments eF_R {E} {X}.
Arguments eF_q {E} {X}.
Arguments eF_k {E} {X}.

Definition wrap {E X} (t : [ E ]e (itree E X)) : itree E X :=
  vis (eF_q t) (eF_k t).

Instance Functor_E {E} : Functor ([ E ]e) := {|
  fmap _ _ f := fun x => EF (eF_q x) (f # eF_k x)
|}. 

Instance Functor_E_itree {E} : Functor ([ E ]e # itree E) := {|
  fmap _ _ f := fun x => EF (eF_q x) (fmap f # eF_k x)
|}.

(*****************)

(*
Section euttG_bind.
Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).
Context (rL rH gL gH : itree E R1 -> itree E R2 -> Prop).
Variant euttG_bind_clo : itree E R1 -> itree E R2 -> Prop :=
| i_gbind_clo t1 t2 k1 k2 :
      euttG RR rL rH gL gH t1 t2 ->
      (forall u1 u2, RR u1 u2 -> euttG RR rL rH gL gH (k1 u1) (k2 u2))
  ->  euttG_bind_clo (ITree.bind t1 k1) (ITree.bind t2 k2)
.
Hint Constructors euttG_bind_clo: core.
Print eqit_.
Lemma euttG_clo_bind vclo
      (MON: monotone2 vclo)
      (CMP: compose (eqitC RR b1 b2) vclo <3= compose vclo (eqitC RR b1 b2))
      (ID: id <3= vclo) :
    euttG_bind_clo b1 b2 <3= gupaco2 (eqit_ RR b1 b2 vclo) (eqitC RR b1 b2).
*)

(*****************)

(*
   \o/ it works
   variation of ITree.Interp.Interp.interp that folds over events instead
   of mapping them
*)

Definition translate_rec {D E : Type -> Type}
           (ctx : D ~> itree (D +' E)) : itree D ~> itree E :=
  fun _ => @interp_mrec _ _ ctx _ # @translate _ _ inl1 _.

Definition foldE {E M X} {FM : Functor M} {MM : Monad M} {IM : MonadIter M}
           (h : [ E ]e (M X) -> M (itree E X + X)%type) : itree E X -> M X
  := iter (fun x => match observe x with
                 | RetF r => ret (inr r)
                 | TauF t => ret (inl t)
                 | VisF e k => h (EF e (iter (ret # inl) # k))
                 end).

(* foldE with additional data *)
Definition foldE_ad {E M A X} {FM : Functor M} {MM : Monad M} {IM : MonadIter M}
           (h : [ E ]e (stateT A M X) -> stateT A M _) (x : itree E X) : A -> M X
  := fmap snd # foldE h x.


Definition caseE {E M X Y} {FM : Functor M} {MM : Monad M} {IM : MonadIter M}
           (f : X -> Y) (x : itree E X) (h : [ E ]e (itree E X) -> M Y) : M Y
  := iter (fun x => match observe x with
                    | RetF r => ret (inr (f r))
                    | TauF t => ret (inl t)
                    | VisF e k => fmap inr (h (EF e k))
                    end) x.

Definition trans_void {E T} : itree void1 T -> itree E T :=
  @translate _ E elim_void1 T.
          
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

Equations ec_plug_e (C : eager_ctx) (x : eager_term) : eager_term :=
  ec_plug_e ECHole        x := x ;
  ec_plug_e (ECApp_l t C) x with ec_plug_e C x := {
    | EValue v with ectx_split t := {
      | EValue v0       := ERedex ECHole v0 v ;
      | ERedex C' v0 v1 := ERedex (ECApp_r C' v) v0 v1 };
    | ERedex C' v0 v1 := ERedex (ECApp_l t C') v0 v1 };
  ec_plug_e (ECApp_r C v) x with ec_plug_e C x := {
    | EValue v0 := ERedex ECHole v0 v ;
    | ERedex C' v0 v1 := ERedex (ECApp_r C' v) v0 v1 } .
#[local] Transparent ec_plug_e.


Lemma ectx_split_plug (C : eager_ctx) (t : term) : ectx_split (ec_plug C t) = ec_plug_e C (ectx_split t).
  induction C; cbn; auto; rewrite<- IHC.
  + destruct (ectx_split (ec_plug C t)); cbn; auto.
    destruct (ectx_split t0); auto.
  + destruct v; cbn; destruct (ectx_split (ec_plug C t)); auto.
Qed.
    

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

(* <<WIP *)
#[local] Transparent plug.
Lemma eval_enf_congr (C : eager_ctx) {t1 t2} (p : eval_enf t1 ≈ eval_enf t2)
  : eval_enf (ec_plug C t1) ≈ eval_enf (ec_plug C t2).
  (*unfold eval_enf; rewrite 2 rec_as_interp.
  Search "eval_enf'".
  rewrite 2 eval_enf'_equation_1.
  rewrite 2 ectx_split_plug.
  Search "clause_1_equation".*)
  induction C; auto;
    unfold eval_enf; rewrite 2 rec_as_interp;
    rewrite 2 eval_enf'_equation_1; rewrite 2 ectx_split_plug.
  induction C; cbn.
  + exact p.
  + unfold eval_enf; rewrite 2 rec_as_interp.
    funind eval_enf'.
    Search "eval_enf'".
(* WIP>> *)
  

Inductive enfE : Type -> Type :=
| ENVarE : nat -> enfE T0
| ENLamE : enfE T1
| ENRedexE : nat -> enfE T2
.

Definition ENVarT {X} (i : nat) : itree enfE X := Vis (ENVarE i) ex_falso.
Definition ENLamT {X} (t : itree enfE X) : itree enfE X :=
  Vis ENLamE (fun x : T1 => match x with t1_0 => t end).
Definition ENRedexT {X} (i : nat) (t0 t1 : itree enfE X) : itree enfE X :=
  Vis (ENRedexE i) (fun x : T2 => match x with t2_0 => t0 | t2_1 => t1 end).

Equations lassen_val (v : value) : itree enfE (term + T0) :=
  lassen_val (VVar i) := ENVarT i ;
  lassen_val (VLam u) := ENLamT (ret (inl u)).

Equations lassen_enf (t : enf) : itree enfE (term + T0) :=
  lassen_enf (ENValue v)     := lassen_val v ;
  lassen_enf (ENRedex C i v) := ENRedexT i (ret (inl (ec_fresh C))) (lassen_val v).

Definition eval_lassen : term -> itree enfE T0 :=
  iter (fun t => translate elim_void1 (eval_enf t) >>= lassen_enf).

End eager_lassen.


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
