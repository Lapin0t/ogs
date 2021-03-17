From ExtLib.Structures Require Import Functor Monad.
From ExtLib.Data Require Import Nat Fin.
From ITree Require Import ITree Events.Dependent Basics.Basics.
Import Monads.
Import MonadNotation.
Open Scope monad_scope.

From Paco Require Import paco.
From Equations Require Import Equations.


(*************************)
(* notations and prelude *)
Notation endo T := (T -> T).
Arguments depE : clear implicits.  (* index is usually hard to infer *)
Notation "f # g" := (Basics.compose f g) (at level 60) : function_scope. 

Variant T0 := .
Variant T1 := t1_0.
Variant T2 := t2_0 | t2_1.
Variant T3 := t3_0 | t3_1 | t3_2.

Definition boom {A : Type} (bot : T0) : A := match bot with end.


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

Definition drec_fix {E : Type -> Type} {A B}
           (body : endo (forall a, itree (depE A B +' E) (B a)))
  : forall a, itree E (B a)
  := drec (body dcall).
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


(*
   \o/ it works
   variation of ITree.Interp.Interp.interp that folds over events instead
   of mapping them
*)
Definition interp {E M : Type -> Type}
           {FM : Functor M} {MM : Monad M} {IM : MonadIter M}
           {X : Type} (h : [ E ]e (M X) -> M X) : itree E X -> M X :=
  iter (fun x => match observe x with
                 | RetF r => ret (inr r)
                 | TauF t => ret (inl t)
                 | VisF e k => fmap inr (h (EF e (iter (ret # inl) # k)))
                 end).

Definition interp_ad {E M : Type -> Type} {A X : Type}
           {FM : Functor M} {MM : Monad M} {IM : MonadIter M}
           (h : [ E ]e (stateT A M X) -> stateT A M X) (x : itree E X) : A -> M X
  := fmap snd # interp h x.

(* usual term definition *)
Inductive term : Type :=
| Var : nat -> term
| App : term -> term -> term
| Lam : term -> term
.

(* itree term definitions *)
Variant termC : Type :=
| VarC : nat -> termC
| AppC : termC
| LamC : termC
.

Equations termA : termC -> Type :=
  termA (VarC _) := T0 ;
  termA AppC     := T2 ;
  termA LamC     := T1
.

Definition termE := depE termC termA.
Definition termT {X : Type} := itree termE X.
Definition termT0 := itree termE T0.

Notation VarE i := (Dep (VarC i)).
Notation AppE := (Dep AppC).
Notation LamE := (Dep LamC).

Definition VarT {X} i : @termT X :=
  Vis (VarE i) (fun x : T0 => match x with end).
Definition AppT {X} u v : @termT X :=
  Vis AppE (fun x : T2 => match x with t2_0 => u | t2_1 => v end).
Definition LamT {X} u : @termT X :=
  Vis LamE (fun x : T1 => match x with t1_0 => u end).

Equations t_evalE : term -> itree termE T0 :=
  t_evalE (Var i)   := VarT i ;
  t_evalE (App u v) := AppT (t_evalE u) (t_evalE v) ;
  t_evalE (Lam u)   := LamT (t_evalE u)
.


Equations t_shift_aux : [ termE ]e (stateT (nat -> nat) (itree termE) T0)
                      -> stateT (nat -> nat) (itree termE) T0 :=
  t_shift_aux (EF (VarE i) k) e := VarT (e i) ;
  t_shift_aux (EF AppE     k) e := AppT (k t2_0 e) (k t2_1 e) ;
  t_shift_aux (EF LamE     k) e := LamT (k t1_0 (fun i => match i with
                                                        | O => O
                                                        | S i => S (e i)
                                                        end)).
Definition t_shift : termT0 -> (nat -> nat) -> termT0 := interp_ad t_shift_aux.


Equations t_subst_aux : [ termE ]e (stateT (nat -> termT0) (itree termE) T0)
                      -> stateT (nat -> termT0) (itree termE) T0 :=
  t_subst_aux (EF (VarE i) k) e := fmap (fun x => pair e x) (e i) ;
  t_subst_aux (EF AppE k)     e := AppT (k t2_0 e) (k t2_1 e) ;
  t_subst_aux (EF LamE k)     e := LamT (k t1_0 (fun i => match i with
                                                  | O => VarT O
                                                  | S i => t_shift (e i) S
                                                  end)).
Definition t_subst : termT0 -> (nat -> termT0) -> termT0 := interp_ad t_subst_aux.

Equations env1 (u : termT0) : nat -> termT0 :=
  env1 u O     := u ;
  env1 u (S i) := VarT i.

Definition t_subst1 u v := t_subst u (env1 v).


(******************************)
(* normal forms and evaluation*)
Variant normC : Type := NLamC | NRedC : nat -> nat -> normC.
Equations normA : normC -> Type :=
  normA NLamC := T1 ;
  normA (NRedC _ i) := fin i.

Definition normE := depE normC normA.
Definition normT {X : Type} := itree normE X.
Definition normT0 := itree normE T0.

Notation NLamE := (Dep NLamC).
Notation NRedE i j := (Dep (NRedC i j)).

Definition NLamT {X} u : @normT X :=
  Vis NLamE (fun x : T1 => match x with t1_0 => u end).
Definition NRedT {X} (i j : nat) (f : fin j -> @normT X) : @normT X :=
  Vis (NRedE i j) f.

Equations norm2term_aux : [ normE ]e (itree termE T0) -> itree termE T0 :=
  norm2term_aux (EF NLamE k)       := LamT (k t1_0);
  norm2term_aux (EF (NRedE i j) k) := spine j (VarT i) k
  where spine (n : nat) : termT0 -> (fin n -> termT0) -> termT0 := {
    spine O     x f := x ;
    spine (S i) x f := spine i (AppT x (f (F0))) (f # FS) }.
Definition norm2term : normT0 -> termT0 := interp norm2term_aux.


Equations eval_aux : [ termE ]e (itree normE T0) -> itree normE T0 :=
  eval_aux (EF (VarE i) k) := NRedT i 0 (fun i => match i with end);
  eval_aux (EF LamE     k) := NLamT (k t1_0);
  eval_aux (EF AppE     k) := _.

(* WIP HERE*)


Equations t_eval_aux : endo (forall t, itree (depE term' (nf # fv) +' void1)
                                             (nf (fv t))) :=
  t_eval_aux h (T' _ (Var i))   := ret (NNeu (NVar i)) ;
  t_eval_aux h (T' _ (App u v)) :=
    f <- dcall (T' _ u) ;;
    a <- dcall (T' _ v) ;;
    match f with
    | NNeu e => ret (NNeu (NApp e a))
    | NLam e => dcall (T' _ (t_subst1 (nf_to_term e) (nf_to_term a)))
    end ;
  t_eval_aux h (T' _ (Lam u))   :=
    a <- dcall (T' _ u) ;;
    ret (NLam a).

Definition t_eval {n} (t : term n) : itree void1 (nf n) :=
  drec_fix t_eval_aux (T' n t).
