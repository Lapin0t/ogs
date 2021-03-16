From ExtLib.Structures Require Import Monad.
Import MonadNotation.
Open Scope monad_scope.

(*Import Compare_dec Lt PeanoNat.Nat Plus.*)

From ITree Require Import ITree Events.Dependent.
From Paco Require Import paco.
From Equations Require Import Equations.
Require Setoid.

(*************************)
(* notations and prelude *)
Notation endo T := (T -> T).
Arguments depE : clear implicits.  (* index is usually hard to infer *)
Notation "f # g" := (Basics.compose f g) (at level 60) : function_scope. 

Definition T0 := Empty_set.
Definition T1 := unit.
Definition T2 := bool.

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


(**************************************************)
(* strictly bounded naturals, non-inductive style *)

(*Record fin (n : nat) : Type := Fin { fin_nat :> nat ; fin_prf : fin_nat < n }.
Arguments Fin {n}.
Arguments fin_nat {n}.
Arguments fin_prf {n}.

Definition fin_ze {m} : fin (S m) := Fin O (lt_0_succ _). 
Definition fin_su {m} (i : fin m) : fin (S m) := Fin (S i) (lt_n_S _ _ (fin_prf i)).

Definition fin_add {m} (n : nat) (i : fin m) : fin (n + m) :=
  Fin (n + i) (plus_lt_compat_l _ _ _ (fin_prf i)).*)


(**************************)
(* terms and substitution *)

(*Inductive termF (X : nat -> Type) (n : nat) : Type :=
| Var : fin n -> termF X n
| App : X n -> X n -> termF X n
| Lam : X (S n) -> termF X n
.*)

(*Inductive termF_sh (n : nat) : Type :=
| Var : fin n -> termF_sh n
| App : termF_sh n
| Lam : termF_sh n
.

Inductive termF_ar (n : nat) : Type :=

Record t_alg : Type := TAlg {
  carrier :> nat -> Type ;
  alg : forall n, termF carrier n -> carrier n
}.*)

Record eF (E : Type -> Type) (X : Type) := EF {
  eF_R : Type ;
  eF_q : E eF_R ;
  eF_k : eF_R -> X
}.

Arguments EF {E} {X} {eF_R}.
Arguments eF_R {E} {X}.
Arguments eF_q {E} {X}.
Arguments eF_k {E} {X}.

Definition e_alg (E E' : Type -> Type) (X : Type) := eF E (itree E' X) -> itree E' X.

Equations e_fold_aux {E E' : Type -> Type} {X : Type}
          (f : eF E (itree E' X) -> itree E' X)
          (h : itree E X -> itree E' X) : itree' E X -> itree E' X :=
  e_fold_aux f h (RetF x)   := Ret x ;
  e_fold_aux f h (TauF t)   := Tau (h t) ;
  e_fold_aux f h (VisF e k) := f (EF e (h # k))
.
Definition e_fold {E E' X} (f : eF E (itree E' X) -> itree E' X) : itree E X -> itree E' X
.
cofix e_fold_.
exact (e_fold_aux f e_fold_ # observe).
Admitted.

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
Definition termT := itree termE T0.

Notation VarE i := (Dep (VarC i)).
Notation AppE := (Dep AppC).
Notation LamE := (Dep LamC).

Definition VarT i : termT := Vis (VarE i) (fun x : T0 => match x with end).
Definition AppT u v : termT := Vis AppE (fun x : T2 => if x then u else v).
Definition LamT u : termT := Vis LamE (fun x : T1 => match x with tt => u end).

Equations t_evalE : term -> itree termE T0 :=
  t_evalE (Var i)   := VarT i ;
  t_evalE (App u v) := AppT (t_evalE u) (t_evalE v) ;
  t_evalE (Lam u)   := LamT (t_evalE u)
.


Equations t_shift (e : nat -> nat) : e_alg termE termE T0 :=
  t_shift e (EF (VarE i) k) := VarT (e i) ;
  t_shift e (EF AppE     k) := AppT (k true) (k false) ;
  t_shift e (EF LamE     k) := LamT
.
Obligation 1.

Equations t_shift (t : term) (e : nat -> nat) : term :=
  t_shift (Var i)   e := Var (e i) ;
  t_shift (App u v) e := App (t_shift u e) (t_shift v e) ;
  t_shift (Lam u)   e := Lam (t_shift u (fun i => match i with
                                                  | O => O
                                                  | S i => S (e i)
                                                  end))
.

Equations t_subst (t : term) (e : nat -> term) : term :=
  t_subst (Var i)   e := e i ;
  t_subst (App u v) e := App (t_subst u e) (t_subst v e) ;
  t_subst (Lam u)   e := Lam (t_subst u (fun i => match i with
                                                  | O => Var O
                                                  | S i => t_shift (e i) S
                                                  end))
.

Equations env1 (u : term) : nat -> term :=
  env1 u O     := u ;
  env1 u (S i) := Var i
.

Definition t_subst1 u v := t_subst u (env1 v).

Inductive nf (n : nat) : Type :=
| NLam : nf (S n) -> nf n
| NNeu : ne n -> nf n
with ne (n : nat) : Type :=
| NVar : fin n -> ne n
| NApp : ne n -> nf n -> ne n
.

Arguments NLam {n}.
Arguments NNeu {n}.
Arguments NVar {n}.
Arguments NApp {n}.

Fixpoint nf_to_term {n} (v : nf n) : term n :=
  match v with
  | NNeu ne => ne_to_term ne
  | NLam a => Lam (nf_to_term a)
  end
with ne_to_term {n} (v : ne n) : term n :=
  match v with
  | NVar i => Var i
  | NApp a b => App (ne_to_term a) (nf_to_term b)
  end
.

Search "translate".
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
    ret (NLam a)
.

(*************)
(* evaluator *)

(*Equations t_eval_aux : endo (forall t, itree (depE term' (wh_nf # fv) +' void1)
                                             (wh_nf (fv t))) :=
 t_eval_aux h (T' _ (Var i))   := ret (WNeu (WVar i)) ;
 t_eval_aux h (T' _ (App u v)) :=
   f <- dcall (T' _ u) ;;
   a <- dcall (T' _ v) ;;
   match f with
   | WNeu e => ret (WNeu (WApp e a))
   | WLam e => dcall (T' _ (t_subst1 e (whnf_to_term a)))
   end ;
 t_eval_aux h (T' _ (Lam u))   := ret (WLam u)
.*)
Definition t_eval {n} (t : term n) : itree void1 (nf n) :=
  drec_fix t_eval_aux (T' n t).

Definition Y : term 0 :=
  let u := Lam (App (Var fin_ze) (Var fin_ze)) in
  App u u.
Compute (burn 10 (t_eval Y)).
