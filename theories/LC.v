From ITree Require Import ITree Events.Dependent.
From Equations Require Import Equations.
Require Setoid.

From ExtLib.Structures Require Import Monad.
Import MonadNotation.
Open Scope monad_scope.

Import Compare_dec Lt PeanoNat.Nat Plus.

Notation endo T := (T -> T).
Arguments depE : clear implicits.  (* index is usually hard to infer *)
Notation "f # g" := (Basics.compose f g) (at level 60) : function_scope. 

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

Record fin (n : nat) : Type := Fin { fin_nat :> nat ; fin_prf : fin_nat < n }.
Arguments Fin {n}.
Arguments fin_nat {n}.
Arguments fin_prf {n}.

Definition fin_ze {m} : fin (S m) := Fin O (lt_0_succ _). 
Definition fin_su {m} (i : fin m) : fin (S m) := Fin (S i) (lt_n_S _ _ (fin_prf i)).

Definition fin_add {m} (n : nat) (i : fin m) : fin (n + m) :=
  Fin (n + i) (plus_lt_compat_l _ _ _ (fin_prf i)).


(**************************)
(* terms and substitution *)

Inductive term {n : nat} : Type :=
(* Let's work with DeBruijn for now. Might want to consider
   using autosubst2 once things get serious *)
| Var : fin n -> @term n
| App : @term n -> @term n -> @term n
| Lam : @term (S n) -> @term n
.
Arguments term : clear implicits.

Record term' : Type := T' { fv : nat; tm : term fv }.


Equations t_shift {m n} (t : term m) (e : fin m -> fin n) : term n :=
  t_shift (Var i)   e := Var (e i) ;
  t_shift (App a b) e := App (t_shift a e) (t_shift b e) ;
  t_shift (Lam a)   e := Lam (t_shift a (fun i => _))
.
Obligation 1.
destruct i as [ [] prf ].
exact fin_ze.
exact (fin_su (e (Fin _ (lt_S_n _ _ prf)))).
Defined.

Equations t_subst_aux {m n} p (t : term (p + m)) (e : fin m -> term n) : term (p + n) :=
  t_subst_aux p (Var (Fin i_n i_p)) e with lt_dec i_n p => {
    | left h => Var (Fin i_n (lt_lt_add_r _ _ _ h)) ;
    | right h => t_shift (e (Fin (i_n - p) _)) (fin_add p)
    } ;
  t_subst_aux p (App a b) e := App (t_subst_aux p a e) (t_subst_aux p b e) ;
  t_subst_aux p (Lam a)   e := Lam (t_subst_aux (S p) a e)
.
Obligation 1.
apply (add_lt_mono_l _ _ p).
apply le_ngt in h.
rewrite<- (Minus.le_plus_minus _ _ h).
exact i_p.
Defined.

Definition t_subst {m n} := @t_subst_aux m n O.

Equations env1 {n} (u : term n) (i : fin (S n)) : term n :=
  env1 u (Fin O _)     := u ;
  env1 u (Fin (S i) p) := Var (Fin i (lt_S_n _ _ p)).

Definition t_subst1 {n} u v := t_subst u (@env1 n v).

(* alternative inefficient but more logical solution
Equations t_subst {m n} (t : term m) (e : fin m -> term n) : term n :=
  t_subst (Var i)   e := e i ;
  t_subst (App a b) e := App (t_subst a e) (t_subst b e) ;
  t_subst (Lam a)   e := Lam (t_subst a (fun i => _))
.
Obligation 1.
destruct i as [ [] prf ].
exact (Var (fin_ze)).
(*exact (t_shift (e (Fin n0 (lt_S_n _ _ prf))) (fun i => fin_add 1 i)).*)
refine (t_shift (e (Fin n0 (lt_S_n _ _ prf))) (fun i => fin_add 1 i)).
Defined.
*)

Inductive wh_ne {n : nat} : Type :=
| NVar : fin n -> @wh_ne n
| NApp : @wh_ne n -> @wh_nf n -> @wh_ne n
with wh_nf {n : nat} : Type :=
| NNeu : @wh_ne n -> @wh_nf n
| NLam : term (1 + n) -> @wh_nf n
.
Arguments wh_ne : clear implicits.
Arguments wh_nf : clear implicits.

Fixpoint whnf_to_term {n} (v : wh_nf n) : term n :=
  match v with
  | NNeu ne => whne_to_term ne
  | NLam a => Lam a
  end
with whne_to_term {n} (v : wh_ne n) : term n :=
  match v with
  | NVar i => Var i
  | NApp a b => App (whne_to_term a) (whnf_to_term b)
  end
.


(*************)
(* evaluator *)

Equations t_eval_aux : endo (forall t, itree (depE term' (wh_nf # fv) +' void1)
                                             (wh_nf (fv t))) :=
 t_eval_aux h (T' _ (Var i))   := ret (NNeu (NVar i)) ;
 t_eval_aux h (T' n (App u v)) :=
   f <- dcall (T' n u) ;;
   a <- dcall (T' n v) ;;
   match f with
   | NNeu e => ret (NNeu (NApp e a))
   | NLam e => dcall (T' _ (t_subst1 e (whnf_to_term a)))
   end ;
 t_eval_aux h (T' _ (Lam u))   := ret (NLam u)
.

Definition t_eval {n} (t : term n) : itree void1 (wh_nf n) :=
  drec_fix t_eval_aux (T' n t).
