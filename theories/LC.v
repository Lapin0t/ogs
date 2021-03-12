From ITree Require Import ITree Events.Dependent.
From Equations Require Import Equations.
Require Setoid.

Import Compare_dec Lt PeanoNat.Nat Plus.

(** Dependent version of stuff in ITree.Interp.Recursion *)
Section dep_rec. 
Arguments depE : clear implicits.  (* index is usually hard to infer *)
Local Notation endo T := (T -> T).

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

Record fin (n : nat) : Type := Fin { fin_nat :> nat ; fin_prf : fin_nat < n }.
Arguments Fin {n}.
Arguments fin_nat {n}.
Arguments fin_prf {n}.

Definition fin_ze {m} : fin (S m) := Fin O (lt_0_succ _). 
Definition fin_su {m} (i : fin m) : fin (S m) := Fin (S i) (lt_n_S _ _ (fin_prf i)).

Definition fin_add {m} (n : nat) (i : fin m) : fin (n + m) :=
  Fin (n + i) (plus_lt_compat_l _ _ _ (fin_prf i)).

Inductive term {n : nat} : Type :=
(* Let's work with DeBruijn for now. Might want to consider
   using autosubst2 once things get serious *)
| Var : fin n -> @term n
| App : @term n -> @term n -> @term n
| Lam : @term (S n) -> @term n
.
Arguments term : clear implicits.

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
  t_subst_aux p (Var i)   e := _ ;
  t_subst_aux p (App a b) e := App (t_subst_aux p a e) (t_subst_aux p b e) ;
  t_subst_aux p (Lam a)   e := Lam (t_subst_aux (S p) a e)
.
Obligation 1.
destruct i as [i_n i_p].
destruct (lt_dec i_n p) as [h|h].
exact (Var (Fin i_n (lt_lt_add_r _ _ _ h))).
refine (t_shift (e (Fin (i_n - p) _)) (fin_add p)).
apply (add_lt_mono_l _ _ p).
apply le_ngt in h.
rewrite<- (Minus.le_plus_minus _ _ h).
exact i_p.
Defined.

Definition t_subst {m n} := @t_subst_aux m n O.
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

Record ev_arg : Type := EArg {
  ev_m : nat ;
  ev_n : nat ;
  ev_tm : term ev_m ;
  ev_ctx : fin ev_m -> wh_nf ev_n
}.
Arguments EArg {ev_m} {ev_n}.
Definition ev_out (a : ev_arg) : Type := wh_nf (ev_n a).

Print callE.
Definition t_eval (arg : ev_arg) : itree void1 (ev_out arg).
  refine (@drec_fix _ ev_arg ev_out (fun h => _) arg).
  intro a; destruct a as [m n t e].
  destruct t as [ i | a b | a ].
  + exact (Ret (e i)).
  + refine (ITree.bind (h (EArg a e)) (fun f => _)).
    refine (ITree.bind (h (EArg b e)) (fun v => _)).
    destruct f as [ neu | lam ].
    - exact (Ret (NNeu (NApp neu v))).
    - refine (h (EArg lam (fun i => _))).
      destruct i as [i_n i_p]; destruct i_n.
      * exact v.
      * refine (NNeu (NVar (Fin i_n _))).
        apply (add_lt_mono_l _ _ 1).
        rewrite add_1_l.
        exact i_p.
  + refine (ITree.bind (h (EArg a _)) (fun a => Ret (NLam (whnf_to_term a)))).
    intro i; destruct i as [i_n i_p]; destruct i_n.
    - exact (NNeu (NVar (Fin 0 (lt_0_succ _)))).
    - refine (t_shift )
  + refine (NLam (h (T_Ctx a _)).
    intro i; destruct i as [i_n i_p]; destruct i_n.
      Search (0 < _).
    - refine (NNeu (NVar (Fin 0 _))).
      exact (match (i with | O => v | (S i) => e i end).
      destruct i.
      *
    Check (ITree.bind _ _).
  Print itreeF.
  exact (Ret )
Search itree.
