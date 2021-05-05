From ExtLib.Data Require Import Nat Fin.
From ITree Require Import ITree Events.Dependent.

From Equations Require Import Equations.

(******************)
(* misc notations *)

#[global] Notation endo T := (T -> T).
#[global] Notation "f # g" := (Basics.compose f g) (at level 60) : function_scope. 

Variant prod1 (D E : Type -> Type) : Type -> Type :=
| pair1 : forall {X Y}, D X -> E Y -> prod1 D E (X * Y).

#[global] Notation "D *' E" := (prod1 D E) (at level 50).

Definition tau {E R} (t : itree E R) : itree E R := Tau t.


(***************)
(* Finite sets *)

Variant T0 := .
Variant T1 := t1_0.
Variant T2 := t2_0 | t2_1.
Variant T3 := t3_0 | t3_1 | t3_2.

Definition ex_falso {A : Type} (bot : T0) : A := match bot with end.


(********************************)
(* Couple lemma on list/vec/fin *)

Equations l_get {X} (xs : list X) : fin (length xs) -> X :=
  l_get (cons x xs) F0     := x ;
  l_get (cons x xs) (FS i) := l_get xs i.

Equations l_acc {X} (n : nat) (f : fin n -> X) : list X :=
  l_acc O     f := nil ;
  l_acc (S n) f := cons (f F0) (l_acc n (f # FS)).

Equations len_acc {X} n (f : fin n -> X) : length (l_acc n f) = n :=
  len_acc O     f := eq_refl ;
  len_acc (S n) f := f_equal S (len_acc n (f # FS)).


(********************************************************)
(* Dependent version of stuff in ITree.Interp.Recursion *)

Arguments depE : clear implicits.  (* index is usually hard to infer *)

Equations dcalling' {A B} {F : Type -> Type}
          (f : forall a, itree F (B a)) : depE A B ~> itree F :=
dcalling' f _ (Dep a) := f a.

Definition drec {E : Type -> Type} {A B}
           (body : forall a, itree (depE A B +' E) (B a)) :
  forall a, itree E (B a) :=
  fun a => mrec (dcalling' body) (Dep a).

Definition dcall {E A B} (a : A) : itree (depE A B +' E) (B a) :=
  ITree.trigger (inl1 (Dep a)).
