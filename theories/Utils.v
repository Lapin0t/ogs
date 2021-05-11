Set Universe Polymorphism.

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

Equations dvec {X} (ty : X -> Type) (xs : list X) : Type :=
  dvec ty nil := T1 ;
  dvec ty (cons x xs) := ty x * dvec ty xs.
Transparent dvec.

Equations d_get {X ty} (c : list X) (d : dvec ty c) (i : fin (length c)) : ty (l_get c i) :=
  d_get (cons t ts) r F0     := fst r ;
  d_get (cons t ts) r (FS i) := d_get ts (snd r) i.

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

Declare Scope indexed_scope.
Open Scope indexed_scope.
Delimit Scope indexed_scope with indexed.

Definition iarrow {I} (X Y : I -> Type) : Type := forall {i}, X i -> Y i.
Infix "==>" := (iarrow) (at level 20) : indexed_scope.

Definition isum {I} (X Y : I -> Type) (i : I) : Type := X i + Y i.
Infix "+i" := (isum) (at level 20) : indexed_scope.


Inductive pin_at {I} (X : Type) (i : I) : I -> Type := Pin : X -> pin_at X i i.
Notation "X @ i" := (pin_at X i) (at level 20) : indexed_scope.
Arguments Pin {_ _ _}.
Derive NoConfusion for pin_at.

Equations pin_lift {I X Y} {i : I} : ((X @ i) ==> Y) -> (X -> Y i) :=
  pin_lift f x := f i (Pin x).


Inductive fiber {A B} (f : A -> B) : B -> Type := FOk a : fiber f (f a).

Definition psh@{a b} (I : Type@{a}) : Type@{max(a,b+1)} := I -> Type@{b}.


(*
Equations pin_elim {I X Y} {i : I} : (X -> Y i) -> (X @ i ==> Y) :=
  pin_elim f (Pin x) := f x.

Definition pin_iso_1 {I X Y} {i : I} (f : X -> Y i)
  : forall x, pin_lift (pin_elim f) x = f x
  := ltac:(auto).

Definition pin_iso_2 {I X Y} {i : I} (f : X @ i ==> Y)
  : forall x, pin_elim (pin_lift f) x = f i x
  := ltac:(destruct x; auto).

Equations pin_sum {I X Y} {i : I} : (X + Y) @ i ==> ((X @ i) +i (Y @ i)) :=
  pin_sum (Pin (inl x)) := inl (Pin x) ;
  pin_sum (Pin (inr y)) := inr (Pin y) .
*)
