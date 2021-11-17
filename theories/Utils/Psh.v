From Coq Require Import Arith Lia Program.
From Equations Require Import Equations.
From Coq.Classes Require Import RelationClasses.
From OGS Require Import Utils.Prelude.

(* (covariant) presheaves *)
Definition psh (I : Type) : Type := I -> Type.

Declare Scope indexed_scope.
Open Scope indexed_scope.
Delimit Scope indexed_scope with indexed.
Bind Scope indexed_scope with psh.

(* pointwise arrows *)
Definition arrᵢ {I} (X Y : psh I) : Type := forall {i}, X i -> Y i.
#[global] Infix "⇒ᵢ" := (arrᵢ) (at level 20) : indexed_scope.

Definition voidᵢ {I : Type} : I -> Type := fun _ => T0.
Notation "∅ᵢ" := (voidᵢ) : indexed_scope.

(* pointwise coproduct *)
Definition sumᵢ {I} (X Y : psh I) : psh I := fun i => (X i + Y i)%type.
Infix "+ᵢ" := (sumᵢ) (at level 20) : indexed_scope.

(** pointwise arrows between F G : endo (psh I)
    "ₙ" is for natural transformation *)
Notation "F ⇒ₙ G" := (forall X : psh _, F X ⇒ᵢ G X) (at level 30).


(** indexed relations *)

Definition relᵢ {I : Type} (A B : psh I) := forall i, A i -> B i -> Prop.

Notation Reflexiveᵢ R := (forall i, Reflexive (R i)).
Notation Symmetricᵢ R := (forall i, Symmetric (R i)).
Notation Transitiveᵢ R := (forall i, Transitive (R i)).

Definition subrelᵢ {I : Type} {A B : psh I} (R1 R2 : relᵢ A B) : Prop :=
  forall i a b, R1 i a b -> R2 i a b.

Definition flipᵢ {I : Type} {A B : psh I} (R : relᵢ A B) : relᵢ B A :=
  fun i x y => R i y x.

Definition eqᵢ {I : Type} {X : psh I} : relᵢ X X := fun i x y => x = y.
Arguments eqᵢ _ _ _ /.

Inductive fiber {A B} (f : A -> B) : psh B := | Fib a : fiber f (f a).
Arguments Fib {A B f}.
Derive NoConfusion for fiber.

Definition fib_extr {A B} {f : A -> B} {b : B} : fiber f b -> A :=
  fun '(Fib a) => a.
Definition fib_coh {A B} {f : A -> B} {b : B} :
    forall p : fiber f b, f (fib_extr p) = b :=
  fun '(Fib _) => eq_refl.
Definition fib_constr {A B} {f : A -> B} a : forall b (p : f a = b), fiber f b :=
  eq_rect (f a) (fiber f) (Fib a).
 
(* These two functions actually form an isomorphism (extensionally)
      (fiber f ⇒ᵢ X) ≅ (∀ a → X (f a))
 *)
Definition fib_into {A B} {f : A -> B} X (h : forall a, X (f a)) : fiber f ⇒ᵢ X :=
  fun _ '(Fib a) => h a.
Definition fib_from {A B} {f : A -> B} X (h : fiber f ⇒ᵢ X) a : X (f a) :=
  h _ (Fib a).

Notation "X @ i" := (fiber (fun (_ : X) => i)) (at level 20) : indexed_scope.
Definition pin {I X} (i : I) : X -> (X @ i) i := Fib.
Definition pin_from {I X Y} {i : I} : ((X @ i) ⇒ᵢ Y) -> (X -> Y i) := fib_from _.
Definition pin_into {I X Y} {i : I} : (X -> Y i) -> (X @ i ⇒ᵢ Y) := fib_into _.
