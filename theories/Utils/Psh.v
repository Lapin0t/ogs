(*|
Type families
===============

This file is dully-named ``Psh.v`` but in fact is actually about
type families, that is maps ``I → Type`` for some ``I : Type``.

.. coq:: none
|*)
From OGS Require Import Prelude.
(*||*)
Notation psh I := (I -> Type).
(*| .. coq:: none |*)
Declare Scope indexed_scope.
Open Scope indexed_scope.
Delimit Scope indexed_scope with indexed.
(*|
Pointwise arrows of families.
|*)
Definition arrᵢ {I} (X Y : psh I) : Type := forall i, X i -> Y i.
#[global] Infix "⇒ᵢ" := (arrᵢ) (at level 20) : indexed_scope.
(*|
A bunch of combinators.
|*)
Definition voidᵢ {I : Type} : I -> Type := fun _ => T0.
#[global] Notation "∅ᵢ" := (voidᵢ) : indexed_scope.

Definition sumᵢ {I} (X Y : psh I) : psh I := fun i => (X i + Y i)%type.
#[global] Infix "+ᵢ" := (sumᵢ) (at level 20) : indexed_scope.

Definition prodᵢ {I} (X Y : psh I) : psh I := fun i => (X i * Y i)%type.
#[global] Infix "×ᵢ" := (prodᵢ) (at level 20) : indexed_scope.
(*|
Fibers of a function are a particularly import kind of type family.
|*)
Inductive fiber {A B} (f : A -> B) : psh B := Fib a : fiber f (f a).
Arguments Fib {A B f}.
Derive NoConfusion for fiber.

Equations fib_extr {A B} {f : A -> B} {b : B} : fiber f b -> A :=
  fib_extr (Fib a) := a .
Equations fib_coh {A B} {f : A -> B} {b : B} : forall p : fiber f b, f (fib_extr p) = b :=
  fib_coh (Fib _) := eq_refl .
Definition fib_constr {A B} {f : A -> B} a : forall b (p : f a = b), fiber f b :=
  eq_rect (f a) (fiber f) (Fib a).

(*|
These next two functions form an isomorphism ``(fiber f ⇒ᵢ X) ≅ (∀ a → X (f a))``
|*)
Equations fib_into {A B} {f : A -> B} X (h : forall a, X (f a)) : fiber f ⇒ᵢ X :=
  fib_into _ h _ (Fib a) := h a .
Definition fib_from {A B} {f : A -> B} X (h : fiber f ⇒ᵢ X) a : X (f a) :=
  h _ (Fib a).
(*|
Using the fiber construction, we can define a "sparse" type family which will
be equal to some set at one point of the index and empty otherwise. This will
enable us to have an isomorphism ``(X @ i ⇒ᵢ Y) ≅ (X → Y i)``.

See the functional pearl by Conor McBride "Kleisli arrows of outrageous fortune"
for background on this construction and its use.
|*)
#[global] Notation "X @ i" := (fiber (fun (_ : X) => i)) (at level 20) : indexed_scope.

Definition pin {I X} (i : I) : X -> (X @ i) i := Fib.
Definition pin_from {I X Y} {i : I} : ((X @ i) ⇒ᵢ Y) -> (X -> Y i) := fib_from _.
Definition pin_into {I X Y} {i : I} : (X -> Y i) -> (X @ i ⇒ᵢ Y) := fib_into _.

Equations pin_map {I X Y} (f : X -> Y) {i : I} : (X @ i) ⇒ᵢ (Y @ i) :=
  pin_map f _ (Fib x) := Fib (f x) .
