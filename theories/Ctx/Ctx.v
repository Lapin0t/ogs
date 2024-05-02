From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.
From OGS.Ctx Require Import All.

#[local] Open Scope ctx_scope.
(*|
Contexts
---------

Contexts are simply lists, with the purely aesthetic choice of representing cons as
coming from the right. Note on paper: we write here "Γ ▶ x" instead of "Γ , x".
|*)
Inductive ctx (X : Type) : Type :=
| cnil : ctx X
| ccon : ctx X -> X -> ctx X.
(*|
.. coq:: none
|*)
#[global] Arguments cnil {X}.
#[global] Arguments ccon {X} Γ x.
Derive NoConfusion for ctx.
#[global] Notation "Γ ▶ x" := (ccon Γ%ctx x) (at level 40, left associativity) : ctx_scope.
(*|
We wish to manipulate intrinsically typed terms. We hence need a tightly typed notion of
position in the context: rather than a loose index, [var x Γ] is a proof of membership of
[x] to [Γ].
|*)
Inductive var {X} (x : X) : ctx X -> Type :=
| top {Γ} : var x (Γ ▶ x)
| pop {Γ y} : var x Γ -> var x (Γ ▶ y).
(*|
.. coq:: none
|*)
Derive Signature NoConfusion NoConfusionHom for var.
#[global] Arguments top {X x Γ}.
#[global] Arguments pop {X x Γ y}.
(*|
A couple basic functions: length, concatenation and pointwise function application.
|*)
Equations c_length {X} (Γ : ctx X) : nat :=
  c_length cnil       := Datatypes.O ;
  c_length (Γ ▶ _) := Datatypes.S (c_length Γ) .

Equations ccat {X} : ctx X -> ctx X -> ctx X :=
  ccat Γ cnil       := Γ ;
  ccat Γ (ccon Δ x) := ccon (ccat Γ Δ) x .

Equations c_map {X Y} : (X -> Y) -> ctx X -> ctx Y :=
  c_map f cnil        := cnil ;
  c_map f (Γ ▶ x) := c_map f Γ ▶ f x .
(*|
Implementation of the abstract context interface.
|*)
#[global] Instance free_context {X} : context X (ctx X) :=
  {| c_emp := cnil ; c_cat := ccat ; c_var Γ x := var x Γ |}.
(*|
Basic theory.
|*)
Lemma c_cat_empty_l {X : Type} {Γ : ctx X} : (∅ +▶ Γ)%ctx = Γ.
Proof. induction Γ; eauto; cbn; f_equal; apply IHΓ. Qed.

Lemma c_cat_empty_r {X : Type} {Γ : ctx X} : (Γ +▶ ∅)%ctx = Γ.
Proof. reflexivity. Qed.

Lemma c_map_cat {X Y} (f : X -> Y) (Γ Δ : ctx X)
  : c_map f (Γ +▶ Δ) = (c_map f Γ +▶ c_map f Δ)%ctx.
Proof. induction Δ; eauto; cbn; f_equal; apply IHΔ. Qed.
(*|
A view-based inversion package for variables in mapped contexts.
|*)
Equations map_has {X Y} {f : X -> Y} (Γ : ctx X) {x} (i : Γ ∋ x) : c_map f Γ ∋ f x :=
  map_has (Γ ▶ _) top     := top ;
  map_has (Γ ▶ _) (pop i) := pop (map_has Γ i) .
#[global] Arguments map_has {X Y f Γ x}.

Variant has_map_view {X Y} {f : X -> Y} {Γ} : forall {y}, c_map f Γ ∋ y -> Type :=
| HasMapV {x} (i : Γ ∋ x) : has_map_view (map_has i).

Lemma view_has_map {X Y} {f : X -> Y} {Γ} [y] (i : c_map f Γ ∋ y) : has_map_view i.
Proof.
  induction Γ; dependent elimination i.
  - exact (HasMapV top).
  - destruct (IHΓ v); exact (HasMapV (pop i)).
Qed.
(*|
Additional goodies.
|*)
Definition r_pop {X} {Γ : ctx X} {x} : Γ ⊆ (Γ ▶ x) :=
  fun _ i => pop i.
#[global] Arguments r_pop _ _ _ _/.

Equations r_shift1 {X} {Γ Δ : ctx X} {a} (f : Γ ⊆ Δ) : (Γ ▶ a) ⊆ (Δ ▶ a) :=
  r_shift1 f _ top     := top ;
  r_shift1 f _ (pop i) := pop (f _ i) .

Equations a_append {X} {Γ Δ : ctx X} {F : Fam₁ X (ctx X)} {a}
  : Γ =[F]> Δ -> F Δ a -> (Γ ▶ a) =[F]> Δ :=
  a_append s z _ top     := z ;
  a_append s z _ (pop i) := s _ i .
