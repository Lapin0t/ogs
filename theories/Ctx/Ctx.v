(*|
Free context structure
======================

Here we instanciate our abstract notion of context structure with the most common example:
lists and DeBruijn indices. More pedantically, this is the free context structure over
a given set ``X``.

.. coq:: none
|*)
From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.
From OGS.Ctx Require Import All.

#[local] Open Scope ctx_scope.
(*|
Contexts
---------

Contexts are simply lists, with the purely aesthetic choice of representing cons as
coming from the right. Note on paper: we write here "Γ ▶ x" instead of "Γ , x".

.. coq::
   :name: concretectx
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
#[global] Bind Scope ctx_scope with ctx.
(*|
|*)
#[global] Notation "∅ₓ" := (cnil) : ctx_scope.
#[global] Notation "Γ ▶ₓ x" := (ccon Γ%ctx x) (at level 40, left associativity) : ctx_scope.
(*|
We wish to manipulate intrinsically typed terms. We hence need a tightly typed notion of
position in the context: rather than a loose index, ``var x Γ`` is a proof of membership
of ``x`` to ``Γ``: a well-scoped and well-typed DeBruijn index. See Ex. 5.
.. coq::
   :name: concretevar
|*)
Inductive var {X} (x : X) : ctx X -> Type :=
| top {Γ} : var x (Γ ▶ₓ x)
| pop {Γ y} : var x Γ -> var x (Γ ▶ₓ y).
Definition cvar {X} Γ x := @var X x Γ.
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
  c_length ∅ₓ       := Datatypes.O ;
  c_length (Γ ▶ₓ _) := Datatypes.S (c_length Γ) .

Equations ccat {X} : ctx X -> ctx X -> ctx X :=
  ccat Γ ∅ₓ       := Γ ;
  ccat Γ (Δ ▶ₓ x) := ccat Γ Δ ▶ₓ x .

Equations c_map {X Y} : (X -> Y) -> ctx X -> ctx Y :=
  c_map f ∅ₓ       := cnil ;
  c_map f (Γ ▶ₓ x) := c_map f Γ ▶ₓ f x .
(*|
Implementation of the revelant part of the abstract context interface.
|*)
#[global] Instance free_context {X} : context X (ctx X) :=
  {| c_emp := cnil ; c_cat := ccat ; c_var := cvar |}.
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
  map_has (Γ ▶ₓ _) top     := top ;
  map_has (Γ ▶ₓ _) (pop i) := pop (map_has Γ i) .
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
Definition r_pop {X} {Γ : ctx X} {x} : Γ ⊆ (Γ ▶ₓ x) :=
  fun _ i => pop i.
#[global] Arguments r_pop _ _ _ _/.

Equations a_append {X} {Γ Δ : ctx X} {F : Fam₁ X (ctx X)} {a}
  : Γ =[F]> Δ -> F Δ a -> (Γ ▶ₓ a) =[F]> Δ :=
  a_append s z _ top     := z ;
  a_append s z _ (pop i) := s _ i .
#[global] Notation "[ u ,ₓ x ]" := (a_append u x) (at level 9) : asgn_scope.

#[global] Instance a_append_eq {X Γ Δ F a}
  : Proper (asgn_eq _ _ ==> eq ==> asgn_eq _ _) (@a_append X Γ Δ F a).
Proof.
  intros ?? Hu ?? Hx ? i.
  dependent elimination i; cbn.
  - exact Hx.
  - now apply Hu.
Qed.
(*|
These concrete definition of shifts compute better than their `generic counterpart
<Renaming.html#rshift>`_.
|*)
Definition r_shift1 {X} {Γ Δ : ctx X} {a} (f : Γ ⊆ Δ)
  : (Γ ▶ₓ a) ⊆ (Δ ▶ₓ a)
  := [ f ᵣ⊛ r_pop ,ₓ top ].

Definition r_shift2 {X} {Γ Δ : ctx X} {a b} (f : Γ ⊆ Δ)
  : (Γ ▶ₓ a ▶ₓ b) ⊆ (Δ ▶ₓ a ▶ₓ b)
  := [ [ f ᵣ⊛ r_pop ᵣ⊛ r_pop ,ₓ pop top ] ,ₓ top ].

Definition r_shift3 {X} {Γ Δ : ctx X} {a b c} (f : Γ ⊆ Δ)
  : (Γ ▶ₓ a ▶ₓ b ▶ₓ c) ⊆ (Δ ▶ₓ a ▶ₓ b ▶ₓ c)
  := [ [ [ f ᵣ⊛ r_pop ᵣ⊛ r_pop ᵣ⊛ r_pop ,ₓ pop (pop top) ] ,ₓ pop top ] ,ₓ top ].

#[global] Instance r_shift1_eq {X Γ Δ a}
  : Proper (asgn_eq _ _ ==> asgn_eq _ _) (@r_shift1 X Γ Δ a).
Proof.
  intros ?? Hu; unfold r_shift1; now rewrite Hu.
Qed.

#[global] Instance r_shift2_eq {X Γ Δ a b}
  : Proper (asgn_eq _ _ ==> asgn_eq _ _) (@r_shift2 X Γ Δ a b).
Proof.
  intros ?? Hu; unfold r_shift2; now rewrite Hu.
Qed.

#[global] Instance r_shift3_eq {X Γ Δ a b c}
  : Proper (asgn_eq _ _ ==> asgn_eq _ _) (@r_shift3 X Γ Δ a b c).
Proof.
  intros ?? Hu; unfold r_shift3; now rewrite Hu.
Qed.

Lemma r_shift1_id {X Γ a} : @r_shift1 X Γ Γ a r_id ≡ₐ r_id .
  intros ? v; now repeat (dependent elimination v; auto).
Qed.

Lemma r_shift2_id {X Γ a b} : @r_shift2 X Γ Γ a b r_id ≡ₐ r_id .
  intros ? v; now repeat (dependent elimination v; auto).
Qed.

Lemma r_shift3_id {X Γ a b c} : @r_shift3 X Γ Γ a b c r_id ≡ₐ r_id .
  intros ? v; now repeat (dependent elimination v; auto).
Qed.

Lemma r_shift1_comp {X Γ1 Γ2 Γ3 a} (r1 : Γ1 ⊆ Γ2) (r2 : Γ2 ⊆ Γ3)
      : @r_shift1 X Γ1 Γ3 a (r1 ᵣ⊛ r2) ≡ₐ r_shift1 r1 ᵣ⊛ r_shift1 r2 .
  intros ? v; now repeat (dependent elimination v; auto).
Qed.

Lemma r_shift2_comp {X Γ1 Γ2 Γ3 a b} (r1 : Γ1 ⊆ Γ2) (r2 : Γ2 ⊆ Γ3)
      : @r_shift2 X Γ1 Γ3 a b (r1 ᵣ⊛ r2) ≡ₐ r_shift2 r1 ᵣ⊛ r_shift2 r2 .
  intros ? v; now repeat (dependent elimination v; auto).
Qed.

Lemma r_shift3_comp {X Γ1 Γ2 Γ3 a b c} (r1 : Γ1 ⊆ Γ2) (r2 : Γ2 ⊆ Γ3)
      : @r_shift3 X Γ1 Γ3 a b c (r1 ᵣ⊛ r2) ≡ₐ r_shift3 r1 ᵣ⊛ r_shift3 r2 .
  intros ? v; now repeat (dependent elimination v; auto).
Qed.
(*|
This is the end for now, but we have not yet instanciated the rest of the abstract
context structure. This is a bit more work, it takes place in another file:
`Ctx/Covering.v <Covering.html>`_
|*)
