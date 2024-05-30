(*|
Coq Prelude
===========

This file contains a bunch of setup, global options and imports.

Our notations have evolved quite organically. It would need refactoring, for now we
just disable warnings related to it.
|*)
#[global] Set Warnings "-notation-overridden".
#[global] Set Warnings "-parsing".
(*|
Enable negative records with definitional eta-equivalence. A requirement for well-behaved
coinductive types.
|*)
#[global] Set Primitive Projections.
(*|
We use a lot of implicit variable declaration around typeclasses.
|*)
#[global] Generalizable All Variables.
(*|
Import the Equations_ library by Matthieu Sozeau, for Agda-like dependent pattern-matching.
We hook it with axiom K (equivalent to unicity of identity proofs, UIP), for even more
powerful matching.

.. _Equations: https://github.com/mattam82/Coq-Equations
|*)
From Equations Require Export Equations.
#[global] Set Equations Transparent.
#[global] Set Equations With UIP.

Lemma YesUIP : forall X : Type, UIP X.
  intro; apply EqdepFacts.eq_dep_eq__UIP, EqdepFacts.eq_rect_eq__eq_dep_eq.
  exact (Eqdep.Eq_rect_eq.eq_rect_eq _).
Qed.
#[global] Existing Instance YesUIP.
(*|
We import dependent induction tactics and inline rewriting notations from the Coq
standard library.
|*)
Require Export Coq.Program.Equality.
Export EqNotations.
(*|
We import basic definition for the use of the universe of strict proposition `SProp`.
|*)
Require Export Coq.Logic.StrictProp.
(*|
A bunch of notations and definitions for basic datatypes.
|*)
#[global] Notation endo T := (T -> T).

#[global] Notation "f ∘ g" := (fun x => f (g x))
 (at level 40, left associativity) : function_scope.

#[global] Notation "a ,' b" := (existT _ a b) (at level 30).

Definition uncurry {A B} {C : A -> B -> Type} (f : forall a b, C a b) (i : A * B)
  := f (fst i) (snd i).

Definition curry {A B} {C : A -> B -> Type} (f : forall i, C (fst i) (snd i)) a b
  := f (a , b).

#[global] Notation curry' := (fun f a b => f (a ,' b)).
#[global] Notation uncurry' := (fun f x => f (projT1 x) (projT2 x)).

#[global] Notation "A × B" := (prod A%type B%type) (at level 20).
(*|
Finite types.
|*)
Variant T0 : Type := .
Variant T1 : Type := T1_0.
Variant T2 : Type := T2_0 | T2_1.
Variant T3 : Type := T3_0 | T3_1 | T3_2.
Derive NoConfusion for T0.
Derive NoConfusion for T1.
Derive NoConfusion for T2.
Derive NoConfusion for T3.
(*|
Absurdity elimination.
|*)
Definition ex_falso {A : Type} (bot : T0) : A := match bot with end.
(*|
Decidable predicates.
|*)
#[global] Notation "¬ P" := (P -> T0) (at level 5).
Variant decidable (X : Type) : Type :=
| Yes : X -> decidable X
| No : ¬X -> decidable X
.
Derive NoConfusion NoConfusionHom for decidable.
(*|
Subset types based on strict propositions.
|*)
Record sigS {X : Type} (P : X -> SProp) := { sub_elt : X ; sub_prf : P sub_elt }.
Arguments sub_elt {X P}.
Arguments sub_prf {X P}.

Lemma sigS_eq {X : Type} {P : X -> SProp} (a b : sigS P)
  (H : a.(sub_elt) = b.(sub_elt)) : a = b .
  destruct a as [ e p ]; cbn in H.
  revert p; rewrite H; intro p.
  change p with b.(sub_prf); reflexivity.
Qed.
(*|
Misc.
|*)
Definition substS {X : SProp} (P : X -> Type) (a b : X) : P a -> P b := fun p => p .

Lemma eq_refl_map2_distr [A B C : Type] (x : A) (y : B) (f : A -> B -> C)
  : f_equal2 f (@eq_refl _ x) (@eq_refl _ y) = eq_refl .
  apply YesUIP.
Qed.

Definition injective {A B : Type} (f : A -> B) := forall x y : A, f x = f y -> x = y .
