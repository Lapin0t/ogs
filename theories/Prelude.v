#[global] Set Warnings "-notation-overridden".
#[global] Set Warnings "-parsing".

#[global] Set Primitive Projections.
#[global] Generalizable All Variables.

From Equations Require Export Equations.
#[global] Set Equations Transparent.
#[global] Set Equations With UIP.

Require Export Coq.Program.Equality.
Export EqNotations.
Require Export Coq.Logic.StrictProp.

Require Import Coq.Lists.List.
Export ListNotations.

(* hook-up Equations' UIP class with Coq's axiom K *)
Lemma YesUIP : forall X : Type, UIP X.
  intro; apply EqdepFacts.eq_dep_eq__UIP, EqdepFacts.eq_rect_eq__eq_dep_eq.
  exact (Eqdep.Eq_rect_eq.eq_rect_eq _).
Qed.
#[global] Existing Instance YesUIP.

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

Variant T0 : Type := .
Variant T1 : Type := T1_0.
Variant T2 : Type := T2_0 | T2_1.
Variant T3 : Type := T3_0 | T3_1 | T3_2.
Derive NoConfusion for T0.
Derive NoConfusion for T1.
Derive NoConfusion for T2.
Derive NoConfusion for T3.

Definition ex_falso {A : Type} (bot : T0) : A := match bot with end.

#[global] Notation "¬ P" := (P -> T0) (at level 5).
Variant decidable (X : Type) : Type :=
| Yes : X -> decidable X
| No : ¬X -> decidable X
.
Derive NoConfusion NoConfusionHom for decidable.

Record sigS {X : Type} (P : X -> SProp) := { sub_elt : X ; sub_prf : P sub_elt }.
Arguments sub_elt {X P}.
Arguments sub_prf {X P}.

Lemma sigS_eq {X : Type} {P : X -> SProp} (a b : sigS P) : a.(sub_elt) = b.(sub_elt) -> a = b .
  intro H; destruct a as [ e p ]; cbn in H.
  revert p; rewrite H; intro p.
  change p with b.(sub_prf); reflexivity.
Qed.

Definition substS {X : SProp} (P : X -> Type) (a b : X) : P a -> P b := fun p => p .

Lemma eq_refl_map2_distr [A B C : Type] (x : A) (y : B) (f : A -> B -> C) : f_equal2 f (@eq_refl _ x) (@eq_refl _ y) = eq_refl .
  apply YesUIP.
Qed.

Definition injective {A B : Type} (f : A -> B) := forall x y : A, f x = f y -> x = y .
