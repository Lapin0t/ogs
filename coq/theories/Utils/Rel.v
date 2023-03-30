From Coq.Classes Require Import RelationClasses.
From Coinduction Require Import lattice.
From OGS.Utils Require Import Psh.

#[export] Existing Instance CompleteLattice_dfun.

Notation relᵢ A B := (forall i, A i -> B i -> Prop).

#[global] Notation Reflexiveᵢ R := (forall i, Reflexive (R i)).
#[global] Notation Symmetricᵢ R := (forall i, Symmetric (R i)).
#[global] Notation Transitiveᵢ R := (forall i, Transitive (R i)).
#[global] Notation Subrelationᵢ R S := (forall i, subrelation (R i) (S i)).

Definition eqᵢ {I : Type} {X : psh I} : relᵢ X X := fun i x y => x = y.
Arguments eqᵢ _ _ _ /.

#[global] Instance Reflexive_eqᵢ {I} {X : psh I} : Reflexiveᵢ (@eqᵢ I X).
Proof. intros i x; reflexivity. Qed.

#[global] Instance Symmetric_eqᵢ {I} {X : psh I} : Symmetricᵢ (@eqᵢ I X).
Proof. intros i x y e; symmetry; exact e. Qed.

#[global] Instance Transitive_eqᵢ {I} {X : psh I} : Transitiveᵢ (@eqᵢ I X).
Proof. intros i x y z a b; transitivity y; [exact a | exact b]. Qed.

Definition seqᵢ {I} {X Y Z : psh I} (R0 : relᵢ X Y) (R1 : relᵢ Y Z) : relᵢ X Z :=
  fun i x z => exists y, R0 i x y /\ R1 i y z.
#[global] Infix "⨟" := (seqᵢ) (at level 120).
#[global] Notation "u ⨟⨟ v" := (ex_intro _ _ (conj u v)) (at level 70).

Definition revᵢ {I} {X Y : psh I} (R : relᵢ X Y) : relᵢ Y X := fun i x y => R i y x.

Definition orᵢ {I} {X Y : psh I} (R S : relᵢ X Y) : relᵢ X Y := fun i x y => R i x y \/ S i x y.
#[global] Infix "∨ᵢ" := (orᵢ) (at level 70).
