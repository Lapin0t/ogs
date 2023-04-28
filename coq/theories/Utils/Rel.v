From Coq.Classes Require Import RelationClasses.
From Coinduction Require Import lattice.
From OGS.Utils Require Import Psh.

#[export] Existing Instance CompleteLattice_dfun.

Notation relᵢ A B := (forall i, A i -> B i -> Prop).

#[global] Notation Reflexiveᵢ R := (forall i, Reflexive (R i)).
#[global] Notation Symmetricᵢ R := (forall i, Symmetric (R i)).
#[global] Notation Transitiveᵢ R := (forall i, Transitive (R i)).
#[global] Notation Equivalenceᵢ R := (forall i, Equivalence (R i)).
#[global] Notation Subrelationᵢ R S := (forall i, subrelation (R i) (S i)).
#[global] Notation PreOrderᵢ R := (forall i, PreOrder (R i)).

Definition eqᵢ {I} (X : psh I) : relᵢ X X := fun _ x y => x = y.
Arguments eqᵢ _ _ _ /.

#[global] Instance Reflexive_eqᵢ {I} {X : psh I} : Reflexiveᵢ (eqᵢ X).
Proof. intros ? ?; reflexivity. Qed.

#[global] Instance Symmetric_eqᵢ {I} {X : psh I} : Symmetricᵢ (eqᵢ X).
Proof. intros ? ? ? ?; now symmetry. Qed.

#[global] Instance Transitive_eqᵢ {I} {X : psh I} : Transitiveᵢ (eqᵢ X).
Proof. intros i x y z a b; now transitivity y. Qed.

Variant sumᵣ {I} {X1 X2 Y1 Y2 : psh I} (R : relᵢ X1 X2) (S : relᵢ Y1 Y2) : relᵢ (X1 +ᵢ Y1) (X2 +ᵢ Y2) :=
  | RLeft {i x1 x2} : R i x1 x2 -> sumᵣ R S i (inl x1) (inl x2)
  | RRight {i y1 y2} : S i y1 y2 -> sumᵣ R S i (inr y1) (inr y2)
.

Definition seqᵢ {I} {X Y Z : psh I} (R0 : relᵢ X Y) (R1 : relᵢ Y Z) : relᵢ X Z :=
  fun i x z => exists y, R0 i x y /\ R1 i y z.
#[global] Infix "⨟" := (seqᵢ) (at level 120).
#[global] Notation "u ⨟⨟ v" := (ex_intro _ _ (conj u v)) (at level 70).
#[global] Hint Unfold seqᵢ : core.

#[global] Instance seq_mon {I} {X Y Z : psh I} : Proper (leq ==> leq ==> leq) (@seqᵢ I X Y Z).
Proof. intros ? ? H1 ? ? H2 ? ? ? [z []]. exists z. split. now apply H1. now apply H2. Qed.

Definition squareᵢ {I} {X : psh I} : mon (relᵢ X X) :=
  {| body R := R ⨟ R ; Hbody _ _ H := seq_mon _ _ H _ _ H |}.

Definition revᵢ {I} {X Y : psh I} (R : relᵢ X Y) : relᵢ Y X := fun i x y => R i y x.
#[global] Hint Unfold revᵢ : core.

#[global] Instance rev_mon {I} {X Y : psh I} : Proper (leq ==> leq) (@revᵢ I X Y).
Proof. firstorder. Qed.

Definition converseᵢ {I} {X : psh I} : mon (relᵢ X X) :=
  {| body := revᵢ ; Hbody := rev_mon |}.

Definition orᵢ {I} {X Y : psh I} (R S : relᵢ X Y) : relᵢ X Y := fun i x y => R i x y \/ S i x y.
#[global] Infix "∨ᵢ" := (orᵢ) (at level 70).
#[global] Instance or_mon {I} {X Y : psh I} : Proper (leq ==> leq ==> leq) (@orᵢ I X Y).
Proof. firstorder. Qed.

Lemma build_reflexive {I} {X : psh I} {R : relᵢ X X} : eqᵢ X <= R -> Reflexiveᵢ R.
Proof. intros H ? ?. now apply H. Qed.

Lemma use_reflexive {I} {X : psh I} {R : relᵢ X X} (H : Reflexiveᵢ R) : eqᵢ X <= R.
Proof. intros ? ? ? ->; now reflexivity. Qed.

Lemma build_symmetric {I} {X : psh I} {R : relᵢ X X} : converseᵢ R <= R -> Symmetricᵢ R.
Proof. intros H ? ? ? ?. now apply H. Qed.

Lemma use_symmetric {I} {X : psh I} {R : relᵢ X X} (H : Symmetricᵢ R) : converseᵢ R <= R.
Proof. intros ? ? ? ?; now symmetry. Qed.

Lemma build_transitive {I} {X : psh I} {R : relᵢ X X} : squareᵢ R <= R -> Transitiveᵢ R.
Proof. intros H i x y z r s. apply H; now exists y. Qed.

Lemma use_transitive {I} {X : psh I} {R : relᵢ X X} (H : Transitiveᵢ R) : squareᵢ R <= R.
Proof. intros ? ? ? [ y [ ? ? ] ]. now transitivity y. Qed.

Lemma build_equivalence {I} {X : psh I} {R : relᵢ X X}
      : eqᵢ X <= R -> converseᵢ R <= R -> squareᵢ R <= R -> Equivalenceᵢ R.
Proof.
  econstructor.
  now apply build_reflexive.
  now apply build_symmetric.
  now apply build_transitive.
Qed.
