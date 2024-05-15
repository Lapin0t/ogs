From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.
From OGS.Ctx Require Import Abstract.

Reserved Notation "F ⇒₀ G" (at level 30).
Reserved Notation "F ⇒₁ G" (at level 30).
Reserved Notation "F ⇒₂ G" (at level 30).
Reserved Notation "u ⦿₀ v" (at level 40).
Reserved Notation "u ⦿₁ v" (at level 40).
Reserved Notation "u ⦿₂ v" (at level 40).
Reserved Notation "F ∥ₛ G" (at level 40).
Reserved Notation "u ⋅ v" (at level 50).
Reserved Notation "⦉ S ⦊" .

Definition Fam₀ (T C : Type) := C -> Type .
Definition Fam₁ (T C : Type) := C -> T -> Type .
Definition Fam₂ (T C : Type) := C -> T -> T -> Type .
Record Oper T C := {
  o_op : T -> Type ;
  o_dom : forall x, o_op x -> C ;
}.

#[global] Arguments o_op {_ _}.
#[global] Arguments o_dom {_ _} [_ _].
#[global] Coercion o_op : Oper >-> Funclass.

Section with_param.
  Context {T C : Type} {CC : context T C}.

  Definition arr_fam₀ (F G : Fam₀ T C) := forall Γ, F Γ -> G Γ.
  Definition arr_fam₁ (F G : Fam₁ T C) := forall Γ x, F Γ x -> G Γ x.
  Definition arr_fam₂ (F G : Fam₂ T C) := forall Γ x y, F Γ x y -> G Γ x y.

  Notation "F ⇒₀ G" := (arr_fam₀ F G).
  Notation "F ⇒₁ G" := (arr_fam₁ F G).
  Notation "F ⇒₂ G" := (arr_fam₂ F G).

  Definition f_id₀ {F : Fam₀ T C} : F ⇒₀ F := fun _ a => a.
  Definition f_id₁ {F : Fam₁ T C} : F ⇒₁ F := fun _ _ a => a.
  Definition f_id₂ {F : Fam₂ T C} : F ⇒₂ F := fun _ _ _ a => a.

  Definition f_comp₀ {F G H : Fam₀ T C} (u : G ⇒₀ H) (v : F ⇒₀ G) : F ⇒₀ H
    := fun _ x => u _ (v _ x).
  Definition f_comp₁ {F G H : Fam₁ T C} (u : G ⇒₁ H) (v : F ⇒₁ G) : F ⇒₁ H
    := fun _ _ x => u _ _ (v _ _ x).
  Definition f_comp₂ {F G H : Fam₂ T C} (u : G ⇒₂ H) (v : F ⇒₂ G) : F ⇒₂ H
    := fun _ _ _ x => u _ _ _ (v _ _ _ x).

  #[global] Arguments f_comp₀ {F G H} u v _ _ /.
  #[global] Arguments f_comp₁ {F G H} u v _ _ _ /.
  #[global] Arguments f_comp₂ {F G H} u v _ _ _ _ /.

  Record f_cut (F G : Fam₁ T C) (Γ : C) :=
    Cut { cut_ty : T ; cut_l : F Γ cut_ty ; cut_r : G Γ cut_ty }. 

  #[global] Arguments Cut {F G Γ cut_ty}.
  #[global] Arguments cut_ty {F G Γ}.
  #[global] Arguments cut_l {F G Γ}.
  #[global] Arguments cut_r {F G Γ}.
  Derive NoConfusion NoConfusionHom for f_cut.

  Definition f_cut_map {F1 F2 G1 G2 : Fam₁ T C} (f : F1 ⇒₁ F2) (g : G1 ⇒₁ G2)
    : (f_cut F1 G1) ⇒₀ (f_cut F2 G2)
    := fun _ c => Cut (f _ _ c.(cut_l)) (g _ _ c.(cut_r)).

  Definition bare_op (O : Oper T C) : Fam₁ T C := fun _ x => O x.
End with_param.

#[global] Notation "F ⇒₀ G" := (arr_fam₀ F G).
#[global] Notation "F ⇒₁ G" := (arr_fam₁ F G).
#[global] Notation "F ⇒₂ G" := (arr_fam₂ F G).

#[global] Notation "u ⦿₀ v" := (f_comp₀ u v).
#[global] Notation "u ⦿₁ v" := (f_comp₁ u v).
#[global] Notation "u ⦿₂ v" := (f_comp₂ u v).

#[global] Notation "F ∥ₛ G" := (f_cut F G).
#[global] Notation "u ⋅ v" := (Cut u v).

#[global] Notation "⦉ S ⦊" := (bare_op S) .
