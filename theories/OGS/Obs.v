From OGS Require Import Prelude.
From OGS.Utils Require Import Rel.
From OGS.Ctx Require Import All.
From OGS.OGS Require Import Subst.
From OGS.ITree Require Import Event ITree Delay Eq Properties.

Open Scope ctx_scope.
Reserved Notation "O ∙" (at level 5).
Reserved Notation "'dom∙' o" (at level 5).
(*Reserved Notation "i ⋅ o ⦉ a ⦊" (at level 30).*)
Reserved Notation "u ≋ v" (at level 40).

(*|
Observation Structure (§ 4.4)
==============================

The messages that player and opponent exchange in the OGS
arise from splitting normal forms into the head variable
on which it is stuck, an observation, and an assignment.

An **observation structure** axiomatizes the observations
of the language:
- a Type [typ] of types (assumed globally in §4),
- a type-indexed set [obs] of observations,
- a map [dom] mapping observations to values filling their copattern

|*)
#[global] Notation obs_struct T C := (Oper T C).
#[global] Notation dom := o_dom.
Definition pointed_obs `{CC : context T C} (O : Oper T C) : Fam₀ T C
  := c_var ∥ₛ ⦉O⦊.
#[global] Notation "O ∙" := (pointed_obs O).
#[global] Notation m_var o := (o.(cut_l)).
#[global] Notation m_obs o := (o.(cut_r)).
#[global] Notation m_dom o := (o_dom o.(cut_r)).

Definition nf `{CC : context T C} (O : obs_struct T C) (X : Fam₁ T C) : Fam₀ T C
  := c_var ∥ₛ (O # X).

Definition nf_to_obs `{CC : context T C} {O} {X : Fam₁ T C} : forall Γ, nf O X Γ -> O∙ Γ
  := f_cut_map f_id₁ forget_args.
#[global] Coercion nf_to_obs : nf >-> pointed_obs.

Definition then_to_obs `{CC : context T C} {O} {X : Fam₁ T C} {Γ}
  : delay (nf O X Γ) -> delay (O∙ Γ)
  := fmap_delay (nf_to_obs Γ).

Section with_param.
  Context `{CC : context T C} {O : obs_struct T C} {X : Fam₁ T C}.

  Definition nf_ty {Γ} (n : nf O X Γ) : T
    := n.(cut_ty).
  Definition nf_var {Γ} (n : nf O X Γ) : Γ ∋ nf_ty n
    := n.(cut_l).
  Definition nf_obs {Γ} (n : nf O X Γ) : O (nf_ty n)
    := n.(cut_r).(fill_op).
  Definition nf_dom {Γ} (n : nf O X Γ) : C
    := dom n.(cut_r).(fill_op).
  Definition nf_args {Γ} (n : nf O X Γ) : nf_dom n =[X]> Γ
    := n.(cut_r).(fill_args).

  Variant nf_eq {Γ} : nf O X Γ -> nf O X Γ -> Prop :=
  | NfEq {t} {i : Γ ∋ t} {o a1 a2} : a1 ≡ₐ a2 -> nf_eq (i⋅o⦇a1⦈) (i⋅o⦇a2⦈).

  #[global] Instance nf_eq_Equivalence {Γ} : Equivalence (@nf_eq Γ).
  Proof.
    split.
    - intros ?; now econstructor.
    - intros ?? []; now econstructor.
    - intros ??? [] h2; dependent induction h2.
      econstructor; now transitivity a2.
  Qed.

  Definition comp_eq {Γ} : relation (delay (nf O X Γ))
    := it_eq (fun _ : T1 => nf_eq) (i := T1_0).

  #[global] Instance then_to_obs_proper {Γ}
    : Proper (@comp_eq Γ ==> it_eq (eqᵢ _) (i:=_)) then_to_obs.
  Proof.
    intros a b; unfold comp_eq, then_to_obs, fmap_delay; cbn; intros H.
    eapply fmap_eq; [ | exact H ].
    now intros [] ?? [].
  Qed.
End with_param.

#[global] Notation "u ≋ v" := (comp_eq u v).
