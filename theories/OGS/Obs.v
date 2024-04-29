From Coinduction Require Import coinduction tactics.

From OGS Require Import Prelude.
From OGS.Utils Require Import Rel.
From OGS.Ctx Require Import All.
From OGS.OGS Require Import Subst.
From OGS.ITree Require Import Event ITree Delay Eq.

Open Scope ctx_scope.
Reserved Notation "O ∙" (at level 5).
Reserved Notation "i ⋅ o ⦉ a ⦊" (at level 30).
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
#[global] Notation obs_struct T := (f_slice T).
#[global] Notation dom := s_dom.
#[global] Coercion s_op : obs_struct >-> Funclass.

Definition pointed_obs {T} (O : obs_struct T) : Fam T := var ∥ ⦇ O ⦈.
#[global] Notation "O ∙" := (pointed_obs O).
Definition nf {T} (O : obs_struct T) (X : Fam₁ T) : Fam T := var ∥ (O # X).

Definition mk_nf {T} {O : obs_struct T} {X : Fam₁ T} {Γ t}
           (i : t ∈ Γ) (o : O t) (a : dom o =[X]> Γ)
  : nf O X Γ
  := ⟨ i | OFill o a ⟩.
#[global] Notation "i ⋅ o ⦉ a ⦊" := (mk_nf i o a%asgn).

Definition nf_to_obs {T O} {X : Fam₁ T} : forall Γ, nf O X Γ -> O∙ Γ
  := f_cut_map f_id₁ forget_args.
#[global] Coercion nf_to_obs : nf >-> pointed_obs.

Definition then_to_obs {T O} {X : Fam₁ T} {Γ} : delay (nf O X Γ) -> delay (O∙ Γ)
  := fmap_delay (nf_to_obs Γ).

Section with_param.
  Context {T : Type} {O : obs_struct T} {X : Fam₁ T}.

  Definition nf_ty {Γ} (n : nf O X Γ) : T
    := n.(cut_ty).
  Definition nf_var {Γ} (n : nf O X Γ) : nf_ty n ∈ Γ
    := n.(cut_l).
  Definition nf_obs {Γ} (n : nf O X Γ) : O (nf_ty n)
    := n.(cut_r).(fill_op).
  Definition nf_dom {Γ} (n : nf O X Γ) : ctx T
    := dom n.(cut_r).(fill_op).
  Definition nf_args {Γ} (n : nf O X Γ) : nf_dom n =[X]> Γ
    := n.(cut_r).(fill_args).

  Variant nf_eq {Γ} : nf O X Γ -> nf O X Γ -> Prop :=
  | NfEq {t} {i : t ∈ Γ} {o a1 a2} : a1 ≡ₐ a2 -> nf_eq (i⋅o⦉a1⦊) (i⋅o⦉a2⦊).

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
    intros a b; revert a b; unfold it_eq; coinduction R CIH; intros a b H.
    unfold comp_eq in H; apply it_eq_step in H.
    cbn in *; unfold observe in H.
    destruct (_observe a), (_observe b); dependent elimination H; econstructor.
    - cbn in r_rel; now destruct r_rel.
    - now apply CIH.
    - destruct q1.
  Qed.
End with_param.

#[global] Notation "u ≋ v" := (comp_eq u v).
