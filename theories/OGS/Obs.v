From Coinduction Require Import coinduction tactics.

From OGS Require Import Prelude.
From OGS.Utils Require Import Ctx Rel.
From OGS.Game Require Import HalfGame Event.
From OGS.OGS Require Import Subst.
From OGS.ITree Require Import ITree Delay Eq.

Open Scope ctx_scope.

Section withFam.
  Context {bT : baseT}.

(*|
Observation Structure (§ 5.4)
==============================

The messages that player and opponent exchange in the OGS
arise from splitting normal forms into the head variable
on which it is stuck, an observation, and an assignment.

An **observation structure** axiomatizes the observations
of the language:
- a Type [typ] of types (assumed globally in Section 5),
- a type-indexed set [obs] of observations,
- a map [dom] mapping observations to values filling their copattern

|*)
  Class observation_structure : Type := {
      obs : typ -> Type ;
      dom : forall t, obs t -> ctx typ ;
    }.
  Arguments dom {_} [_].

  Context {O : observation_structure}.

(*|
Given an observation structure, we define the family of pointed observations
(Definition 5.15) packaging them into a type, and an observation at
this type.
|*)
  Notation context := (ctx typ).
  Definition obs' (Γ : context) : Type := { t : typ & Γ ∋ t * obs t }%type.
  Notation "obs∙" := obs'.

  Definition obs'_ty {Γ} (o : obs∙ Γ) : typ := projT1 o.
  Notation "ty∙ o" := (obs'_ty o) (at level 10).
  Definition obs'_var {Γ} (o : obs∙ Γ) : Γ ∋ ty∙ o := fst (projT2 o).
  Definition obs'_obs {Γ} (o : obs∙ Γ) : obs (ty∙ o) := snd (projT2 o).
  Definition obs'_dom {Γ} (o : obs∙ Γ) : context := dom (obs'_obs o).
  Notation "dom∙ o" := (obs'_dom o) (at level 10).

(*|
Given an observation structure and a sorted family of values,
we can define normal forms as a pair of a pointed observation and an
assignment for its domain.
The following definition is equivalent, but with a slightly different packaging.
|*)
  Context {bV : baseV}.
  Context {sV : subst_monoid bV}.

  Definition nf  (Γ : context) (t : typ) : Type := { m : obs t & dom m ⇒ᵥ Γ }.
  Definition nf' (Γ : context) : Type := { t : typ & Γ ∋ t * nf Γ t }%type.
  Notation "nf∙" := nf'.

  Definition nf'_ty {Γ} : nf∙ Γ -> typ := @projT1 _ _.
  Definition nf'_var {Γ} (u : nf∙ Γ) : Γ ∋ (nf'_ty u) := fst (projT2 u).
  Definition nf'_nf {Γ} (u : nf∙ Γ) : nf Γ (nf'_ty u) := snd (projT2 u).
  Definition nf'_obs {Γ} (u : nf∙ Γ) : obs (nf'_ty u) := projT1 (snd (projT2 u)).
  Definition nf'_val {Γ} (u : nf∙ Γ) : dom (nf'_obs u) ⇒ᵥ Γ := projT2 (snd (projT2 u)).

  Definition nf_eq {Γ t} : relation (nf Γ t) :=
    fun a b => exists H : projT1 a = projT1 b,
        rew H in projT2 a ≡ₐ projT2 b.

  Definition nf'_eq {Γ} : relation (nf∙ Γ) :=
    fun a b => exists H : nf'_ty a = nf'_ty b,
        (rew H in nf'_var a = nf'_var b) /\ (nf_eq (rew H in nf'_nf a) (nf'_nf b)).

  Definition comp_eq {Γ} : relation (delay (nf∙ Γ)) :=
    it_eq (fun _ : T1 => nf'_eq) (i := T1_0).
  Notation "u ≋ v" := (comp_eq u v) (at level 40).

  Definition obs'_of_nf' : nf∙ ⇒ᵢ obs∙ :=
    fun Γ u => (nf'_ty u ,' (nf'_var u , nf'_obs u)).

  Definition nf'_of_obs' {Γ} (o : obs∙ Γ) : nf∙ (Γ +▶ dom∙ o) :=
    (obs'_ty o ,' (r_concat_l _ (obs'_var o) , (obs'_obs o ,' v_var ⊛ᵣ r_concat_r))).

  #[global] Instance nf_eq_rfl {Γ t} : Reflexive (@nf_eq Γ t) .
    intros a; exists eq_refl; auto.
  Qed.

  #[global] Instance nf_eq_sym {Γ t} : Symmetric (@nf_eq Γ t) .
    intros a b [ p q ].
    unshelve econstructor.
    - now symmetry.
    - intros ? i.
      destruct a as [ m a ] ; cbn in *.
      revert a q i; rewrite p; clear p; intros a q i.
      symmetry; apply q.
  Qed.

  #[global] Instance nf_eq_tra {Γ t} : Transitive (@nf_eq Γ t) .
    intros a b c [ p1 q1 ] [ p2 q2 ].
    unfold nf_eq.
    unshelve econstructor.
    - now transitivity (projT1 b).
    - transitivity (rew [fun m : obs t => dom m ⇒ᵥ Γ] p2 in projT2 b); auto.
      now rewrite <- p2.
  Qed.

  #[global] Instance nf_eq_rfl' {Γ} : Reflexiveᵢ (fun _ : T1 => @nf'_eq Γ) .
    intros _ [ x [ i n ] ].
    unshelve econstructor; auto.
  Qed.

  #[global] Instance nf_eq_sym' {Γ} : Symmetricᵢ (fun _ : T1 => @nf'_eq Γ) .
    intros _ [ x1 [ i1 n1 ] ] [ x2 [ i2 n2 ] ] [ p [ q1 q2 ] ].
    unshelve econstructor; [ | split ]; cbn in *.
    - now symmetry.
    - revert i1 q1; rewrite p; intros i1 q1; now symmetry.
    - revert n1 q2; rewrite p; intros n1 q2; now symmetry.
  Qed.

  #[global] Instance nf_eq_tra' {Γ} : Transitiveᵢ (fun _ : T1 => @nf'_eq Γ) .
    intros _ [ x1 [ i1 n1 ] ] [ x2 [ i2 n2 ] ] [ x3 [ i3 n3 ] ] [ p1 [ q1 r1 ] ] [ p2 [ q2 r2 ] ].
    unshelve econstructor; [ | split ]; cbn in *.
    - now transitivity x2.
    - transitivity (rew [has Γ] p2 in i2); auto.
      now rewrite <- p2.
    - transitivity (rew [nf Γ] p2 in n2); auto.
      now rewrite <- p2.
  Qed.

  Lemma eval_to_obs_eq {Γ} (a b : delay (nf∙ Γ)) (H : a ≋ b) :
    fmap_delay (@obs'_of_nf' Γ) a ≊ fmap_delay (@obs'_of_nf' Γ) b .
  Proof.
    revert a b H; unfold it_eq; coinduction R CIH; intros a b H.
    unfold comp_eq in H; apply it_eq_step in H.
    cbn in *; unfold observe in H.
    destruct (_observe a), (_observe b); dependent elimination H; econstructor.
    - destruct r_rel as [ p [ q [ r _ ] ] ].
      destruct r1 as [ x1 [ i1 [ m1 a1 ] ] ], r2 as [ x2 [ i2 [ m2 a2 ] ] ].
      unfold obs'_of_nf', nf'_ty, nf'_var, nf'_obs in *; cbn in *.
      revert i1 m1 a1 q r; rewrite p; intros i1 m1 a1 q r.
      now do 2 f_equal.
    - now apply CIH.
    - inversion q1.
  Qed.

End withFam.

Arguments dom {_ _} [_].
#[global] Notation context := (ctx typ).
#[global] Notation "obs∙ Γ" := (obs' Γ) (at level 10).
#[global] Notation "ty∙ o" := (obs'_ty o) (at level 10).
#[global] Notation "dom∙ o" := (obs'_dom o) (at level 10).
#[global] Notation "nf∙ Γ" := (nf' Γ) (at level 10).
#[global] Notation "u ≋ v" := (comp_eq u v) (at level 40).
