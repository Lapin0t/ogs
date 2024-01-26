(*|
Soundness (Theorem 6.12)
========================
Finally, all the pieces are in place to prove that bisimilarity of induced LTS is sound
w.r.t. substitution equivalence.
Having worked hard to establish adequacy and congruence of weak bisimilarity for composition,
very little remains to do here.

At the end of the file, we run two commands:
- [About ogs_correction.] explicit the assumptions of the theorem, that we show how to instantiate in the [Example] folder on several concrete examples of languages.
- [Print Assumptions ogs_correction.] explicit if any axiom has been used to establish the result. As stated in the Readme, we exclusively use [Eqdep.Eq_rect_eq.eq_rect_eq] (i.e., axiom K).
|*)

From Coinduction Require Import coinduction tactics.

From OGS Require Import Prelude.
From OGS.Utils Require Import Ctx Rel.
From OGS.OGS Require Export Subst Obs Machine Game Strategy CompGuarded Adequacy Congruence.
From OGS.ITree Require Import Event ITree Eq Delay Structure Properties Guarded.

Open Scope ctx_scope.

Section withFam.

(*|
We consider a language abstractly captured as a machine
|*)
  Context {bT : baseT}.
  Context {bV : baseV}.
  Context {bC : baseC}.
  Context {sV : subst_monoid bV}.
  Context {sC : subst_module bV bC}.
  Context {oS : observation_structure}.
  Context {M: machine}.
(*|
Satisfying an appropriate axiomatization
|*)
  Context {sVL: subst_monoid_laws}.
  Context {sCL: subst_module_laws}.
  Context {VA : var_assumptions} .
  Context {ML: machine_laws}.

(*|
Substitution equivalence of two abstract machine configurations (Def 4.21)
|*)
  Definition ciu {Γ} Δ (x y : conf Γ) : Prop
    := forall e : Γ ⇒ᵥ Δ, eval_in_env e x ≈ eval_in_env e y.
  Notation "x ≈⟦ciu Δ ⟧≈ y" := (ciu Δ x y) (at level 50).

  Definition barb {Γ} Δ (x y : conf Γ) : Prop
    := forall e : Γ ⇒ᵥ Δ, (inj_init_act Δ x ∥ inj_init_pas e) ≈ (inj_init_act Δ y ∥ inj_init_pas e).
  Notation "x ≈⟦barb Δ ⟧≈ y" := (barb Δ x y) (at level 50).

  Theorem barb_correction {Γ} Δ (x y : conf Γ) : x ≈⟦barb Δ ⟧≈ y -> x ≈⟦ciu Δ ⟧≈ y.
  Proof.
    intros H e.
    etransitivity; [ apply it_eq_wbisim, (adequacy x e) | ].
    etransitivity; [ apply iter_evg_iter | ].
    etransitivity; [ apply (H e) | symmetry ].
    etransitivity; [ apply it_eq_wbisim, (adequacy y e) | ].
    etransitivity; [ apply iter_evg_iter | ].
    reflexivity.
  Qed.

  Theorem ogs_correction {Γ} Δ (x y : conf Γ) : x ≈⟦ogs Δ ⟧≈ y -> x ≈⟦ciu Δ ⟧≈ y.
  Proof.
    intro H; apply barb_correction.
    intro e; unfold compo.
    rewrite <- 2 compo_compo_alt.
    apply compo_alt_proper; [ exact H | intro; reflexivity ].
  Qed.

End withFam.
About ogs_correction.
Print Assumptions ogs_correction.
