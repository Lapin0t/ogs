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

From Coinduction Require Import coinduction.

From OGS Require Import Prelude.
From OGS.Ctx Require Import All.
From OGS.OGS Require Export Subst Obs Machine Game Strategy CompGuarded Adequacy Congruence.
From OGS.ITree Require Import Eq Guarded.

Section with_param.
(*|
We consider a language abstractly captured as a machine satisfying an
appropriate axiomatization.
|*)
  Context {T C} {CC : context T C} {CL : context_laws T C}.
  Context {val} {VM : subst_monoid val} {VML : subst_monoid_laws val}.
  Context {conf} {CM : subst_module val conf} {CML : subst_module_laws val conf}.
  Context {obs : obs_struct T C} {M : machine val conf obs} {ML : machine_laws val conf obs}.
  Context {VV : var_assumptions val}.

(*|
Substitution equivalence of two abstract machine configurations (Def 4.21)
|*)
  Definition ciu {Γ} Δ (a b : conf Γ) : Prop
    := forall γ : Γ =[val]> Δ, evalₒ (a ₜ⊛ γ) ≈ evalₒ (b ₜ⊛ γ).
  Notation "x ≈⟦ciu Δ ⟧≈ y" := (ciu Δ x y) (at level 50).

  Definition barb {Γ} Δ (x y : conf Γ) : Prop
    := forall γ : Γ =[val]> Δ,
         (inj_init_act Δ x ∥ inj_init_pas γ)
       ≈ (inj_init_act Δ y ∥ inj_init_pas γ).
  Notation "x ≈⟦barb Δ ⟧≈ y" := (barb Δ x y) (at level 50).

  Theorem barb_correction {Γ} Δ (x y : conf Γ) : x ≈⟦barb Δ ⟧≈ y -> x ≈⟦ciu Δ ⟧≈ y.
  Proof.
    intros H e.
    rewrite (it_eq_wbisim _ _ _ (adequacy x e)), (it_eq_wbisim _ _ _ (adequacy y e)).
    unfold compo_ev_guarded; rewrite 2 iter_evg_iter; apply H.
  Qed.

  Theorem ogs_correction {Γ} Δ (x y : conf Γ) : x ≈⟦ogs Δ ⟧≈ y -> x ≈⟦ciu Δ ⟧≈ y.
  Proof.
    intro H; apply barb_correction.
    intro e; unfold compo.
    rewrite <- 2 (compo_compo_alt (x := RedT _ _)).
    apply compo_alt_proper; [ exact H | intro; reflexivity ].
  Qed.

End with_param.
