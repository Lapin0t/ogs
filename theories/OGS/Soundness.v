(*|
Soundness (Theorem 6.12)
========================

Finally, all the pieces are in place to prove that bisimilarity of induced LTS is sound
w.r.t. substitution equivalence. Having worked hard to establish
`adequacy <Adequacy.html>`_ and `congruence <Congruence.html>`_
of weak bisimilarity for composition, very little remains to do here.

.. coq:: none
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
We define substitution equivalence of two language machine configurations (Def 4.24).

.. coq::
   :name: substeq
|*)
  Definition substeq {Γ} Δ (a b : conf Γ) : Prop
    := forall γ : Γ =[val]> Δ, evalₒ (a ₜ⊛ γ) ≈ evalₒ (b ₜ⊛ γ).
  Notation "x ≈⟦sub Δ ⟧≈ y" := (substeq Δ x y) (at level 50).
(*|
We define an intermediate notion of equivalence, stating that for any assignment ``γ``,
the induced LTS are bisimilar when composed with the passive interpretation of ``γ``.
|*)
  Definition barb {Γ} Δ (x y : conf Γ) : Prop
    := forall γ : Γ =[val]> Δ,
         (inj_init_act Δ x ∥ inj_init_pas γ)
       ≈ (inj_init_act Δ y ∥ inj_init_pas γ).
  Notation "x ≈⟦barb Δ ⟧≈ y" := (barb Δ x y) (at level 50).
(*|
Barbed equivalence is sound w.r.t. substitution equivalence, by swapping the naive
composition with the guarded one and then applying adequacy.
|*)
  Theorem barb_correction {Γ} Δ (x y : conf Γ) : x ≈⟦barb Δ ⟧≈ y -> x ≈⟦sub Δ ⟧≈ y.
  Proof.
    intros H e.
    rewrite (it_eq_wbisim _ _ _ (adequacy x e)), (it_eq_wbisim _ _ _ (adequacy y e)).
    unfold compo_ev_guarded; rewrite 2 iter_evg_iter; apply H.
  Qed.
(*|
Our main theorem: bisimilarity of induced OGS machine strategies is sound w.r.t.
substitution equivalence, by applying barbed equivalence soundness, swapping the naive
composition with the `opaque one <Congruence.html>`_ and then applying congruence.

.. coq::
   :name: soundness
|*)
  Theorem ogs_correction {Γ} Δ (x y : conf Γ) : x ≈⟦ogs Δ ⟧≈ y -> x ≈⟦sub Δ ⟧≈ y.
  Proof.
    intro H; apply barb_correction.
    intro e; unfold compo.
    rewrite <- 2 (compo_compo_alt (x := RedT _ _)).
    apply compo_alt_proper; [ exact H | intro; reflexivity ].
  Qed.
End with_param.
(*|
If you wish to double check these results you can run the following commands at
this point in the file:

.. coq::

   About ogs_correction.
   Print Assumptions ogs_correction.

The first command will explicit the assumptions of the theorem, which we show how
to provide with several examples:

- `simply-typed call-by-value λ-calculus <STLC_CBV.html>`_
- `untyped pure call-by-value λ-calculus <ULC_CBV.html>`_
- `call-by-value System L <SystemL_CBV.html>`_
- `polarized System D <SystemD.html>`_

The second command will explicit if any axiom has been used to establish the
result. As stated in the `prelude <Prelude.html>`_, we exclusively use
:coqid:`Coq.Eqdep.Eq_rect_eq.eq_rect_eq`, ie Streicher's axiom K.
|*)
