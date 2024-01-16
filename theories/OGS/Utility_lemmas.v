From OGS Require Import Prelude.
From OGS.Utils Require Import Ctx Rel.
From OGS.Game Require Import HalfGame Event.
From OGS.OGS Require Import Subst Obs Machine.
From OGS.ITree Require Import ITree Eq Delay Structure Properties Guarded.

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

  Lemma is_var_irr {Γ x} {v : val Γ x} (p q : is_var v) : p = q.
  Proof.
    destruct p as [i1 e1], q as [i2 e2].
    destruct (v_var_inj _ _ (eq_trans (eq_sym e1) e2)).
    f_equal; apply YesUIP.
  Qed.

  Definition ren_is_var {Γ1 Γ2 x} (v : val Γ1 x) (e : Γ1 ⊆ Γ2) : is_var v -> is_var (e ᵣ⊛ᵥ v).
  Proof.
    intro p.
    refine (e _ (is_var_get p) ,' _).
    pose (i := is_var_get p); eassert (H : _) by exact (is_var_get_eq p); fold i in H |- *.
    rewrite H; change (e ᵣ⊛ᵥ v_var x i) with ((e ᵣ⊛ v_var) x i).
    unfold e_ren; rewrite v_sub_var; reflexivity.
  Defined.

  Variant is_var_ren_view {Γ1 Γ2 x} (v : val Γ1 x) (e : Γ1 ⊆ Γ2) : is_var (e ᵣ⊛ᵥ v) -> Type :=
    | IsVarRen (p : is_var v) : is_var_ren_view v e (ren_is_var v e p)
  .
  Arguments IsVarRen {Γ1 Γ2 x v e}.

  Lemma view_is_var_ren {Γ1 Γ2 x} (v : val Γ1 x) (e : Γ1 ⊆ Γ2) (p : is_var (e ᵣ⊛ᵥ v)) : is_var_ren_view v e p.
    rewrite (is_var_irr p (ren_is_var v e (is_var_ren v e p))); econstructor.
  Qed.


(*|
A couple derived properties on the constructed operations.
|*)

  #[global] Instance e_comp_proper {Γ1 Γ2 Γ3} :
    Proper (ass_eq Γ2 Γ3 ==> ass_eq Γ1 Γ2 ==> ass_eq Γ1 Γ3) e_comp.
  Proof.
    intros ? ? H1 ? ? H2 ? i; unfold e_comp, s_map.
    now rewrite H1, H2.
  Qed.

  #[global] Instance e_ren_proper {Γ1 Γ2 Γ3} :
    Proper (ass_eq Γ2 Γ3 ==> ass_eq Γ1 Γ2 ==> ass_eq Γ1 Γ3) e_ren.
  Proof.
    intros ? ? H1 ? ? H2; unfold e_ren.
    apply e_comp_proper; eauto; now rewrite H1.
  Qed.

  Lemma e_comp_ren_r {Γ1 Γ2 Γ3 Γ4} (u : Γ3 ⇒ᵥ Γ4) (v : Γ2 ⇒ᵥ Γ3) (w : Γ1 ⊆ Γ2)
    : u ⊛ (v ⊛ᵣ w) ≡ₐ (u ⊛ v) ⊛ᵣ w.
  Proof.
    reflexivity.
  Qed.

  Lemma e_comp_ren_l {Γ1 Γ2 Γ3 Γ4} (u : Γ3 ⇒ᵥ Γ4) (v : Γ2 ⊆ Γ3) (w : Γ1 ⇒ᵥ Γ2)
        : (u ⊛ᵣ v) ⊛ w ≡ₐ u ⊛ (v ᵣ⊛ w).
  Proof.
    unfold e_ren; now rewrite v_sub_sub, e_comp_ren_r, v_sub_var.
  Qed.

  Lemma v_sub_comp {Γ1 Γ2 Γ3} (u : Γ2 ⇒ᵥ Γ3) (v : Γ1 ⇒ᵥ Γ2) {x} (w : val Γ1 x) :
    u ⊛ᵥ (v ⊛ᵥ w) = (u ⊛ v) ⊛ᵥ w.
  Proof.
    pose (w' := a_append a_empty w : (∅ ▶ x) ⇒ᵥ Γ1).
    change w with (w' _ Ctx.top).
    do 2 change (?u ⊛ᵥ ?v _ Ctx.top) with ((u ⊛ v) _ Ctx.top).
    apply v_sub_sub.
  Qed.

  Lemma v_sub_id {Γ1 Γ2} (u : Γ1 ⇒ᵥ Γ2) {x} (i : Γ1 ∋ x) : u ⊛ᵥ (v_var x i) = u x i .
    apply v_sub_var.
  Qed.

End withFam.
