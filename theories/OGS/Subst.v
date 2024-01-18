From OGS Require Import Prelude.
From OGS.Utils Require Import Ctx Rel.
From OGS.Game Require Import HalfGame Event.

Open Scope ctx_scope.

Class baseT : Type :=
  { typ : Type }.

Class baseV `{baseT} : Type :=
  { val : Famₛ typ }.

Class baseC `{baseT} : Type :=
  { conf : Fam typ }.

Section withFam.
  Context {bT : baseT}.
  Context {bV : baseV}.
  Context {bC : baseC}.

(*|
Substitution Monoid (§ 5.3)
===========================

The specification of an evaluator will be separated in several steps. First we will ask for a family of values,
ie objects that can be substituted for variables. We formalize well-typed well-scoped substitutions in the
monoidal style of Fiore et al and Allais et al.
|*)
  Class subst_monoid : Type := {
      v_var {Γ} : Γ =[val]> Γ ; (* Γ ∋ x -> val Γ x *)
      v_sub {Γ Δ} : Γ =[val]> Δ -> val Γ ⇒ᵢ val Δ ;
    }.

  Notation "u ⊛ᵥ v" := (v_sub u _ v) (at level 30).
  Notation "Γ ⇒ᵥ Δ" := (Γ =[val]> Δ) (at level 30).

  Context {VM : subst_monoid}.

  Definition e_comp {Γ1 Γ2 Γ3} : Γ2 ⇒ᵥ Γ3 -> Γ1 ⇒ᵥ Γ2 -> Γ1 ⇒ᵥ Γ3
    := fun u v => s_map (v_sub u) v.
  Infix "⊛" := e_comp (at level 14).

(*|
The laws for monoids and modules are pretty straitforward.
A specificity is that assignments are represented
by functions from variables to values, as such their well-behaved equality is
|*)
  Class subst_monoid_laws : Prop :=
    {
      v_sub_proper {Γ Δ} ::
        Proper (ass_eq Γ Δ ==> forall_relation (fun i => eq ==> eq)) v_sub ;
      v_sub_var {Γ1 Γ2} (p : Γ1 ⇒ᵥ Γ2) : p ⊛ v_var ≡ₐ p ;
      v_var_sub {Γ1 Γ2} (p : Γ1 ⇒ᵥ Γ2) : v_var ⊛ p ≡ₐ p ;
      v_sub_sub {Γ1 Γ2 Γ3 Γ4} (p : Γ3 ⇒ᵥ Γ4) (q : Γ2 ⇒ᵥ Γ3) (r : Γ1 ⇒ᵥ Γ2) :
      p ⊛ (q ⊛ r) ≡ₐ (p ⊛ q) ⊛ r ;
    } .

(*|
Next we ask for a module over the monoid of values, to represent the configurations of the machine.
|*)
  Class subst_module : Type := {
      c_sub {Γ Δ} : Γ ⇒ᵥ Δ -> conf Γ -> conf Δ ;
    }.

  Notation "u ⊛ₜ c" := (c_sub u c) (at level 30).

  Class subst_module_laws {CM : subst_module} : Prop := {
    c_sub_proper {Γ Δ} :: Proper (ass_eq Γ Δ ==> eq ==> eq) c_sub ;
    c_var_sub {Γ} (c : conf Γ) : v_var ⊛ₜ c = c ;
    c_sub_sub {Γ1 Γ2 Γ3} (u : Γ2 ⇒ᵥ Γ3) (v : Γ1 ⇒ᵥ Γ2) {c}
      : u ⊛ₜ (v ⊛ₜ c) = (u ⊛ v) ⊛ₜ c ;
  } .

(*|
Additional assumptions on how variables behave.
|*)
  Definition is_var {Γ x} (v : val Γ x) : Type := { i : Γ ∋ x & v = v_var x i } .
  Definition is_var_get {Γ x} {v : val Γ x} (p : is_var v) : Γ ∋ x := projT1 p .
  Definition is_var_get_eq {Γ x} {v : val Γ x} (p : is_var v) : v = v_var x (is_var_get p) := projT2 p .

  Context {CM : subst_module}.

(*|
Derived notions: renamings.
|*)
  Definition v_ren {Γ Δ} : Γ ⊆ Δ -> val Γ ⇒ᵢ val Δ :=
    fun u => v_sub (v_var ⊛ᵣ u) .
  Notation "r ᵣ⊛ᵥ v" := (v_ren r _ v) (at level 14).

  Definition e_ren {Γ1 Γ2 Γ3} : Γ2 ⊆ Γ3 -> Γ1 ⇒ᵥ Γ2 -> Γ1 ⇒ᵥ Γ3
    := fun u v => (v_var ⊛ᵣ u) ⊛ v.
  Infix "ᵣ⊛" := e_ren (at level 14).

  Definition c_ren {Γ1 Γ2} : Γ1 ⊆ Γ2 -> conf Γ1 -> conf Γ2
    := fun u c => (v_var ⊛ᵣ u) ⊛ₜ c .
  Infix "ᵣ⊛ₜ" := c_ren (at level 14).

  Class var_assumptions : Type := {
    v_var_inj {Γ x} (i j : Γ ∋ x) : v_var x i = v_var x j -> i = j ;
    is_var_dec {Γ x} (v : val Γ x) : is_var v + (is_var v -> False) ;
    is_var_ren {Γ1 Γ2 x} (v : val Γ1 x) (e : Γ1 ⊆ Γ2) : is_var (e ᵣ⊛ᵥ v) -> is_var v ;
  }.

  Context {sVL: subst_monoid_laws}.
  Context {sCL: subst_module_laws}.
  Context {VA : var_assumptions} .

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

Arguments subst_monoid {_} _.
Arguments subst_module {_} _ _.
Notation "u ⊛ᵥ v" := (v_sub u _ v) (at level 30).
Notation "Γ ⇒ᵥ Δ" := (Γ =[val]> Δ) (at level 30).
Notation "u ⊛ₜ c" := (c_sub u c) (at level 30).
Infix "⊛" := e_comp (at level 14).
Notation "r ᵣ⊛ᵥ v" := (v_ren r _ v) (at level 14).
Infix "ᵣ⊛" := e_ren (at level 14).
Infix "ᵣ⊛ₜ" := c_ren (at level 14).

