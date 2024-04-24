(*|
Substitution (§ 4.3)
=====================
|*)
From OGS Require Import Prelude.
From OGS.Utils Require Import Ctx Psh Rel.

Open Scope ctx_scope.

(*|
Substitution Monoid (Def. 4.9)
==============================

The specification of an evaluator will be separated in several steps. First we will ask for a family of values,
i.e. objects that can be substituted for variables. We formalize well-typed well-scoped substitutions in the
monoidal style of Fiore et al and Allais et al.
|*)

Class subst_monoid {T} (val : Famₛ T) : Type := {
  v_var {Γ} : Γ =[val]> Γ ; (* Γ ∋ x -> val Γ x *)
  v_sub {Γ Δ} : Γ =[val]> Δ -> val Γ ⇒ᵢ val Δ ;
}.
#[global] Notation "u ⊛ᵥ v" := (v_sub u _ v) (at level 30).

Definition e_comp {T val} {_ : @subst_monoid T val} {Γ1 Γ2 Γ3}
  : Γ2 =[val]> Γ3 -> Γ1 =[val]> Γ2 -> Γ1 =[val]> Γ3
  := fun u v => s_map (v_sub u) v.
#[global] Infix "⊛" := e_comp (at level 14).

(*|
The laws for monoids and modules are pretty straitforward. A specificity is that
assignments are represented by functions from variables to values, as such their
well-behaved equality is pointwise equality and we require substitution to respect it.
|*)

Class subst_monoid_laws {T} (val : Famₛ T) {VM : subst_monoid val} : Prop := {
  v_sub_proper {Γ Δ}
    :: Proper (ass_eq Γ Δ ==> forall_relation (fun _ => eq ==> eq)) v_sub ;
  v_sub_var {Γ1 Γ2} (p : Γ1 =[val]> Γ2)
    : p ⊛ v_var ≡ₐ p ;
  v_var_sub {Γ1 Γ2} (p : Γ1 =[val]> Γ2)
    : v_var ⊛ p ≡ₐ p ;
  v_sub_sub {Γ1 Γ2 Γ3 Γ4} (p : Γ3 =[val]> Γ4) (q : Γ2 =[val]> Γ3) (r : Γ1 =[val]> Γ2)
   : p ⊛ (q ⊛ r) ≡ₐ (p ⊛ q) ⊛ r ;
} .

(*|
Substitution Module (Def. 4.11)
===============================

Next, we ask for a module over the monoid of values, to represent the configurations
of the machine.
|*)

Class subst_module {T} (val : Famₛ T) (conf : Fam T) : Type := {
  c_sub {Γ Δ} : Γ =[val]> Δ -> conf Γ -> conf Δ ;
}.

#[global] Notation "u ⊛ₜ c" := (c_sub u c) (at level 30).

Class subst_module_laws {T} (val : Famₛ T) (conf : Fam T)
      {VM : subst_monoid val} {CM : subst_module val conf} : Prop := {
  c_sub_proper {Γ Δ} :: Proper (ass_eq Γ Δ ==> eq ==> eq) c_sub ;
  c_var_sub {Γ} (c : conf Γ) : v_var ⊛ₜ c = c ;
  c_sub_sub {Γ1 Γ2 Γ3} (u : Γ2 =[val]> Γ3) (v : Γ1 =[val]> Γ2) {c}
    : u ⊛ₜ (v ⊛ₜ c) = (u ⊛ v) ⊛ₜ c ;
} .

(*|
Derived notions: renamings.
|*)

Section renaming.
  Context {T : Type} {val : Famₛ T} {conf : Fam T}.
  Context {VM : subst_monoid val} {VML : subst_monoid_laws val}.
  Context {CM : subst_module val conf} {CML : subst_module_laws val conf}.

  Definition v_ren {Γ Δ} : Γ ⊆ Δ -> val Γ ⇒ᵢ val Δ :=
    fun u => v_sub (v_var ⊛ᵣ u) .

  Definition e_ren {Γ1 Γ2 Γ3} : Γ2 ⊆ Γ3 -> Γ1 =[val]> Γ2 -> Γ1 =[val]> Γ3
    := fun u v => (v_var ⊛ᵣ u) ⊛ v.

  Definition c_ren {Γ1 Γ2} : Γ1 ⊆ Γ2 -> conf Γ1 -> conf Γ2
    := fun u c => (v_var ⊛ᵣ u) ⊛ₜ c .
End renaming.
#[global] Notation "r ᵣ⊛ᵥ v" := (v_ren r _ v) (at level 14).
#[global] Infix "ᵣ⊛" := e_ren (at level 14).
#[global] Infix "ᵣ⊛ₜ" := c_ren (at level 14).

(*|
Additional assumptions on how variables behave. We basically ask that the identity
assignment is injective, that being in its image is stable by renaming and that its
image is decidable.
|*)

Variant is_var {T} {val : Famₛ T} {VM : subst_monoid val} {Γ x} : val Γ x -> Type :=
| IsVar (i : Γ ∋ x) : is_var (v_var x i)
.
Derive NoConfusion for is_var.

Class var_assumptions {T} (val : Famₛ T) {VM : subst_monoid val} : Type := {
  v_var_inj {Γ x} (i j : Γ ∋ x) : v_var x i = v_var x j -> i = j ;
  is_var_dec {Γ x} (v : val Γ x) : is_var v + (is_var v -> False) ;
  is_var_ren {Γ1 Γ2 x} (v : val Γ1 x) (e : Γ1 ⊆ Γ2) : is_var (e ᵣ⊛ᵥ v) -> is_var v ;
}.

Section variables.
  Context {T : Type} (val : Famₛ T).
  Context {VM : subst_monoid val} {VML : subst_monoid_laws val}.
  Context {VA : var_assumptions val}.

  Lemma is_var_irr {Γ x} {v : val Γ x} (p q : is_var v) : p = q.
  Proof.
    refine (match p as i in is_var v
            return forall w (H : w = v) (q : is_var w), i = rew [is_var] H in q
            with IsVar i => fun w H q => _
            end v eq_refl q).
    dependent elimination q.
    pose proof (v_var_inj _ _ H) as H'.
    now dependent elimination H'; dependent elimination H.
  Qed.

  Lemma ren_is_var {Γ1 Γ2 x} (v : val Γ1 x) (e : Γ1 ⊆ Γ2) : is_var v -> is_var (e ᵣ⊛ᵥ v).
  Proof.
    intro p; dependent elimination p.
    pose proof (v_sub_var (v_var ⊛ᵣ e) _ i) as H.
    unfold v_ren, e_comp, s_map in *.
    rewrite H; econstructor.
  Qed.
End variables.

(*|
A couple derived properties on the constructed operations.
|*)

Section properties.
  Context {T : Type} (val : Famₛ T).
  Context {VM : subst_monoid val} {VML : subst_monoid_laws val}.

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

  Lemma e_comp_ren_r {Γ1 Γ2 Γ3 Γ4} (u : Γ3 =[val]> Γ4) (v : Γ2 =[val]> Γ3) (w : Γ1 ⊆ Γ2)
    : u ⊛ (v ⊛ᵣ w) ≡ₐ (u ⊛ v) ⊛ᵣ w.
  Proof.
    reflexivity.
  Qed.

  Lemma e_comp_ren_l {Γ1 Γ2 Γ3 Γ4} (u : Γ3 =[val]> Γ4) (v : Γ2 ⊆ Γ3) (w : Γ1 =[val]> Γ2)
        : (u ⊛ᵣ v) ⊛ w ≡ₐ u ⊛ (v ᵣ⊛ w).
  Proof.
    unfold e_ren; now rewrite v_sub_sub, e_comp_ren_r, v_sub_var.
  Qed.

  Lemma v_sub_comp {Γ1 Γ2 Γ3} (u : Γ2 =[val]> Γ3) (v : Γ1 =[val]> Γ2) {x} (w : val Γ1 x) :
    u ⊛ᵥ (v ⊛ᵥ w) = (u ⊛ v) ⊛ᵥ w.
  Proof.
    pose (w' := a_append a_empty w : (∅ ▶ x) =[val]> Γ1).
    change w with (w' _ Ctx.top).
    do 2 change (?u ⊛ᵥ ?v _ Ctx.top) with ((u ⊛ v) _ Ctx.top).
    apply v_sub_sub.
  Qed.

  Lemma v_sub_id {Γ1 Γ2} (u : Γ1 =[val]> Γ2) {x} (i : Γ1 ∋ x) : u ⊛ᵥ (v_var x i) = u x i .
  Proof.
    apply v_sub_var.
  Qed.
End properties.
