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
      v_sub_v_var {Γ1 Γ2} (p : Γ1 ⇒ᵥ Γ2) : p ⊛ v_var ≡ₐ p ;
      v_var_v_sub {Γ1 Γ2} (p : Γ1 ⇒ᵥ Γ2) : v_var ⊛ p ≡ₐ p ;
      v_sub_v_sub {Γ1 Γ2 Γ3 Γ4} (p : Γ3 ⇒ᵥ Γ4) (q : Γ2 ⇒ᵥ Γ3) (r : Γ1 ⇒ᵥ Γ2) :
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

End withFam.

Arguments subst_monoid {_} _.
Arguments subst_module {_} _ _.
Notation "u ⊛ᵥ v" := (v_sub u _ v) (at level 30).
Notation "Γ ⇒ᵥ Δ" := (Γ =[val]> Δ) (at level 30).
Notation "u ⊛ₜ c" := (c_sub u c) (at level 30).
Infix "⊛" := e_comp (at level 14).

