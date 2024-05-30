From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.
From OGS.Ctx Require Import All DirectSum Ctx.
From OGS.OGS Require Import Subst.

Open Scope ctx_scope.

(* hole and composition of contexts *)
Class fill_monoid `{CC : context T C} (ectx : Fam₂ T C) := {
  e_hole {Γ τ} : ectx Γ τ τ ;
  e_fill {Γ τ1 τ2 τ3} : ectx Γ τ2 τ3 -> ectx Γ τ1 τ2 -> ectx Γ τ1 τ3 ;
}.

#[global] Notation "∙" := e_hole.
#[global] Notation "E @ₑ F" := (e_fill E F) (at level 20).

Class fill_monoid_laws `{CC : context T C} (ectx : Fam₂ T C) {EM : fill_monoid ectx} := {
  e_hole_fill {Γ τ1 τ2} (e : ectx Γ τ1 τ2) : ∙ @ₑ e = e ;
  e_fill_hole {Γ τ1 τ2} (e : ectx Γ τ1 τ2) : e @ₑ ∙ = e ;
  e_fill_fill {Γ τ1 τ2 τ3 τ4}  (E1 : ectx Γ τ1 τ2) (E2 : ectx Γ τ2 τ3) (E3 : ectx Γ τ3 τ4)
    : E3 @ₑ (E2 @ₑ E1) = (E3 @ₑ E2) @ₑ E1 ;
}.

(* substitution of a Fam₂-shaped family by values *)
Class subst_module2 `{CC : context T C} (val : Fam₁ T C) (ectx : Fam₂ T C) := {
  e_sub : ectx ⇒₂ ⟦ val , ectx ⟧₂ ;
}.
#[global] Arguments e_sub {T C CC val ectx _} [Γ x y] E {Δ} a : rename.
#[global] Notation "E ₑ⊛ a" := (e_sub E a%asgn) (at level 30).

Class subst_module2_laws `{CC : context T C} (val : Fam₁ T C) (ectx : Fam₂ T C)
      {VM : subst_monoid val} {ESM : subst_module2 val ectx} := {
  e_sub_proper :: Proper (∀ₕ Γ, ∀ₕ _, ∀ₕ _, eq ==> ∀ₕ Δ, asgn_eq Γ Δ ==> eq) e_sub ;
  e_sub_id {Γ τ1 τ2} (E : ectx Γ τ1 τ2) : E ₑ⊛ a_id = E;
  e_sub_comp {τ1 τ2 Γ1 Γ2 Γ3} (E : ectx Γ1 τ1 τ2) (u : Γ1 =[val]> Γ2) (v : Γ2 =[val]> Γ3)
    : E ₑ⊛ (u ⊛ v) = (E ₑ⊛ u) ₑ⊛ v ;
}.
#[global] Instance e_sub_proper_a `{subst_module2_laws T C val ectx}
          {Γ1 Γ2 x y} {E : ectx Γ1 x y} : Proper (asgn_eq Γ1 Γ2 ==> eq) (e_sub E).
Proof. now apply e_sub_proper. Qed.

(* filling a context with a term *)
Class fill_module `{CC : context T C} (ectx : Fam₂ T C) (term : Fam₁ T C) := {
  t_fill {Γ τ1 τ2} : ectx Γ τ1 τ2 -> term Γ τ1 -> term Γ τ2
}.
#[global] Notation "E @ₜ t" := (t_fill E t) (at level 20).

Class fill_module_laws `{CC : context T C} (ectx : Fam₂ T C) (term : Fam₁ T C)
      {EFM : fill_monoid ectx} {TFM : fill_module ectx term} := {
  t_fill_id {Γ τ1} (t : term Γ τ1) : ∙ @ₜ t = t ;
  t_fill_comp  {Γ τ1 τ2 τ3} (E1 : ectx Γ τ1 τ2) (E2 : ectx Γ τ2 τ3) (t : term Γ τ1)
    : E2 @ₜ (E1 @ₜ t) = (E2 @ₑ E1) @ₜ t ;
}.

(* substituting a Famₛ-shaped family *)
Class subst_module1 `{CC : context T C} (val term : Fam₁ T C) := {
  t_sub : term ⇒₁ ⟦ val , term ⟧₁ ;
}.
#[global] Arguments t_sub {T C CC val term _} [Γ x] t {Δ} a : rename.
#[global] Notation "t ₜ⊛ a" := (t_sub t a%asgn) (at level 30).

Class subst_module1_laws `{CC : context T C} (val term : Fam₁ T C)
      {VM : subst_monoid val} {TSM : subst_module1 val term} := {
  t_sub_proper :: Proper (∀ₕ Γ, ∀ₕ _, eq ==> ∀ₕ Δ, asgn_eq Γ Δ ==> eq) t_sub ;
  t_sub_id {Γ τ} (t : term Γ τ) : t ₜ⊛ a_id = t ;
  t_sub_sub {Γ1 Γ2 Γ3 τ} (t : term Γ1 τ) (u : Γ1 =[val]> Γ2) (v : Γ2 =[val]> Γ3)
    : t ₜ⊛ (u ⊛ v) = (t ₜ⊛ u) ₜ⊛ v ;
} .
#[global] Instance t_sub_proper_a `{subst_module1_laws T C val term}
          {Γ1 Γ2 x} {t : term Γ1 x} : Proper (asgn_eq Γ1 Γ2 ==> eq) (t_sub t).
Proof. now apply t_sub_proper. Qed.

(* all the laws for a fill-monoid that can also be substituted *)
Class fill_monoid_subst_module2_coh `{CC : context T C} (val : Fam₁ T C) (ectx : Fam₂ T C)
      {VM : subst_monoid val} {EFM : fill_monoid ectx} {ESM : subst_module2 val ectx} := {
  fsmon_fill_monoid_laws :: fill_monoid_laws ectx ;
  fsmon_subst_module2_laws :: subst_module2_laws val ectx ;
  e_sub_hole {Γ Δ τ} (u : Γ =[val]> Δ) : ∙ ₑ⊛ u = (∙ : ectx _ τ τ) ;
  e_sub_fill {Γ Δ τ1 τ2 τ3} (E1 : ectx Γ τ1 τ2) (E2 : ectx Γ τ2 τ3) (u : Γ =[val]> Δ)
    : (E2 @ₑ E1) ₑ⊛ u = (E2 ₑ⊛ u) @ₑ (E1 ₑ⊛ u);
}.

(* all the laws for a fill-module that can also be substituted *)
Class fill_module_subst_module1_coh `{CC : context T C}
      (val : Fam₁ T C) (ectx : Fam₂ T C) (term : Fam₁ T C)
      {VM : subst_monoid val} {EFM : fill_monoid ectx} {ESM : subst_module2 val ectx}
      {TVM : subst_module1 val term} {TFM : fill_module ectx term} := {
  fsmod_fill_module_laws :: fill_module_laws ectx term ;
  fsmod_subst_module1_laws :: subst_module1_laws val term ;
  t_sub_fill {Γ Δ τ1 τ2} (E : ectx Γ τ1 τ2) (t : term  Γ τ1) (u : Γ =[val]> Δ)
    : (E @ₜ t) ₜ⊛ u = (E ₑ⊛ u) @ₜ (t ₜ⊛ u) ;
}.

Section translation.
  Context `{CC : context T C} {val : Fam₁ T C} {ectx : Fam₂ T C} {term : Fam₁ T C}.
  Context {VM : subst_monoid val} {VML : subst_monoid_laws val}.
  Context {EFM : fill_monoid ectx} {ESM : subst_module2 val ectx}
          {EML : fill_monoid_subst_module2_coh val ectx}.
  Context {TFM : fill_module ectx term} {TSM : subst_module1 val term}
          {TML : fill_module_subst_module1_coh val ectx term}.

  Notation ictx := (dsum C C).
  Notation ityp := (T + T)%type.
  Notation "⌊ x ⌋" := (inl x) (at level 5).
  Notation "¬ x" := (inr x) (at level 5).

  Notation "ᵥ↓ Γ" := (fst Γ) (at level 5).
  Notation "ₖ↓ Γ" := (snd Γ) (at level 5).

  Record f_named (F : Fam₁ T C) (Γ : ictx) := Named {
    n_ty : T ;
    n_kvar : ₖ↓Γ ∋ n_ty ;
    n_elt : F ᵥ↓Γ n_ty ;
  }.
  #[global] Arguments Named {F Γ σ} i t : rename.
  #[global] Arguments n_ty {F Γ}.
  #[global] Arguments n_kvar {F Γ}.
  #[global] Arguments n_elt {F Γ}.
  Notation "⦅ i ⦆ x" := (Named i x) (at level 40).

  Definition iectx : ictx -> T -> Type
    := fun Γ τ => f_named (fun Δ σ => ectx Δ τ σ) Γ .

  Definition iterm : ictx -> Type
    := f_named term .

  Equations ival : Fam₁ ityp ictx :=
    ival Γ ⌊τ⌋ := val ᵥ↓Γ τ ;
    ival Γ ¬τ  := iectx Γ τ .

  Definition a_down {Γ Δ} (u : Γ =[ival]> Δ) : ᵥ↓Γ =[val]> ᵥ↓Δ :=
    fun σ i => u ⌊σ⌋ i.
  Notation "ₐ↓ u" := (a_down u) (at level 20).
  Arguments a_down {_ _} _ _ /.

  #[export] Instance a_down_proper {Γ Δ} : Proper (asgn_eq Γ Δ ==> asgn_eq _ _) a_down.
  Proof. intros ?? Hu ? i; exact (Hu ⌊_⌋ i). Qed.

  Equations ival_var {Γ} σ : Γ ∋ σ -> ival Γ σ :=
    ival_var ⌊σ⌋ i := v_var (i : ᵥ↓Γ ∋ _) ;
    ival_var ¬σ  i := ⦅i⦆ ∙ .

  Equations ival_sub {Γ} σ (v : ival Γ σ) {Δ} (γ : Γ =[ival]> Δ) : ival Δ σ :=
    ival_sub ⌊σ⌋ v  γ := (v : val _ _) ᵥ⊛ ₐ↓γ ;
    ival_sub ¬σ  iE γ :=
      let jF := γ (¬ _) iE.(n_kvar) in
      ⦅jF.(n_kvar)⦆ (jF.(n_elt) @ₑ (iE.(n_elt) ₑ⊛ ₐ↓γ)) .

  Definition iterm_sub {Γ} (c : iterm Γ) {Δ} (γ : Γ =[ival]> Δ) : iterm Δ :=
      let iE := γ (¬ _) c.(n_kvar) in
      ⦅iE.(n_kvar)⦆ (iE.(n_elt) @ₜ (c.(n_elt) ₜ⊛ ₐ↓γ)) .

  #[global] Instance ival_monoid : subst_monoid ival :=
    {| v_var := @ival_var ; v_sub := @ival_sub |}.

  #[global] Instance iterm_module : subst_module ival iterm :=
    {| c_sub := @iterm_sub |}.

  #[global] Instance ival_sub_proper
            : Proper (∀ₕ Γ, ∀ₕ _, eq ==> ∀ₕ Δ, asgn_eq Γ Δ ==> eq) (@ival_sub) .
  Proof.
    intros ? [] ?? <- ??? Hu; cbn.
    - apply v_sub_proper_a; eauto; now rewrite Hu.
    - rewrite (Hu (¬_) (n_kvar x)); do 2 f_equal.
      apply e_sub_proper_a; eauto; now rewrite Hu.
  Qed.

  #[global] Instance iterm_sub_proper
            : Proper (∀ₕ Γ, eq ==> ∀ₕ Δ, asgn_eq Γ Δ ==> eq) (@iterm_sub) .
  Proof.
    intros ? [ τ α t ] ? <- ??? Hu; unfold iterm_sub; cbn.
    rewrite (Hu (¬_) α); do 2 f_equal.
    now rewrite Hu.
  Qed.

  (* .. et puis la première loi. L'idée c'est de faire des lemmes pour chacun des champs
     de `subst_monoid_laws ival` et `subst_module_laws ival iterm`. *)
  Lemma ival_sub_var {Γ1 Γ2} (p : Γ1 =[ival]> Γ2) : p ⊛ ival_var ≡ₐ p .
  Proof.
    intros [] i; cbn.
    - change (ₐ↓ ival_var) with (a_id (Γ:=ᵥ↓Γ2)).
      now rewrite v_var_sub.
    - change (ₐ↓ ival_var) with (a_id (Γ:=ᵥ↓Γ2)).
      now rewrite e_hole_fill, e_sub_id.
  Qed.

  Lemma ciu_is_subst_eq {Δ y Γ x} (a b : term Γ x)
        : (forall (e : ectx Δ x y) (γ : Γ =[val]> Δ), )
End translation.
