From OGS Require Import Prelude.
From OGS.Utils Require Import Family.

#[global] Declare Scope ctx_scope.
#[global] Delimit Scope ctx_scope with ctx.
#[local] Open Scope ctx_scope.

Reserved Notation "∅".
Reserved Notation "Γ +▶ Δ" (at level 50, left associativity).
Reserved Notation "Γ ∋ x" (at level 60).
Reserved Notation "[ x ]".

Class context (C : Type) (Xs : list Type) := {
  c_emp : C ;
  c_cat : C -> C -> C ;
  c_var : C -> Fam Xs ;
}.
#[global] Notation "∅" := c_emp : ctx_scope.
#[global] Notation "Γ +▶ Δ" := (c_cat Γ Δ) : ctx_scope.
#[global] Notation "Γ ∋ xs" := (c_var Γ%ctx @ᵢ xs).

Class context_cat_wkn C Xs {CC : context C Xs} := {
  r_cat_l {Γ Δ} : c_var Γ →ᵢ c_var (Γ +▶ Δ) ;
  r_cat_r {Γ Δ} : c_var Δ →ᵢ c_var (Γ +▶ Δ) ;
}.

Section with_param.
  Context `{CW : context_cat_wkn C Xs}.

  Variant c_emp_view xs : ∅ ∋ xs -> Type := .
  Derive NoConfusion NoConfusionHom for c_emp_view.

  Variant c_cat_view Γ Δ xs : (Γ +▶ Δ) ∋ xs -> Type :=
  | Vcat_l (i : Γ ∋ xs) : c_cat_view Γ Δ xs (r_cat_l $ᵢ i)
  | Vcat_r (j : Δ ∋ xs) : c_cat_view Γ Δ xs (r_cat_r $ᵢ j)
  .
  #[global] Arguments Vcat_l {Γ Δ xs} i.
  #[global] Arguments Vcat_r {Γ Δ xs} j.
  Derive NoConfusion for c_cat_view.
End with_param.

Class context_laws T C {CC : context T C} := {
  c_var_cat :: context_cat_wkn T C ;
  c_view_emp : ∀… xs, forall i, c_emp_view xs i ;
  c_view_cat {Γ Δ} : ∀… xs, forall i, c_cat_view Γ Δ xs i ;
  r_cat_l_inj {Γ Δ} : ∀… xs, injective (applyF (r_cat_l (Γ:=Γ) (Δ:=Δ)) (xs:=xs)) ;
  r_cat_r_inj {Γ Δ} : ∀… xs, injective (applyF (r_cat_r (Γ:=Γ) (Δ:=Δ)) (xs:=xs)) ;
  r_cat_disj {Γ Δ} : ∀… xs, forall (i : Γ ∋ xs) (j : Δ ∋ xs), ¬ (r_cat_l $ᵢ i = r_cat_r $ᵢ j)
} .

(*

Class monoid_laws T {M : monoid T} := {
  m_emp_cat {a} : ∅ +▶ a = a ; 
  m_cat_emp {a} : a +▶ ∅ = a ; 
  m_cat_cat {a b c} : (a +▶ b) +▶ c = (a +▶ b) +▶ c ; 
}.

Class context_over (X T : Type) := {
  m_sing : X -> T ;
}.
#[global] Notation "[ x ]" := (m_sing x) : ctx_scope.
Class context_over X T `{C : context X T} {MO : monoid_over X T} := {
  c_var_sing {x} : x ∈ [ x ] ;
}.
  Variant c_sing_view x : forall y, y ∈ [ x ] -> Type :=
  | Vsing : c_sing_view x x c_var_sing .
  #[global] Arguments Vsing {x}.

Class context_over_laws X T `{CO : context_over X T} := {
  c_view_sing {x y} i : c_sing_view x y i ;
}.
  Definition a_sing {F x Γ} (v : F x Γ) : [ x ] =[F]> Γ
    := fun x i => match c_view_sing i in c_sing_view _ x i return F x _
               with Vsing => v
               end.
*)
