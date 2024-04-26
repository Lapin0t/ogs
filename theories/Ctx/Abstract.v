From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.

#[global] Declare Scope ctx_scope.
#[global] Delimit Scope ctx_scope with ctx.
#[local] Open Scope ctx_scope.

Reserved Notation "∅".
Reserved Notation "Γ +▶ Δ" (at level 50, left associativity).
Reserved Notation "Γ ∋ x" (at level 60).
Reserved Notation "[ x ]".

Class context (T C : Type) := {
  c_emp : C ;
  c_cat : C -> C -> C ;
  c_var : C -> T -> Type ;
}.
#[global] Notation "∅" := c_emp : ctx_scope.
#[global] Notation "Γ +▶ Δ" := (c_cat Γ Δ) : ctx_scope.
#[global] Notation "Γ ∋ t" := (c_var Γ%ctx t).

Class context_cat_wkn (T C : Type) {CC : context T C} := {
  r_cat_l {Γ Δ} [t] : Γ ∋ t -> Γ +▶ Δ ∋ t ;
  r_cat_r {Γ Δ} [t] : Δ ∋ t -> Γ +▶ Δ ∋ t ;
}.

Section with_param.
  Context `{C : context_cat_wkn X T}.

  Variant c_emp_view t : ∅ ∋ t -> Type := .
  Derive NoConfusion NoConfusionHom for c_emp_view.

  Variant c_cat_view Γ Δ t : Γ +▶ Δ ∋ t -> Type :=
  | Vcat_l (i : Γ ∋ t) : c_cat_view Γ Δ t (r_cat_l i)
  | Vcat_r (j : Δ ∋ t) : c_cat_view Γ Δ t (r_cat_r j)
  .
  #[global] Arguments Vcat_l {Γ Δ t} i.
  #[global] Arguments Vcat_r {Γ Δ t} j.
  Derive NoConfusion for c_cat_view.
End with_param.

Class context_laws T C {CC : context T C} := {
  c_var_cat :: context_cat_wkn T C ;
  c_view_emp {t} i : c_emp_view t i ;
  c_view_cat {Γ Δ t} i : c_cat_view Γ Δ t i ;
  r_cat_l_inj {t Γ Δ} : injective (@r_cat_l _ _ _ _ Γ Δ t) ;
  r_cat_r_inj {t Γ Δ} : injective (@r_cat_r _ _ _ _ Γ Δ t) ;
  r_cat_disj {t Γ Δ} (i : Γ ∋ t) (j : Δ ∋ t) : ¬ (r_cat_l i = r_cat_r j) ;
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
