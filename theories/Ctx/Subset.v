From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.
From OGS.Ctx Require Import Abstract Family.

#[local] Open Scope ctx_scope.

Reserved Notation "∅ₛ".
Reserved Notation "Γ +▶ₛ Δ" (at level 40).

Section with_param.
  Context {T C} {CC : context T C} {CL : context_laws T C} {P : T -> SProp}.

  Definition allS (Γ : C) : SProp := forall x, Γ ∋ x -> P x.
  Definition ctxS : Type := sigS allS.
  Definition coe_ctxS : ctxS -> C := sub_elt.

  Definition varS (Γ : ctxS) (x : T) := Γ.(sub_elt) ∋ x.

  Program Definition nilS : ctxS := {| sub_elt := ∅ |}.
  Next Obligation. intros ? i; destruct (c_view_emp i). Qed.

  Program Definition catS (Γ Δ : ctxS) : ctxS :=
    {| sub_elt := Γ.(sub_elt) +▶ Δ.(sub_elt) |}.
  Next Obligation.
    intros ? i; destruct (c_view_cat i).
    now apply Γ.(sub_prf).
    now apply Δ.(sub_prf).
  Qed.

  #[global] Instance subset_context : context T ctxS :=
    {| c_emp := nilS ;
       c_cat := catS ;
       c_var := varS |}.

  #[global] Instance subset_context_cat_wkn : context_cat_wkn T ctxS :=
    {| r_cat_l Γ Δ t i := @r_cat_l T C _ _ Γ.(sub_elt) Δ.(sub_elt) t i ;
       r_cat_r Γ Δ t i := @r_cat_r T C _ _ Γ.(sub_elt) Δ.(sub_elt) t i |} .

  #[global] Instance subset_context_laws : context_laws T ctxS.
  Proof.
    unshelve esplit; cbn.
    - intros ? i; destruct (c_view_emp i).
    - intros ??? i; destruct (c_view_cat i).
      refine (Vcat_l _).
      refine (Vcat_r _).
    - intros ????? H; exact (r_cat_l_inj _ _ H).
    - intros ????? H; exact (r_cat_r_inj _ _ H).
    - intros ????? H; exact (r_cat_disj _ _ H).
  Qed.

  Definition s_elt_upg {Γ : ctxS} {x} (i : Γ.(sub_elt) ∋ x) : sigS P :=
    {| sub_prf := Γ.(sub_prf) x i |}.

  Definition s_var_upg {Γ : ctxS} {x : T} (i : Γ.(sub_elt) ∋ x)
    : Γ ∋ (s_elt_upg i).(sub_elt) := i.
End with_param.

#[global] Arguments ctxS T C {CC} P.
#[global] Arguments allS {T C CC} P Γ.

#[global] Notation "∅ₛ" := (nilS) : ctx_scope.
#[global] Notation "Γ +▶ₛ Δ" := (catS Γ Δ) : ctx_scope.
