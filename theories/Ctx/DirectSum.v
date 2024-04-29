From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.
From OGS.Ctx Require Import Abstract Family.

#[local] Open Scope ctx_scope.

Section with_param.
  Context {T1 C1 : Type} {CC1 : context T1 C1} {CL1 : context_laws T1 C1}.
  Context {T2 C2 : Type} {CC2 : context T2 C2} {CL2 : context_laws T2 C2}.

  Definition dsum := C1 × C2.
               
  Definition c_emp2 : dsum := (∅ , ∅) .

  Definition c_cat2 (Γ12 : dsum) (Δ12 : dsum) : dsum
    := (fst Γ12 +▶ fst Δ12 , snd Γ12 +▶ snd Δ12).

  Equations c_var2 : dsum -> T1 + T2 -> Type :=
   c_var2 Γ12 (inl t1) := fst Γ12 ∋ t1 ;
   c_var2 Γ12 (inr t2) := snd Γ12 ∋ t2 .

  #[global] Instance direct_sum_context : context (T1 + T2) dsum :=
    {| c_emp := c_emp2 ; c_cat := c_cat2 ; c_var := c_var2 |}.

  #[global] Instance direct_sum_cat_wkn : context_cat_wkn (T1 + T2) dsum .
  Proof.
    split.
    - intros ?? [ t1 | t2 ] i; cbn; now apply r_cat_l.
    - intros ?? [ t1 | t2 ] i; cbn; now apply r_cat_r.
  Defined.

  #[global] Instance direct_sum_laws : context_laws (T1 + T2) dsum .
  Proof.
    esplit; cbn.
    - intros [] i; cbn in i; now destruct (c_view_emp i).
    - intros ?? [] i; cbn in i; destruct (c_view_cat i).
      now refine (Vcat_l _).
      now refine (Vcat_r _).
      now refine (Vcat_l _).
      now refine (Vcat_r _).
    - intros ?? []; cbn; intros ?? H; now apply (r_cat_l_inj _ _ H).
    - intros ?? []; cbn; intros ?? H; now apply (r_cat_r_inj _ _ H).
    - intros ?? []; cbn; intros ?? H; now apply (r_cat_disj _ _ H).
  Qed.
End with_param.
#[global] Arguments dsum C1 C2 : clear implicits.
