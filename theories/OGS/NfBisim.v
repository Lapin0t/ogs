From OGS Require Import Prelude.
From OGS.Utils Require Import Rel.
From OGS.Ctx Require Import All Ctx Covering Subst.
From OGS.ITree Require Import Event ITree Eq Delay.
From OGS.OGS Require Import Obs Game Machine.

Section with_param.
  Context `{CC : context T C} {CL : context_laws T C} (obs : obs_struct T C).
  Context {val} {VM : subst_monoid val} {VML : subst_monoid_laws val}.
  Context {conf} {CM : subst_module val conf} {CML : subst_module_laws val conf}.
  Context (M : machine val conf obs).

  (* NF bisimulation game *)
  Definition nfb_g : game C (C × C)
    := {| g_client := {| g_move Γ := obs∙ Γ ;
                         g_next Γ o := (Γ , dom o.(cut_r)) |} ;
          g_server := {| g_move '(Γ , Δ) := obs∙ Δ ;
                         g_next '(Γ , Δ) o := Γ +▶ dom o.(cut_r) |} |}.

  Definition nfb_e : event C C
    := e_of_g nfb_g.

  (* active NF bisimulation *)
  Definition nfb_act := itree nfb_e ∅ᵢ.
  (* single-var passive NF bisimulation *)
  Definition nfb_pas₁ (Γ : C) (x : T) := forall o : obs x, nfb_act (Γ +▶ dom o) .
  (* full passive NF bisimulation *)
  Definition nfb_pas '(Γ , Δ) := Δ =[nfb_pas₁]> Γ .

  (* active NF bisimulation with cut-off *)
  Definition nfb_fin Δ Γ := itree nfb_e (fun _ => obs∙ Δ) Γ.
  (* single-var passive NF bisimulation with cut-off *)
  Definition nfb_fin_pas₁ (Δ Γ : C) (x : T) := forall o : obs x, nfb_fin Δ (Γ +▶ dom o) .

  (* renaming active NF bisim *)
  Definition nfb_ren : forall Γ1 Γ2, Γ1 ⊆ Γ2 -> nfb_act Γ1 -> nfb_act Γ2 :=
    cofix _nfb_ren _ _ ρ t :=
      go match t.(_observe) with
         | RetF r => match r with end
         | TauF t => TauF (_nfb_ren _ _ ρ t)
         | VisF q k =>
            VisF (ρ _ q.(cut_l) ⋅ q.(cut_r) : nfb_e.(e_qry) _)
                 (fun r => _nfb_ren _ _ (r_shift (m_dom r) ρ) (k r))
         end .

  Definition nfb_var : c_var ⇒₁ nfb_pas₁
    := cofix _nfb_var Γ x i o :=
      Vis' (r_cat_l i ⋅ o : nfb_e.(e_qry) _)
           (fun r => _nfb_var _ _ (r_cat_r r.(cut_l)) r.(cut_r)) .

  (* renaming active NF bisim with cut-off *)
  Program Definition nfb_fin_ren {Δ} : forall Γ1 Γ2, Γ1 ⊆ Γ2 -> nfb_fin Δ Γ1 -> nfb_fin Δ Γ2 :=
    cofix _nfb_fin_ren _ _ ρ t :=
      go match t.(_observe) with
         | RetF r => RetF r
         | TauF t => TauF (_nfb_fin_ren _ _ ρ t)
         | VisF q k =>
            VisF (ρ _ q.(cut_l) ⋅ q.(cut_r) : nfb_e.(e_qry) _)
                 (fun r => _nfb_fin_ren _ _ (r_shift (m_dom r) ρ) (k r))
         end .

  (* tail-cutting of NF bisim *)
  Program Definition nfb_stop : forall Δ Γ, nfb_act (Δ +▶ Γ) -> nfb_fin Δ Γ :=
    cofix _nfb_stop Δ _ t :=
      go match t.(_observe) with
         | RetF r => match r with end
         | TauF t => TauF (_nfb_stop _ _ t)
         | VisF q k => ltac:(exact
            match c_view_cat q.(cut_l) with
            | Vcat_l i => RetF (i ⋅ q.(cut_r))
            | Vcat_r j => VisF (j ⋅ q.(cut_r) : nfb_e.(e_qry) _)
                              (fun r => _nfb_stop _ _ (nfb_ren _ _ r_assoc_r (k r)))
            end)
          end.

  (* embed active NF-bisim with cut-off to active OGS strategy (generalized) *)
  Definition nfb_to_ogs_aux {Δ}
    : forall Φ (ks : ↓⁻Φ =[nfb_fin_pas₁ Δ]> ↓⁺Φ), nfb_fin Δ ↓⁺Φ -> ogs_act (obs:=obs) Δ Φ.
    cofix _nfb_to_ogs; intros Φ ks t.
    apply go; destruct (t.(_observe)).
    + apply RetF; exact r.
    + apply TauF; exact (_nfb_to_ogs _ ks t0).
    + unshelve eapply VisF; [ exact q | ].
      intro r.
      pose (ks' := [ ks , fun _ j o => k (j ⋅ o) ]%asgn).
      refine (_nfb_to_ogs (Φ ▶ₓ _ ▶ₓ _)%ctx _ (ks' _ r.(cut_l) r.(cut_r))).
      intros ? i o.
      refine (nfb_fin_ren _ _ [ r_cat_l ᵣ⊛ r_cat_l , r_cat_r ]%asgn (ks' _ i o)).
  Defined.

  (* embed active NF-bisim with cut-off to active OGS strategy (initial state) *)
  Definition nfb_to_ogs {Δ Γ} : nfb_fin Δ Γ -> ogs_act Δ (∅ ▶ₓ Γ)
    := fun u => nfb_to_ogs_aux (∅ ▶ₓ Γ) ! (nfb_fin_ren _ _ r_cat_r u) .

  Definition app_no_arg {Γ x} (v : val Γ x) (o : obs x)
    : conf (Γ +▶ dom o)
    := v ᵥ⊛ᵣ r_cat_l ⊙ o ⦗ r_emb r_cat_r ⦘.
  
  (* language machine to NF-bisim *)
  Definition m_nfb_act : conf ⇒₀ nfb_act
    := cofix _m_nfb Γ c
      := subst_delay
           (fun n => Vis' (nf_to_obs _ n : nfb_e.(e_qry) _)
                       (fun o => _m_nfb _ (app_no_arg (nf_args n _ o.(cut_l)) o.(cut_r)))) 
           (eval c).

  Definition m_nfb_pas : val ⇒₁ nfb_pas₁
    := fun _ _ v o => m_nfb_act _ (app_no_arg v o).
End with_param.
