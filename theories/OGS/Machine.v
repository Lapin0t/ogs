From OGS Require Import Prelude.
From OGS.Utils Require Import Ctx Rel.
From OGS.Game Require Import HalfGame Event.
From OGS.OGS Require Import Subst Obs.
From OGS.ITree Require Import ITree Eq Delay Structure Properties Guarded.

Section withFam.
  Context {bT : baseT}.
  Context {bV : baseV}.
  Context {bC : baseC}.
  Context {sV : subst_monoid bV}.
  Context {sC : subst_module bV bC}.
  Context {oS : observation_structure}.

  Class machine : Type := {
      eval {Γ} : conf Γ -> delay (nf' Γ) ;
      app {Γ x} (v : val Γ x) (m : obs x) (r : dom m ⇒ᵥ Γ) : conf Γ ;
    }.

  Context {M : machine}.

  Definition eval_to_obs {Γ} (t : conf Γ) : delay (obs∙ Γ) :=
    fmap_delay (obs'_of_nf' Γ) (eval t) .

  Variant head_inst_nostep (u : { x : typ & obs x }) : { x : typ & obs x } -> Prop :=
  | HeadInst {Γ y} (v : val Γ y) (m : obs y) (e : dom m ⇒ᵥ Γ) (p : is_var v -> False) (i : Γ ∋ projT1 u)
             : eval_to_obs (app v m e) ≊ ret_delay (projT1 u ,' (i , projT2 u)) ->
               head_inst_nostep u (y ,' m) .

  Class machine_laws : Prop := {
    app_proper {Γ x v m} :: Proper (ass_eq (dom m) Γ ==> eq) (@app _ Γ x v m) ;

    app_sub {Γ1 Γ2 x} (e : Γ1 ⇒ᵥ Γ2) (v : val Γ1 x) (m : obs x) (r : dom m ⇒ᵥ Γ1)
      : e ⊛ₜ app v m r = app (e ⊛ᵥ v) m (e ⊛ r) ;

    eval_sub {Γ Δ} (c : conf Γ) (e : Γ ⇒ᵥ Δ)
      : eval (e ⊛ₜ c)
      ≋ bind_delay' (eval c) (fun u => eval (app (e _ (nf'_var u)) (nf'_obs u) (e ⊛ nf'_val u))) ;

    eval_nf_ret {Γ} (u : nf' Γ) :
      eval (app (v_var _ (nf'_var u)) (nf'_obs u) (nf'_val u))
      ≋ ret_delay u ;

    eval_app_not_var : well_founded head_inst_nostep ;
  } .


End withFam.
