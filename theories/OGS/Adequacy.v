(*|
Adequacy (Def 6.1)
==================

We prove in this module that the composition of strategy is adequate.
The proof essentially proceeds by showing that "evaluating and observing",
i.e., [reduce], is a solution of the same equations as is the composition
of strategies.

This argument assumes we can rely on the unicity of such a solution:
we prove this fact by proving that these equations are eventually
guarded in [OGS/CompGuarded.v].
|*)

(* for some reason we need this for some instance resolution *)
From Coinduction Require Import coinduction.

From OGS Require Import Prelude.
From OGS.Utils Require Import Rel.
From OGS.Ctx Require Import All Ctx.
From OGS.OGS Require Import Subst Obs Machine Strategy CompGuarded.
From OGS.ITree Require Import Event ITree Eq Delay Structure Properties Guarded.

Section with_param.
(*|
We consider a language abstractly captured as a machine satisfying an
appropriate axiomatization.
|*)
  Context {T C} {CC : context T C} {CL : context_laws T C}.
  Context {val} {VM : subst_monoid val} {VML : subst_monoid_laws val}.
  Context {conf} {CM : subst_module val conf} {CML : subst_module_laws val conf}.
  Context {obs : obs_struct T C} {M : machine val conf obs} {ML : machine_laws val conf obs}.
  Context {VV : var_assumptions val}.

  (*
(*|
Evaluate a configuration inside an environment (assignment), returning only the message part (the "positive" or "static" part).
|*)
  Definition eval_in_env {Γ Δ} (e : Γ =[val]> Δ) (c : conf Γ) : delay (obs∙ Δ) :=
    evalₒ (c ₜ⊛ t) .

  #[global] Instance eval_in_env_proper {Γ Δ} : Proper (ass_eq Γ Δ ==> eq ==> eq) (@eval_in_env Γ Δ).
    intros ? ? H1 ? ? H2; unfold eval_in_env; now rewrite H1, H2.
  Qed.
*)

  Definition reduce {Δ} (x : reduce_t Δ)
    : delay (obs∙ Δ)
    := evalₒ (x.(red_act).(ms_conf)
              ₜ⊛ [ a_id , bicollapse x.(red_act).(ms_env) x.(red_pas) ]) .

  Definition reduce' {Δ} : forall i, reduce_t Δ -> itree ∅ₑ (fun _ : T1 => obs∙ Δ) i
    := fun 'T1_0 => reduce .

  Check (it_eq_t_trans).

  (*Tactic Notation "mytransitivity" := first [eapply @transitivity; [eapply it_eq_t_trans; fail | |] | etransitivity].*)

(*|
Equipped with eventually guarded equations, we are ready to prove the adequacy
|*)
  Lemma compo_reduce_simpl {Δ} (x : reduce_t Δ) :
    (compo_body x >>= fun _ r =>
         match r with
         | inl y => reduce' _ y
         | inr o => Ret' (o : (fun _ => obs∙ _) _)
         end)
      ≊
      (eval x.(red_act).(ms_conf) >>= fun _ n =>
           match c_view_cat (nf_var n) with
           | Vcat_l i => Ret' (i ⋅ nf_obs n)
           | Vcat_r j => reduce' _ (RedT (m_strat_resp x.(red_pas) (j ⋅ nf_obs n))
                                        (x.(red_act).(ms_env) ;⁻ nf_args n))
           end).
  Proof.
    do 2 (etransitivity; [ now apply fmap_bind_com | ]).
    apply (subst_eq (RX := fun _ => eq)); eauto.
    intros ? [ ? i [ ? ? ] ] ? <-.
    unfold m_strat_wrap; cbn.
    now destruct (c_view_cat i).
  Qed.

  Definition eval_split_sub {Γ Δ} (c : conf (Δ +▶ Γ)) (e : Γ =[val]> Δ)
    : delay (nf obs val Δ)
    := eval c >>= fun 'T1_0 n =>
         match c_view_cat (nf_var n) with
         | Vcat_l i => Ret' (i ⋅ nf_obs n ⦇ nf_args n ⊛ [ v_var,  e ] ⦈)
         | Vcat_r j => eval (e _ j ⊙ nf_obs n ⦗ nf_args n ⊛ [ v_var,  e ] ⦘)
         end .

  Lemma eval_split {Γ Δ} (c : conf (Δ +▶ Γ)) (e : Γ =[val]> Δ) :
    eval (c ₜ⊛ [ a_id , e ]) ≋ eval_split_sub c e .
  Proof.
    unfold eval_split_sub.
    rewrite (eval_sub c ([ v_var , e ])).
    apply (subst_eq (RX := fun _ => eq)); eauto.
    intros [] [ ? i [ o a ] ] ? <-; unfold emb; cbn.
    destruct (c_view_cat i).
    + unfold nf_args, fill_args, cut_r.
      rewrite app_sub, v_sub_var.
      cbn; rewrite c_view_cat_simpl_l.
      now apply (eval_nf_ret (i ⋅ o ⦇ a ⊛ [a_id, e] ⦈)).
    + rewrite app_sub, v_sub_var.
      cbn; now rewrite c_view_cat_simpl_r.
  Qed.

(*|
Note the use of [iter_evg_uniq]: the proof of adequacy is proved by unicity
of the fixed point, which is made possible by equivalently viewing the fixpoint
combinator used to define the composition of strategy as a fixpoint of eventually
guarded equations.
|*)

  Lemma adequacy_gen {Δ a} (c : m_strat_act Δ a) (e : m_strat_pas Δ a) :
    reduce (RedT c e) ≊ (c ∥g e).
  Proof.
    refine (iter_evg_uniq (fun 'T1_0 u => compo_body u) (fun 'T1_0 u => reduce u) _ _ T1_0 _).
    clear a c e; intros [] [ ? [ u v ] ].
    etransitivity; [ | symmetry; apply compo_reduce_simpl ].
    unfold reduce at 1, evalₒ at 1; rewrite eval_split.
    etransitivity; [ apply bind_fmap_com | ].
    apply (subst_eq (RX := fun _ => eq)); eauto.
    intros [] [ ? i [ o a ] ] ? <-; unfold emb; cbn.
    destruct (c_view_cat i).
    - rewrite c_view_cat_simpl_l.
      apply it_eq_unstep; cbn; do 2 econstructor.
    - rewrite c_view_cat_simpl_r.
      unfold reduce; cbn; unfold nf_args, cut_r, fill_args; cbn.
      assert (H : (bicollapse v red_pas cut_ty j ⊙ o ⦗ a ⊛ [a_id, bicollapse v red_pas] ⦘)
                  = ((ₐ↓ red_pas cut_ty j ᵥ⊛ r_emb r_cat3_1) ⊙ o ⦗ r_cat_rr ᵣ⊛ a_id ⦘
       ₜ⊛ [a_id, [bicollapse v red_pas, a ⊛ [a_id, bicollapse v red_pas]]])).             
        rewrite app_sub, <- v_sub_sub.
      
        (* AAAAA setoid rewriting!!!! *)
        etransitivity; cycle 1.
        unshelve erewrite v_sub_proper.
        5: { rewrite (a_ren_r_simpl _ r_cat3_1 _).
             now rewrite r_cat3_1_simpl; eauto.
           }
        3,4: reflexivity.

        change (?r ᵣ⊛ a_id)%asgn with (r_emb r); rewrite a_ren_r_simpl.
        unfold r_cat_rr; rewrite a_ren_l_comp.
        rewrite 2 a_cat_proj_r.

        pose proof (H := collapse_fix_pas v red_pas _ j).
        cbn in H; now rewrite H.
        exact _.

      pose (xx := bicollapse v red_pas cut_ty j ⊙ o ⦗ a ⊛ [a_id, bicollapse v red_pas] ⦘).
      change (bicollapse v _ _ _ ⊙ o ⦗ _ ⦘) with xx in H |- *.
      now rewrite H.
  Qed.

(*|
Adequacy (Def 6.1) holds
|*)
  Lemma adequacy {Γ Δ} (c : conf Γ) (e : Γ =[val]> Δ) :
    evalₒ (c ₜ⊛ e) ≊ (inj_init_act Δ c ∥g inj_init_pas e).
  Proof.
    rewrite <- adequacy_gen; unfold reduce; cbn.
    now rewrite <- c_sub_sub, a_ren_r_simpl,
          a_ren_l_comp, 2 a_cat_proj_r,
          a_ren_comp, a_cat_proj_l, a_comp_id.
  Qed.
End with_param.

