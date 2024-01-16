From OGS Require Import Prelude.
From OGS.Utils Require Import Ctx Rel.
From OGS.Game Require Import HalfGame Event.
From OGS.OGS Require Import Subst Obs Machine Game Strategy.
From OGS.ITree Require Import ITree Eq Delay Structure Properties Guarded.

Open Scope ctx_scope.

Section withFam.

(*|
We consider a language abstractly captured as a machine
|*)
  Context {bT : baseT}.
  Context {bV : baseV}.
  Context {bC : baseC}.
  Context {sV : subst_monoid bV}.
  Context {sC : subst_module bV bC}.
  Context {oS : observation_structure}.
  Context {M: machine}.
(*|
Satisfying an appropriate axiomatization
|*)
  Context {sVL: subst_monoid_laws}.
  Context {sCL: subst_module_laws}.
  Context {VA : var_assumptions} .
  Context {ML: machine_laws}.

(*|
Evaluate a configuration inside an environment (assignment), returning only the message part (the "positive" or "static" part).
|*)
  Definition eval_in_env {Γ Δ} (e : Γ ⇒ᵥ Δ) (t : conf Γ) : delay (obs∙ Δ) :=
    eval_to_obs (e ⊛ₜ t) .

  #[global] Instance eval_in_env_proper {Γ Δ} : Proper (ass_eq Γ Δ ==> eq ==> eq) (@eval_in_env Γ Δ).
    intros ? ? H1 ? ? H2; unfold eval_in_env; now rewrite H1, H2.
  Qed.

  Definition ciu {Γ} Δ (x y : conf Γ) : Prop
    := forall e : Γ ⇒ᵥ Δ, eval_in_env e x ≈ eval_in_env e y.
  Notation "x ≈⟦ciu Δ ⟧≈ y" := (ciu Δ x y) (at level 50).

  Lemma compo_body_guarded_aux {Δ Ψ} (u : alt_env Δ Δ Ⓟ Ψ) (v : alt_env Δ Δ Ⓞ Ψ)
    {x} (m : obs x) (γ : dom m ⇒ᵥ (Δ +▶ ↓⁺ Ψ)) (j : ↓⁺ Ψ ∋ x) :
    ev_guarded (fun 'T1_0 => compo_body (Δ := Δ))
      (compo_body ((Ψ ▶ dom m),' (app (r_concat3_1 ᵣ⊛ᵥ concat0 v x j) m ((v_var ⊛ᵣ r_concat_r) ⊛ᵣ r_concat_r), v ▶ₑ⁺, u ▶ₑ⁻ γ))) .
  Proof.
    pose (m' := (x ,' m)).
    revert γ j.
    change x with (projT1 m').
    change m with (projT2 m').
    remember m' as m''; clear m' m x Heqm''; rename m'' into m.
    pose (wf := eval_app_not_var m).

    revert Ψ u v; induction wf; intros Ψ u v γ j.
    destruct x as [ x m ]; cbn [projT1 projT2] in *.

    pose (h := lt_wf (var_height j)); remember (var_height j) as n.
    revert Ψ u v γ j Heqn; induction h; intros Ψ u v γ j Heqn.

    unfold ev_guarded; cbn -[cat_split].

    pose (vv := @r_concat3_1 typ Δ ↓⁻ Ψ (@dom S x m) ᵣ⊛ᵥ concat0 v x j).
    change (r_concat3_1 ᵣ⊛ᵥ _) with vv; destruct (is_var_dec vv).

    - destruct i as [ i eq ].
      rewrite eq.
      eassert (H3 : _) by exact (eval_nf_ret (_ ,' (i , (m ,' ((v_var ⊛ᵣ r_concat_r) ⊛ᵣ r_concat_r))))).
      unfold comp_eq in H3.
      apply it_eq_step in H3; cbn in H3; unfold observe in H3.
      pose (ot := _observe (eval (app (v_var x i) m ((v_var ⊛ᵣ r_concat_r) ⊛ᵣ r_concat_r)))); fold ot in H3 |- *.
      destruct ot; dependent elimination H3.
      cbn in r1, r_rel |- * .
      destruct r1 as [ x' [ i' [ m' a' ] ] ].
      destruct r_rel as [ p [ q r ] ]; cbn in *.
      unfold m_strat_wrap; unfold dom' in a'; unfold msg_of_nf', nf_ty', nf_var', nf_msg' in *; cbn [ fst snd projT1 projT2] in *.
      revert i' m' a' q r; rewrite p; clear p x'; intros i' m' a' q [ r1 _ ]; cbn in q, r1.
      rewrite q; clear q i'.
      revert a'; rewrite r1; clear r1 m'; intros a'.
      pose (i' := (i ,' eq) : is_var vv).
      change i with (is_var_get i').
      remember i' as ii; clear i i' Heqii eq.
      unfold vv in ii; destruct (view_is_var_ren _ _ ii).
      destruct p; simpl is_var_get.
      destruct (cat_split x1).
      * unfold r_concat3_1; change (?u x (r_cover_l _ x i)) with ((u ⊛ᵣ r_concat_l) x i).
        rewrite s_eq_cat_l, cat_split_l.
        now do 2 econstructor.
      * unfold r_concat3_1; change (?u x (r_cover_r _ x j0)) with ((u ⊛ᵣ r_concat_r) x j0).
        rewrite s_eq_cat_r; unfold s_ren, s_map; rewrite cat_split_r.
        unfold dom', m_strat_resp; cbn [fst snd projT1 projT2].
        refine (GNext _); eapply H2; [ | reflexivity ].

        rewrite Heqn.
        unfold var_height; rewrite var_depth_ext.
        simpl c_length; rewrite PeanoNat.Nat.sub_succ.
        apply (Plus.plus_lt_reg_l_stt _ _ (var_depth j0 + var_depth j)).
        rewrite PeanoNat.Nat.add_shuffle0.
        rewrite Arith_prebase.le_plus_minus_r_stt; [ | exact (@var_depth_le _ false _ j0) ].
        rewrite <- PeanoNat.Nat.add_assoc.
        rewrite Arith_prebase.le_plus_minus_r_stt; [ | exact (@var_depth_le Ψ _ _ j) ].
        rewrite PeanoNat.Nat.add_comm.
        apply Plus.plus_lt_compat_r_stt.
        exact (depth_increases v j j0 e).

    - remember (eval (app vv m ((v_var ⊛ᵣ r_concat_r) ⊛ᵣ r_concat_r))) as t.
      remember (_observe t) as ot.
      destruct ot; try now do 2 econstructor.
      unfold m_strat_wrap.
      destruct r as [ x' [ j' [ m' a' ]]]. unfold nf_msg', nf_val' in *. cbn [ fst snd projT1 projT2 ].
      pose (uu := cat_split j'); change (cat_split j') with uu; destruct uu.
      now do 2 econstructor.
      refine (GNext _).
      unfold dom', msg_msg'; cbn [fst snd projT1 projT2].
      eapply (H0 (x' ,' m')).
      econstructor.
      exact f.
      apply it_eq_unstep; cbn.
      rewrite Heqt in Heqot.
      rewrite <- Heqot.
      econstructor; reflexivity.
  Qed.


  Lemma compo_body_guarded {Δ} : eqn_ev_guarded (fun 'T1_0 => compo_body (Δ := Δ)).
    intros [] [ Γ [ [c u] v ] ]; unfold m_strat_pas in v.
    unfold ev_guarded; cbn -[cat_split].
    pose (ot := _observe (eval c)); change (_observe (eval c)) with ot.
    destruct ot; try now do 2 econstructor.
    remember r as r'; rewrite Heqr'.
    unfold m_strat_wrap; destruct r as [ ? [ i [ m γ ] ] ]; cbn in *.
    destruct (cat_split i); try now do 2 econstructor.
    refine (GNext _).
    unfold obs'_dom, obs'_obs, obs'_ty; cbn [ fst snd projT1 projT2 ].
    apply compo_body_guarded_aux.
  Qed.

  Definition compo_ev_guarded {Δ a} (u : m_strat_act Δ a) (v : m_strat_pas Δ a) : delay (msg' Δ)
    := iter_ev_guarded _ compo_body_guarded T1_0 (a ,' (u , v)).
  Notation "u ∥g v" := (compo_ev_guarded u v) (at level 40).

  Lemma quatre_trois_app {Γ Δ} (c : conf Γ) (e : Γ ⇒ᵥ Δ) :
    eval_in_env e c ≊ (inj_init_act Δ c ∥g inj_init_pas e).
  Proof.
    etransitivity; [ | apply quatre_trois ].
    unfold reduce, inj_init_act, eval_in_env; cbn [fst snd projT1 projT2]; apply (fmap_eq (RX:=eqᵢ _)).
    intros ? ? ? ->; auto.
    unfold inj_init_pas; rewrite concat1_equation_2, 2 concat1_equation_1.
    unfold c_ren; rewrite c_sub_sub, c_sub_proper ; try reflexivity.
    rewrite s_eq_cover_empty_r.
    rewrite e_comp_ren_r, v_sub_var.
    rewrite s_ren_comp, 2 s_eq_cat_r.
    unfold e_ren, r_concat_l, cover_cat; cbn; rewrite r_cover_l_nil, s_ren_id.
    now rewrite 2 v_var_sub.
  Qed.

  Definition barb {Γ} Δ (x y : conf Γ) : Prop
    := forall e : Γ ⇒ᵥ Δ, (inj_init_act Δ x ∥ inj_init_pas e) ≈ (inj_init_act Δ y ∥ inj_init_pas e).
  Notation "x ≈⟦barb Δ ⟧≈ y" := (barb Δ x y) (at level 50).

  Theorem barb_correction {Γ} Δ (x y : conf Γ) : x ≈⟦barb Δ ⟧≈ y -> x ≈⟦ciu Δ ⟧≈ y.
  Proof.
    intros H e.
    etransitivity; [ apply it_eq_wbisim, (quatre_trois_app x e) | ].
    etransitivity; [ apply iter_evg_iter | ].
    etransitivity; [ apply (H e) | symmetry ].
    etransitivity; [ apply it_eq_wbisim, (quatre_trois_app y e) | ].
    etransitivity; [ apply iter_evg_iter | ].
    reflexivity.
  Qed.

  Theorem ogs_correction {Γ} Δ (x y : conf Γ) : x ≈⟦ogs Δ ⟧≈ y -> x ≈⟦ciu Δ ⟧≈ y.
  Proof.
    intro H; apply barb_correction.
    intro e; unfold compo.
    change (iter _ T1_0 ?u) with (iter_delay compo_body u); rewrite <- 2 compo_compo_alt.
    apply compo_alt_proper; [ exact H | intro; reflexivity ].
  Qed.

End withInteractionSpec.
About ogs_correction.
Print Assumptions ogs_correction.
