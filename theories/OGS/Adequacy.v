From OGS Require Import Prelude.
From OGS.Utils Require Import Ctx Rel.
From OGS.Game Require Import HalfGame Event.
From OGS.OGS Require Import Subst Obs Machine Game Strategy Utility_lemmas CompGuarded.
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

  Equations reduce {Δ} : reduce_t Δ -> delay (obs∙ Δ) :=
    reduce u := eval_in_env
                  ([ v_var , concat1 (snd (fst (projT2 u))) (snd (projT2 u)) ])
                  (fst (fst (projT2 u))) .

  Definition reduce' {Δ} : forall i, reduce_t Δ -> itree ∅ₑ (fun _ : T1 => msg' Δ) i := fun 'T1_0 => reduce .


(*|
Equipped with eventually guarded equations, we are ready to prove the adequacy
|*)
  Lemma adequacy_pre {Δ} (x : reduce_t Δ) :
    (compo_body x >>= fun _ r =>
         match r with
         | inl x' => reduce' _ x'
         | inr y => Ret' (y : (fun _ => msg' _) _)
         end)
      ≊
      (eval (fst (fst (projT2 x))) >>= fun _ u =>
           match cat_split (nf_var' u) with
           | CLeftV h => Ret' (_ ,' (h, nf_msg' u))
           | CRightV h => reduce' _ (_ ,' (m_strat_resp (snd (projT2 x)) (_ ,' (h, nf_msg' u)) ,
                                           snd (fst (projT2 x)) ▶ₑ⁻ nf_val' u))
           end).
  Proof.
    etransitivity; [ now apply bind_bind_com | ].
    etransitivity; [ now apply fmap_bind_com | ].
    unfold m_strat_play, m_strat_wrap.
    remember (eval (fst (fst (projT2 x)))) as t eqn:H; clear H; revert t.
    unfold it_eq; coinduction R CIH; intros t.
    cbn; destruct (t.(_observe)) as [ [ ? [ i [ ? ? ] ] ] | | [] ]; cbn.
    + destruct (cat_split i).
      * econstructor; reflexivity.
      * cbn -[eval_in_env] .
        change (it_eqF _ _ _ _ (_observe ?a) (_observe ?b))
          with (it_eq_map  ∅ₑ (eqᵢ _) (it_eq_t _ (eqᵢ _) R) T1_0 a b).
        reflexivity.
    + econstructor; apply CIH.
  Qed.

  Lemma adequacy {Δ a} (c : m_strat_act Δ a) (e : m_strat_pas Δ a) :
    reduce (_ ,' (c , e)) ≊ (c ∥g e).
  Proof.
    refine (iter_evg_uniq (fun 'T1_0 u => compo_body u) (fun 'T1_0 u => reduce u) _ _ T1_0 _).
    clear a c e; intros [] [ ? [ u v ] ].
    etransitivity; [ | symmetry; apply adequacy_pre ].
    unfold reduce at 1.
    etransitivity; [ apply eval_to_msg_eq, eval_split | ].
    etransitivity; [ apply bind_fmap_com | ].
    unfold it_eq; cbn [fst snd projT2 projT1].
    apply (tt_t (it_eq_map ∅ₑ (eqᵢ _))).
    refine (it_eq_up2bind_t _ _ _ _ (eval (fst u) >>= _) (eval (fst u) >>= _) _); econstructor; eauto.
    intros [] [ t1 [ i1 [ m1 γ1 ] ]] [ t2 [ i2 [ m2 γ2 ] ]] [ p [ q r ] ].
    cbn in *.
    revert i1 m1 γ1 q r; rewrite p; clear p t1; intros i1 m1 γ1 q r; cbn in q,r.
    rewrite q; clear q i1.
    destruct r as [ p q ]; cbn in p,q.
    revert γ1 q; rewrite p; clear p m1; intros γ1 q; cbn in q.
    apply (bt_t (it_eq_map ∅ₑ (eqᵢ (fun _ : T1 => msg' Δ)))).
    pose (xx := cat_split i2); change (cat_split i2) with xx; destruct xx.
    - cbn; econstructor; reflexivity.
    - cbn -[it_eq_map fmap].
      change (it_eq_t ∅ₑ (eqᵢ (fun _ : T1 => msg' Δ)) bot) with (it_eq (E:=∅ₑ) (eqᵢ (fun _ : T1 => msg' Δ))).
      apply it_eq_step, (fmap_eq (RX := eqᵢ _)).
      intros ? ? ? ->; auto.
      unfold m_strat_resp; cbn [fst snd projT1 projT2].
      rewrite app_sub, concat1_equation_2.

      pose (xx := [ v_var , [concat1 v (snd u), ([v_var, concat1 (snd u) v]) ⊛ γ2]] ⊛ᵥ r_concat3_1 ᵣ⊛ᵥ concat0 v t2 j).
      change ([ v_var , [ _ , _ ]] ⊛ᵥ _) with xx.
      assert (H : xx = concat1 (snd u) v t2 j); [ | rewrite H; clear H ].
      + unfold xx; clear xx.
        change (?a ⊛ᵥ ?b ᵣ⊛ᵥ (concat0 v _ j)) with ((a ⊛ (b ᵣ⊛ concat0 v)) _ j).
        unfold e_ren; rewrite v_sub_sub.
        etransitivity; [ | now apply (proj2 (concat_fixpoint (snd u) v)) ].
        eapply e_comp_proper; [ | reflexivity ].
        rewrite e_comp_ren_r, v_sub_var.
        unfold r_concat3_1.
        etransitivity; [ unfold s_ren at 1; apply s_eq_cover_map | ].
        change (s_map ?a ?b) with (s_ren a b); change (s_cover cover_cat ?a ?b) with ([ a , b ]).
        now rewrite s_eq_cat_l, s_ren_comp, s_eq_cat_r, s_eq_cat_l.
      + erewrite app_proper; [ reflexivity | ].
        now rewrite q, 2 e_comp_ren_r, v_sub_var, 2 s_eq_cat_r.
  Qed.

  Lemma adequacy_app {Γ Δ} (c : conf Γ) (e : Γ ⇒ᵥ Δ) :
    eval_in_env e c ≊ (inj_init_act Δ c ∥g inj_init_pas e).
  Proof.
    etransitivity; [ | apply adequacy ].
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


  Definition ciu {Γ} Δ (x y : conf Γ) : Prop
    := forall e : Γ ⇒ᵥ Δ, eval_in_env e x ≈ eval_in_env e y.
  Notation "x ≈⟦ciu Δ ⟧≈ y" := (ciu Δ x y) (at level 50).


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
