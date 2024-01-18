From Coinduction Require Import coinduction tactics.

From OGS Require Import Prelude.
From OGS.Utils Require Import Ctx Rel.
From OGS.Game Require Import HalfGame Event.
From OGS.OGS Require Import Subst Obs Machine Game Strategy CompGuarded.
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
                  ([ v_var , concat1 _ (snd (fst (projT2 u))) (snd (projT2 u)) ])
                  (fst (fst (projT2 u))) .

  Definition reduce' {Δ} : forall i, reduce_t Δ -> itree ∅ₑ (fun _ : T1 => obs∙ Δ) i := fun 'T1_0 => reduce .

  Tactic Notation "mytransitivity" := first [eapply @transitivity; [eapply it_eq_t_trans; fail | |] | etransitivity].

(*|
Equipped with eventually guarded equations, we are ready to prove the adequacy
|*)
  Lemma adequacy_pre {Δ} (x : reduce_t Δ) :
    (compo_body x >>= fun _ r =>
         match r with
         | inl x' => reduce' _ x'
         | inr y => Ret' (y : (fun _ => obs∙ _) _)
         end)
      ≊
      (eval (fst (fst (projT2 x))) >>= fun _ u =>
           match cat_split (nf'_var u) with
           | CLeftV h => Ret' (_ ,' (h, nf'_obs u))
           | CRightV h => reduce' _ (_ ,' (m_strat_resp (snd (projT2 x)) (_ ,' (h, nf'_obs u)) ,
                                           snd (fst (projT2 x)) ▶ₑ⁻ nf'_val u))
           end).
  Proof.
    mytransitivity; [ now apply bind_bind_com | ].
    mytransitivity; [ now apply fmap_bind_com | ].
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

  Definition split_sub_eval {Γ Δ} (c : conf (Δ +▶ Γ)) (e : Γ ⇒ᵥ Δ) : delay (nf∙ Δ) :=
    eval ([ v_var , e ] ⊛ₜ c) .

  Definition eval_split_sub {Γ Δ} (c : conf (Δ +▶ Γ)) (e : Γ ⇒ᵥ Δ) : delay (nf' Δ) :=
    eval c >>= fun 'T1_0 u =>
        match cat_split (nf'_var u) with
        | CLeftV h => Ret' (nf'_ty u ,' (h , (nf'_obs u ,' [ v_var,  e ] ⊛ nf'_val u)))
        | CRightV h => eval (app (e _ h) (nf'_obs u) ([v_var , e ] ⊛ nf'_val u))
        end .

  Lemma eval_split {Γ Δ} (c : conf (Δ +▶ Γ)) (e : Γ ⇒ᵥ Δ) :
    split_sub_eval c e ≋ eval_split_sub c e .
  Proof.
    unfold split_sub_eval, eval_split_sub.
    rewrite (eval_sub c ([ v_var , e ])).
    unfold bind_delay'.
    remember (eval c) as t; clear c Heqt.
    revert t; unfold comp_eq,it_eq; coinduction R CIH; cbn; intro t.
    destruct (_observe t); [ | econstructor; apply CIH | inversion q ].
    destruct r as [ x [ i [ m γ ] ] ]; cbn in *.
    destruct (cat_split i).
    + change (?u x (r_cover_l cover_cat x i)) with ((u ⊛ᵣ r_concat_l) x i).
      rewrite s_eq_cat_l.
      eassert (H : _) by exact (eval_nf_ret (x ,' (i , (m ,' ([v_var, e]) ⊛ γ)))).
      unfold comp_eq in H.
      apply it_eq_step in H; cbn in *; unfold observe in H.
      destruct (_observe (eval (app (v_var x i) m (([v_var, e]) ⊛ γ)))); dependent elimination H; auto.
    + change (?u x (r_cover_r cover_cat x j)) with ((u ⊛ᵣ r_concat_r) x j).
      rewrite s_eq_cat_r.
      destruct (_observe (eval (app (e x j) m (([v_var, e]) ⊛ γ)))); econstructor; auto.
      now apply nf_eq_rfl'.
  Qed.

  Lemma adequacy_gen {Δ a} (c : m_strat_act Δ a) (e : m_strat_pas Δ a) :
    reduce (_ ,' (c , e)) ≊ (c ∥g e).
  Proof.
    refine (iter_evg_uniq (fun 'T1_0 u => compo_body u) (fun 'T1_0 u => reduce u) _ _ T1_0 _).
    clear a c e; intros [] [ ? [ u v ] ].
    etransitivity; [ | symmetry; apply adequacy_pre ].
    unfold reduce at 1.
    etransitivity; [ apply eval_to_obs_eq, eval_split | ].
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
    apply (bt_t (it_eq_map ∅ₑ (eqᵢ (fun _ : T1 => obs∙ Δ)))).
    pose (xx := cat_split i2); change (cat_split i2) with xx; destruct xx.
    - cbn; econstructor; reflexivity.
    - cbn -[it_eq_map fmap].
      change (it_eq_t ∅ₑ (eqᵢ (fun _ : T1 => obs∙ Δ)) bot) with (it_eq (E:=∅ₑ) (eqᵢ (fun _ : T1 => obs∙ Δ))).
      apply it_eq_step, (fmap_eq (RX := eqᵢ _)).
      intros ? ? ? ->; auto.
      unfold m_strat_resp; cbn [fst snd projT1 projT2].
      rewrite app_sub, concat1_equation_2.

      pose (xx := [ v_var , [concat1 _ v (snd u), ([v_var, concat1 _ (snd u) v]) ⊛ γ2]] ⊛ᵥ r_concat3_1 ᵣ⊛ᵥ concat0 v t2 j).
      change ([ v_var , [ _ , _ ]] ⊛ᵥ _) with xx.
      assert (H : xx = concat1 _ (snd u) v t2 j); [ | rewrite H; clear H ].
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

 (* Something in the refactoring broke all rewrites in this proof,
     there seems to be a unification problem diverging during TC search.
     To be fixed, for now we painfully fix the proofs by hand.
   *)
  Lemma adequacy {Γ Δ} (c : conf Γ) (e : Γ ⇒ᵥ Δ) :
    eval_in_env e c ≊ (inj_init_act Δ c ∥g inj_init_pas e).
  Proof.
    etransitivity; [ | apply adequacy_gen ].
    unfold reduce, inj_init_act, eval_in_env; cbn [fst snd projT1 projT2]; apply (fmap_eq (RX:=eqᵢ _)).
    intros ? ? ? ->; auto.
    unfold inj_init_pas; rewrite concat1_equation_2, 2 concat1_equation_1.
    unfold c_ren; rewrite c_sub_sub, c_sub_proper ; try reflexivity.
    etransitivity.
    2:{
      eapply e_comp_proper; [| reflexivity].
      eapply s_cover_proper; [reflexivity |].
      eapply s_cover_proper; [reflexivity |].
      eapply e_comp_proper; [| reflexivity].
      apply s_eq_cover_empty_r.
    }
    rewrite e_comp_ren_r, v_sub_var.
    rewrite s_ren_comp.
    (* rewrite s_eq_cat_r. *)
    etransitivity.
    2:{
      eapply s_ren_proper; [| reflexivity].
      symmetry; apply s_eq_cat_r.
    }
    etransitivity.
    2:{
      symmetry; apply s_eq_cat_r.
    }
    unfold e_ren, r_concat_l, cover_cat; cbn.
    etransitivity.
    2:{
      eapply e_comp_proper; [reflexivity |].
      eapply e_comp_proper; [| reflexivity].
      eapply s_ren_proper; [reflexivity |].
      symmetry; apply r_cover_l_nil.
    }
    etransitivity.
    2:{
      eapply e_comp_proper; [reflexivity |].
      eapply e_comp_proper; [| reflexivity].
      symmetry; apply s_ren_id.
    }
    etransitivity.
    2:{
      eapply e_comp_proper; [reflexivity |].
      symmetry; apply v_var_sub.
    }
    etransitivity.
    2:{
      eapply e_comp_proper; [| reflexivity].
      symmetry; apply s_eq_cover_empty_r.
    }
    etransitivity.
    2:{
      eapply e_comp_proper; [| reflexivity].
      symmetry; apply s_eq_cover_empty_r.
    }
    symmetry; apply v_var_sub.
  Qed.

End withFam.

