Definition split_sub_eval {Γ Δ} (c : conf (Δ +▶ Γ)) (e : Γ ⇒ᵥ Δ) : delay (nf∙ Δ) :=
  eval ([ v_var , e ] ⊛ₜ c) .

Definition eval_split_sub {Γ Δ} (c : conf (Δ +▶ Γ)) (e : Γ ⇒ᵥ Δ) : delay (nf' Δ) :=
  eval c >>= fun 'T1_0 u =>
      match cat_split (nf_var' u) with
      | CLeftV h => Ret' (nf_ty' u ,' (h , (nf_msg' u ,' [ v_var,  e ] ⊛ nf_val' u)))
      | CRightV h => eval (app (e _ h) (nf_msg' u) ([v_var , e ] ⊛ nf_val' u))
      end .

Lemma eval_to_msg_eq {Γ} (a b : delay (nf' Γ)) (H : a ≋ b) :
  fmap_delay (@msg_of_nf' Γ) a ≊ fmap_delay (@msg_of_nf' Γ) b .
Proof.
  revert a b H; unfold it_eq; coinduction R CIH; intros a b H.
  unfold comp_eq in H; apply it_eq_step in H.
  cbn in *; unfold observe in H.
  destruct (_observe a), (_observe b); dependent elimination H; econstructor.
  - destruct r_rel as [ p [ q [ r _ ] ] ].
    destruct r1 as [ x1 [ i1 [ m1 a1 ] ] ], r2 as [ x2 [ i2 [ m2 a2 ] ] ].
    unfold msg_of_nf', nf_ty', nf_var', nf_msg' in *; cbn in *.
    revert i1 m1 a1 q r; rewrite p; intros i1 m1 a1 q r.
    now do 2 f_equal.
  - now apply CIH.
  - inversion q1.
Qed.

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

Equations reduce {Δ} : reduce_t Δ -> delay (msg' Δ) :=
  reduce u := eval_in_env
                ([ v_var , concat1 (snd (fst (projT2 u))) (snd (projT2 u)) ])
                (fst (fst (projT2 u))) .

  Definition reduce' {Δ} : forall i, reduce_t Δ -> itree ∅ₑ (fun _ : T1 => msg' Δ) i := fun 'T1_0 => reduce .

  Lemma quatre_trois_pre {Δ} (x : reduce_t Δ) :
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

  (* Alternative definition of the composition easier to prove
  congruence (respecting weak bisimilarity). *)

  Definition compo_alt_t (Δ : context) : Type :=
    ⦉ ogs_act Δ ×ᵢ ogs_pas Δ ⦊ᵢ .

  Notation "'RetD' x" := (RetF (x : (fun _ : T1 => _) T1_0)) (at level 40).
  Notation "'TauD' t" := (TauF (t : itree ∅ₑ (fun _ : T1 => _) T1_0)) (at level 40).

  Equations compo_alt_body {Δ} : compo_alt_t Δ -> delay (compo_alt_t Δ + msg' Δ) :=
    compo_alt_body :=
      cofix _compo_body u :=
        go match (fst (projT2 u)).(_observe) with
            | RetF r => RetD (inr r)
            | TauF t => TauD (_compo_body (_ ,' (t , (snd (projT2 u)))))
            | VisF e k => RetD (inl (_ ,' (snd (projT2 u) e , k)))
            end .

  Definition compo0 {Δ a} (u : ogs_act Δ a) (v : ogs_pas Δ a) : delay (msg' Δ)
    := iter_delay compo_alt_body (a ,' (u , v)).

  Definition compo_t_eq (Δ : context) : relation (compo_alt_t Δ) :=
    fun x1 x2 =>
     exists p : projT1 x1 = projT1 x2,
       rew p in fst (projT2 x1) ≈ fst (projT2 x2)
       /\ h_pasvR ogs_hg (it_wbisim (eqᵢ _)) _ (rew p in snd (projT2 x1)) (snd (projT2 x2)).

  Definition compo_t_eq_strong (Δ : context) : relation (compo_alt_t Δ) :=
    fun x1 x2 =>
     exists p : projT1 x1 = projT1 x2,
       rew p in fst (projT2 x1) ≊ fst (projT2 x2)
       /\ h_pasvR ogs_hg (it_eq (eqᵢ _)) _ (rew p in snd (projT2 x1)) (snd (projT2 x2)).

  #[global] Instance compo_alt_proper {Δ a}
    : Proper (it_wbisim (eqᵢ _) a ==> h_pasvR ogs_hg (it_wbisim (eqᵢ _)) a ==> it_wbisim (eqᵢ _) T1_0)
        (@compo0 Δ a).
    intros x y H1 u v H2.
    unshelve eapply (iter_weq (RX := fun _ => compo_t_eq Δ)); [ | exact (ex_intro _ eq_refl (conj H1 H2)) ].
    clear a x y H1 u v H2; intros [] [ ? [ x u ]] [ ? [ y v ]] [ H1 H2 ].
    cbn in H1; destruct H1; cbn in H2; destruct H2 as [ H1 H2 ].
    unfold it_wbisim; revert x y H1; coinduction R CIH; intros x y H1.
    apply it_wbisim_step in H1; cbn in *; unfold observe in H1; destruct H1 as [ ? ? r1 r2 rr ].
    dependent destruction rr.
    - unshelve econstructor.
      * exact (RetF (inr r0)).
      * exact (RetF (inr r3)).
      * remember (_observe x) eqn:H; clear H.
        remember (@RetF alt_ext ogs_e (fun _ => msg' Δ) (ogs_act Δ) x0 r0) eqn:H.
        apply (fun u => rew <- [ fun v => it_eat _ _ v ] H in u) in r1.
        induction r1; [ now rewrite H | eauto ].
      * remember (_observe y) eqn:H; clear H.
        remember (@RetF alt_ext ogs_e (fun _ => msg' Δ) (ogs_act Δ) x0 r3) eqn:H.
        apply (fun u => rew <- [ fun v => it_eat _ _ v ] H in u) in r2.
        induction r2; [ now rewrite H | eauto ].
      * now repeat econstructor.
    - unshelve econstructor.
      * exact (TauD (compo_alt_body (_ ,' (t1 , u)))).
      * exact (TauD (compo_alt_body (_ ,' (t2 , v)))).
      * remember (_observe x) eqn:H; clear H.
        remember (TauF t1) eqn:H.
        induction r1; [ now rewrite H | auto ].
      * remember (_observe y) eqn:H; clear H.
        remember (TauF t2) eqn:H.
        induction r2; [ now rewrite H | auto ].
      * auto.
    - unshelve econstructor.
      * exact (RetF (inl (_ ,' (u q , k1)))).
      * exact (RetF (inl (_ ,' (v q , k2)))).
      * remember (_observe x) eqn:H; clear H.
        remember (VisF q k1) eqn:H.
        induction r1; [ now rewrite H | auto ].
      * remember (_observe y) eqn:H; clear H.
        remember (VisF q k2) eqn:H.
        induction r2; [ now rewrite H | auto ].
      * unshelve (do 3 econstructor); [ exact eq_refl | exact (conj (H2 q) k_rel) ].
   Qed.

  Definition reduce_t_inj {Δ : context} (x : reduce_t Δ) : compo_alt_t Δ
     := (_ ,' (m_strat _ (fst (projT2 x)) , m_stratp _ (snd (projT2 x)))) .

  Lemma compo_compo_alt {Δ} {x : reduce_t Δ}
        : iter_delay compo_alt_body (reduce_t_inj x) ≊ iter_delay compo_body x .

    apply (iter_cong_strong (RX := fun _ a b => compo_t_eq_strong _ a (reduce_t_inj b))); cycle 1.

    cbn; destruct (reduce_t_inj x) as [ ? [] ].
    exists eq_refl; split; cbn; [ | intro r ]; reflexivity.

    intros [] [? [u1 e1]] [? [u2 e2]] [A B].
    dependent elimination A; cbn in B; destruct B as [H1 H2].
    rewrite unfold_mstrat in H1.
    unfold compo_body; cbn [fst snd projT1 projT2].
    remember (m_strat_play u2) eqn:Hu; clear Hu.
    clear u2; unfold it_eq; revert u1 d H1; coinduction R CIH; intros u1 d H1.
    apply it_eq_step in H1; cbn in *; unfold observe in *.
    destruct (_observe d).
    + destruct r as [ | [] ]; destruct (_observe u1); dependent elimination H1;
        econstructor; econstructor; eauto.
      exists eq_refl; split; [ exact (H2 q0) | exact k_rel ].
    + destruct (_observe u1); dependent elimination H1; eauto.
    + destruct q.
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
