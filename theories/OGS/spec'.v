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
