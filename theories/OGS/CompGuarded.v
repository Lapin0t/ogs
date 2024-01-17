From OGS Require Import Prelude.
From OGS.Utils Require Import Ctx Rel.
From OGS.Game Require Import HalfGame Event.
From OGS.OGS Require Import Subst Obs Machine Game Strategy Utility_lemmas.
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
A central elements in the proof lies in ensuring that there exists a unique solution
to [compo_body]. Since the composition of strategies is defined as such a solution,
adequacy can be established by proving that evaluating and observing the substituted
term.

By [iter_evg_uniq], we know that eventually guarded equations admit a unique fixed point:
we hence start by proving this eventual guardedness, captured in lemma [compo_body_guarded].
|*)

  Equations var_depth (Ψ : alt_ext) b {x} (j : ↓[b] Ψ ∋ x) : nat by struct Ψ :=
    var_depth ∅%ctx        _     (!) ;
    var_depth (Ψ ▶ Γ)%ctx true  i := aux Γ i
      where aux (Γ1 : context) {x1} (i : (↓⁻ Ψ +▶ Γ1) ∋ x1) : nat by struct Γ1 := {
        aux ∅%ctx         i1           := Datatypes.S (var_depth Ψ _ i1) ;
        aux (Γ1 ▶ _)%ctx (Ctx.top)    := Datatypes.O ;
        aux (Γ1 ▶ _)%ctx (Ctx.pop i1) := aux Γ1 i1
      } ;
    var_depth (Ψ ▶ Γ)%ctx false i := Datatypes.S (var_depth Ψ _ i).
  Arguments var_depth {Ψ b x} j.

  Lemma var_depth_ext {Ψ Γ x} (j : ↓⁻ Ψ ∋ x) :
    @var_depth (Ψ ▶ Γ) true x (r_concat_l x j) = Datatypes.S (var_depth j) .
  Proof.
    cbn.
    pose (t' := r_concat_l (Δ:=Γ) x j); change (r_concat_l x j) with t' at 1.
    pose (x' := x); change x with x' at 1; change x with x' in t'.
    pose (Γ' := Γ); change Γ with Γ' at 1; change Γ with Γ' in t'.
    remember t' as t_; clear Heqt_ t'.
    remember x' as x_; clear Heqx_ x'.
    remember Γ' as Γ_; clear HeqΓ_ Γ'.
    revert x_ Γ_ t_; induction Γ; intros x_ Γ_ t_; cbn.
    now rewrite r_cover_l_nil.
    now apply IHΓ.
  Qed.

  Definition var_height {Ψ : alt_ext} {b x} (j : ↓[b] Ψ ∋ x) : nat :=
    Nat.sub (c_length Ψ) (var_depth j) .

  Lemma var_depth_le {Ψ : alt_ext} {b x} (j : ↓[b] Ψ ∋ x) : (var_depth j <= c_length Ψ)%nat.
  Proof.
    revert b j; induction Ψ; intros b j; [ inversion j | ].
    destruct b; cbn in *; [ | apply le_n_S, IHΨ ].
    induction x0; [ apply le_n_S, IHΨ | ].
    dependent elimination j; [ now apply le_0_n | now apply IHx0 ].
  Qed.

  Lemma depth_increases {Δ Ψ b} (v : alt_env Δ Δ b Ψ) {x} (j : ↓[negb b] Ψ ∋ x) (k : ↓[b] Ψ ∋ x)
    (H : concat0 v x j = v_var x (r_concat_r x k)) : var_depth j < var_depth k.
  Proof.
    revert b v x j k H; induction Ψ; intros b v t j k H; [ inversion j | ].
    destruct b; cbn in *.
    - pose (k' := k); change k with k' at 1.
      pose (x' := x); change x with x' at 1; change x with x' in k'.
      pose (t' := t); change t with t' at 2; change t with t' in k'.
      remember k' as k_; clear Heqk_ k'.
      remember x' as x_; clear Heqx_ x'.
      remember t' as t_; clear Heqt_ t'.
      revert x_ t_ k_; induction x; intros x_ t_ k_.
      * apply le_n_S.
        (* dependent elimination v. *)
        depelim v.
        refine (IHΨ _ v _ j k _).
        assert (H2 : @r_concat3_1 typ Δ ↓⁻ Ψ ∅ ≡ₐ r_id)
          by (apply s_eq_cover_uniq; [ reflexivity | cbn; now rewrite r_cover_l_nil ]).
        cbn in H; unfold e_ren in H.
        unshelve erewrite (e_comp_proper _ v_var _ _ (concat0 v)) in H;
          [ | now rewrite v_var_sub in H | reflexivity ].
        etransitivity; [ apply s_ren_proper | apply s_ren_id ]; auto.
      * depelim v; dependent elimination k; cbn in *.
        (* dependent elimination v; dependent elimination k; cbn in *. *)
      + pose (H' := (_ ,' H) : is_var _).
        assert (Heq : is_var_get H' = Ctx.top) by reflexivity.
        remember H' as H1; clear H' H HeqH1.
        change ((?u ᵣ⊛ concat0 v) x1 j) with (u ᵣ⊛ᵥ concat0 v x1 j) in H1.
        destruct (view_is_var_ren (concat0 v x1 j) _ H1); cbn in Heq.
        destruct (cat_split (is_var_get p)).
        ++ change (?u x1 _) with ((u ⊛ᵣ r_concat_l) _ i) in Heq.
           unfold r_concat3_1 in Heq; rewrite s_eq_cat_l in Heq.
           cbn in Heq; unfold s_ren, s_map, r_pop in Heq; inversion Heq.
        ++ change (?u x1 _) with ((u ⊛ᵣ r_concat_r) _ j0) in Heq.
           unfold r_concat3_1 in Heq; rewrite s_eq_cat_r in Heq.
           cbn in Heq; unfold s_ren, s_map, r_pop in Heq; inversion Heq.
      + apply (IHx (v ▶ₑ⁺) h); cbn.
        pose (H' := (_ ,' H) : is_var _).
        assert (Heq : is_var_get H' = (r_pop ⊛ᵣ r_cover_r cover_cat) x2 h) by reflexivity.
        remember H' as H1; clear H' H HeqH1.
        change ((?u ᵣ⊛ concat0 v) x2 j) with (u ᵣ⊛ᵥ concat0 v x2 j) in H1.
        destruct (view_is_var_ren (concat0 v x2 j) _ H1).
        destruct p; cbn in *.
        unfold e_ren, e_comp, s_map; rewrite e, v_sub_id; unfold s_ren, s_map.
        destruct (cat_split x0).
        ++ change (r_concat3_1 x2 _) with ((@r_concat3_1 _ _ ↓⁻ Ψ (x ▶ y) ⊛ᵣ r_concat_l) x2 i) in Heq.
           unfold r_concat3_1 in Heq; rewrite s_eq_cat_l in Heq.
           change (r_concat3_1 x2 _) with ((@r_concat3_1 _ _ ↓⁻ Ψ x ⊛ᵣ r_concat_l) x2 i).
           unfold r_concat3_1; rewrite s_eq_cat_l; unfold r_concat_l.
           cbn in Heq; unfold r_pop, s_ren, s_map in Heq.
           remember (@r_cover_l _ _ _ (Δ +▶ (↓⁻ Ψ +▶ x)) cover_cat x2 i).
           remember (@r_cover_r _ _ _ (Δ +▶ (↓⁻ Ψ +▶ x)) cover_cat x2 h).
           clear -Heq; now dependent induction Heq.
        ++ change (r_concat3_1 x2 _) with ((@r_concat3_1 _ Δ _ (x ▶ y) ⊛ᵣ r_concat_r) x2 j0) in Heq.
           unfold r_concat3_1 in Heq; rewrite s_eq_cat_r in Heq.
           change (r_concat3_1 x2 _) with ((@r_concat3_1 _ Δ _ x ⊛ᵣ r_concat_r) x2 j0).
           unfold r_concat3_1; rewrite s_eq_cat_r; unfold r_concat_l.
           cbn in Heq; unfold r_pop, s_ren, s_map in Heq.
           unfold s_ren, s_map, r_concat_r.
           remember ((@r_cover_r _ _ _ (Δ +▶ (↓⁻ Ψ +▶ x)) cover_cat x2 (r_concat_l x2 j0))).
           remember ((@r_cover_r _ _ _ (Δ +▶ (↓⁻ Ψ +▶ x)) cover_cat x2 (@r_cover_l _ _ _ (↓⁻ Ψ +▶ x) cover_cat x2 j0))).
           clear -Heq; now dependent induction Heq.
    - pose (j' := j); change j with j' at 1.
      pose (x' := x); change x with x' at 1; change x with x' in j'.
      pose (t' := t); change t with t' at 1; change t with t' in j'.
      remember j' as j_; clear Heqj_ j'.
      remember x' as x_; clear Heqx_ x'.
      remember t' as t_; clear Heqt_ t'.
      revert x_ t_ j_; induction x; intros x_ t_ j_.
      * apply le_n_S.
        depelim v.
        (* dependent elimination v. *)
        refine (IHΨ _ v _ j k _).
        cbn in H; unfold s_cat, s_cover in H.
        destruct (cover_split cover_cat j); [ | inversion j ].
        cbn; rewrite r_cover_l_nil; exact H.
      * dependent elimination j; [ apply PeanoNat.Nat.lt_0_succ | ].
        depelim v; cbn.
        (* dependent elimination v; cbn. *)
        eapply (IHx (v ▶ₑ⁻ (a ⊛ᵣ r_pop))); cbn in *.
        rewrite <- H.
        change (([ ?u , a ]) x2 (pop h)) with (([ u , a ] ⊛ᵣ r_pop) x2 h).
        apply s_eq_cover_uniq; rewrite <- s_ren_comp.
      + change (r_pop ⊛ᵣ r_cover_l cover_cat) with (@r_cover_l _ _ _ (↓⁻ Ψ +▶ x ▶ y) cover_cat).
        now rewrite s_eq_cat_l.
      + change (r_pop ⊛ᵣ r_cover_r cover_cat) with (@r_cover_r _ _ _ (↓⁻ Ψ +▶ x ▶ y) cover_cat ⊛ᵣ r_pop).
        now rewrite s_ren_comp, s_eq_cat_r.
  Qed.

  Lemma compo_body_guarded_aux
    {Δ Ψ} (u : alt_env Δ Δ Ⓟ Ψ) (v : alt_env Δ Δ Ⓞ Ψ)
    {x} (o : obs x) (γ : dom o ⇒ᵥ (Δ +▶ ↓⁺ Ψ)) (j : ↓⁺ Ψ ∋ x) :
    ev_guarded (fun 'T1_0 => compo_body (Δ := Δ))
        (compo_body
           ((Ψ ▶ dom o),' (app (r_concat3_1 ᵣ⊛ᵥ concat0 v x j) o ((v_var ⊛ᵣ r_concat_r) ⊛ᵣ r_concat_r), v ▶ₑ⁺, u ▶ₑ⁻ γ))) .
  Proof.
    pose (o' := (x ,' o)).
    revert γ j.
    change x with (projT1 o').
    change o with (projT2 o').
    remember o' as o''; clear o' o x Heqo''; rename o'' into o.
    pose (wf := eval_app_not_var o).

    revert Ψ u v; induction wf; intros Ψ u v γ j.
    destruct x as [ x m ]; cbn [projT1 projT2] in *.

    pose (h := lt_wf (var_height j)); remember (var_height j) as n.
    revert Ψ u v γ j Heqn; induction h; intros Ψ u v γ j Heqn.

    unfold ev_guarded; cbn -[cat_split].

    pose (vv := @r_concat3_1 typ Δ ↓⁻ Ψ (@dom _ _ x m) ᵣ⊛ᵥ concat0 v x j).
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
      unfold m_strat_wrap; unfold obs' in a'; unfold obs'_of_nf', nf'_ty, nf'_var, nf'_obs in *; cbn [ fst snd projT1 projT2] in *.
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
        unfold obs'_dom, m_strat_resp; cbn [fst snd projT1 projT2].
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
      destruct r as [ x' [ j' [ m' a' ]]]. unfold nf'_obs, nf'_val in *. cbn [ fst snd projT1 projT2 ].
      pose (uu := cat_split j'); change (cat_split j') with uu; destruct uu.
      now do 2 econstructor.
      refine (GNext _).
      unfold obs'_dom, obs'_obs; cbn [fst snd projT1 projT2].
      eapply (H0 (x' ,' m')).
      econstructor.
      exact f.
      apply it_eq_unstep; cbn.
      rewrite Heqt in Heqot.
      rewrite <- Heqot.
      econstructor; reflexivity.
  Qed.

  Lemma compo_body_guarded {Δ} : eqn_ev_guarded (fun 'T1_0 => compo_body (Δ := Δ)).
  Proof.
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

  Definition compo_ev_guarded {Δ a} (u : m_strat_act Δ a) (v : m_strat_pas Δ a) : delay (obs∙ Δ) :=
    iter_ev_guarded _ compo_body_guarded T1_0 (a ,' (u , v)).

End withFam.

Notation "u ∥g v" := (compo_ev_guarded u v) (at level 40).



