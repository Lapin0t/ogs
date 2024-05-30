(*|
Eventual guardedness of the composition
=======================================

We want to prove adequacy by unicity of solutions to the set of equations defining the
composition. To do so, we rely on the notion of guarded iteration introduced in
`ITree/Guarded.v <Guarded.html>`_. Through this file, we prove that the composition is
indeed eventually guarded. As described in §6.3, the proof relies crucially on the
``eval_app_not_var`` assumption (Def 6.21).

.. coq:: none
|*)
From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.
From OGS.Ctx Require Import All Ctx.
From OGS.OGS Require Import Subst Obs Machine Game Strategy.
From OGS.ITree Require Import Event ITree Eq Delay Structure Properties Guarded.

Require Import Coq.Arith.PeanoNat.

Section with_param.
(*|
We consider a language abstractly captured as a machine satisfying an
appropriate axiomatization.
|*)
  Context `{CC : context T C} {CL : context_laws T C}.
  Context {val} {VM : subst_monoid val} {VML : subst_monoid_laws val}.
  Context {conf} {CM : subst_module val conf} {CML : subst_module_laws val conf}.
  Context {obs : obs_struct T C} {M : machine val conf obs}.
  Context {ML : machine_laws val conf obs} {VV : var_assumptions val}.

  Notation ogs_ctx := (ogs_ctx (C:=C)).
(*|
A central elements in the proof lies in ensuring that there exists a unique solution
to ``compo_body``. Since the composition of strategies is defined as such a solution,
adequacy can be established by proving that evaluating and observing the substituted
term is also a solution of ``compo_body``.

By ``iter_evg_uniq``, we know that eventually guarded equations admit a unique fixed point:
we hence start by proving this eventual guardedness, captured in lemma
``compo_body_guarded``.

This proof will among other be using an induction on the *age* of a variable, ie it's
height in the OGS position Φ. We provide this definition and utilities.
|*)
  Equations var_height Φ p {x} : ↓[p]Φ ∋ x -> nat :=
    var_height ∅ₓ       Pas i with c_view_emp i := { | ! } ;
    var_height ∅ₓ       Act i with c_view_emp i := { | ! } ;
    var_height (Φ ▶ₓ Γ) Pas i := var_height Φ Act i ;
    var_height (Φ ▶ₓ Γ) Act i with c_view_cat i := {
      | Vcat_l j := var_height Φ Pas j ;
      | Vcat_r j := 1 + c_length Φ } .
  #[global] Arguments var_height {Φ p x} i.

  Lemma var_height_pos {Φ p x} (i : ↓[p]Φ ∋ x) : 0 < var_height i .
  Proof.
    funelim (var_height i).
    - apply H.
    - rewrite <- Heqcall; apply H.
    - rewrite <- Heqcall; apply Nat.lt_0_succ.
  Qed.

  Equations lt_bound : polarity -> relation nat :=
    lt_bound Act := lt ;
    lt_bound Pas := le .

  Lemma var_height_bound {Φ p x} (i : ↓[p]Φ ∋ x)
    : lt_bound p (var_height i) (1 + c_length Φ).
  Proof.
    funelim (var_height i); cbn.
    - now apply Nat.lt_succ_r, Nat.le_le_succ_r, Nat.le_le_succ_r.
    - rewrite Heq; now apply Nat.lt_succ_r.
    - rewrite Heq; apply Nat.lt_succ_diag_r.
  Qed.

  Equations var_height' {Δ Φ p x} : Δ +▶ ↓[p]Φ ∋ x -> nat :=
    var_height' i with c_view_cat i := {
      | Vcat_l j := O ;
      | Vcat_r j := var_height j } .
(*|
This is the main theorem about height: if we lookup a variable in an OGS environment and
obtain another variable, then this new variable is strictly lower than the first one.
|*)
  Lemma height_decrease {Δ Φ p} (v : ogs_env Δ p Φ) {x}
        (j : ↓[p^] Φ ∋ x)
        (H :  is_var (ₐ↓v _ j))
        : var_height' (is_var_get H) < var_height j.
  Proof.
    revert H; rewrite lookup_collapse; intro H.
    destruct (view_is_var_ren _ _ H).
    rewrite ren_is_var_get; cbn.
    remember (lookup v j).
    destruct H; cbn; destruct (c_view_cat i).
    - unfold var_height'; rewrite c_view_cat_simpl_l; apply var_height_pos.
    - unfold var_height'; rewrite c_view_cat_simpl_r; cbn.
      remember (r_ctx_dom j).
      funelim (r_ctx_dom j); try clear Heqcall.
      + cbn; rewrite c_view_cat_simpl_l; cbn.
        dependent destruction v; now apply (H _ v).
      + dependent destruction v.
        revert j1 Heqv0; cbn; rewrite Heq; cbn; intros j1 Heqv.
        now apply (H _ v).
      + dependent destruction v; clear Heqv0.
        revert j1; cbn; rewrite Heq; exact var_height_bound.
  Qed.
(*|
We are now ready to prove eventual guardedness. In fact the main lemma will have a slightly
different statement, considering a particular kind of pair of OGS states: the ones we
obtain when restarting after an interaction. As the statement is quite long we factor
it in a definition first.
|*)
  Definition compo_body_guarded_aux_stmt {Δ Φ} (u : ogs_env Δ Act Φ) (v : ogs_env Δ Pas Φ)
    {x} (o : obs x) (γ : dom o =[val]> (Δ +▶ ↓⁺ Φ)) (j : ↓⁺ Φ ∋ x) : Prop
    := ev_guarded
         (fun 'T1_0 => compo_body)
         (compo_body (RedT (MS ((ₐ↓v _ j ᵥ⊛ᵣ r_cat3_1) ⊙ o⦗r_cat_rr ᵣ⊛ a_id⦘)
                               (v ;⁺))
                           (u ;⁻ γ))) .
(*|
Now the main proof.
|*)
  Lemma compo_body_guarded_aux
    {Δ Φ} (u : ogs_env Δ Act Φ) (v : ogs_env Δ Pas Φ)
    {x} (o : obs x) γ j : compo_body_guarded_aux_stmt u v o γ j .
  Proof.
(*|
First we setup an induction on the accessibility of the current observation in the relation
given by the "no-infinite redex" property.
|*)
    revert Φ u v γ j.
    pose (o' := (x ,' o)); change x with (projT1 o'); change o with (projT2 o').
    generalize o'; clear x o o'; intro o.
    pose (wf := eval_app_not_var o); induction wf.
    destruct x as [ x o ]; cbn [ projT1 projT2 ] in *.
    clear H; rename H0 into IHred; intros Φ u v γ j.
(*|
Next we setup an induction on the height of the current variable we have restarted on.
|*)
    pose (h := lt_wf (var_height j)); remember (var_height j) as n.
    revert Φ u v γ j Heqn; induction h.
    clear H; rename x0 into n, H0 into IHvar; intros Φ u v γ j Heqn.
(*|
Then we case split on whether ``ₐ↓ v x j`` is a variable or not.
|*)
    unfold compo_body_guarded_aux_stmt.
    pose (vv := ₐ↓ v x j); fold vv.
    destruct (is_var_dec vv).
(*|
Case 1: it is a variable.

First, some shenenigans to extract the variable.
|*)
    - rewrite (is_var_get_eq i); unfold vv in *; clear vv.
      unfold v_ren; rewrite v_sub_var; unfold r_emb.
      unfold ev_guarded; cbn.
(*|
Next, we are evaluating a normal form, so we know by hypothesis ``eval_nf_ret`` that it
will reduce to the same normal form. We need some trickery to rewrite by this bisimilarity.
|*)
      pose proof (Heval :=
                    eval_nf_ret ((r_cat3_1 x (is_var_get i)) ⋅ o ⦇ r_cat_rr ᵣ⊛ a_id  ⦈)).
      unfold comp_eq in Heval; apply it_eq_step in Heval.
      change (eval _) with
        (eval (a_id (r_cat3_1 x (is_var_get i)) ⊙ o ⦗ r_cat_rr ᵣ⊛ a_id ⦘))
        in Heval.
      remember (eval (a_id (r_cat3_1 x (is_var_get i)) ⊙ o ⦗ r_cat_rr ᵣ⊛ a_id ⦘))
        as tt; clear Heqtt.
      remember (r_cat3_1 x (is_var_get i) ⋅ o ⦇ r_cat_rr ᵣ⊛ a_id ⦈) as ttn.
      cbn in Heval; dependent destruction Heval.
      rewrite Heqttn in r_rel; clear Heqttn.
      dependent elimination r_rel.
      unfold observe in x; rewrite <- x; clear x; cbn.
      unfold m_strat_wrap, r_cat3_1; cbn.
      remember (ₐ↓v _ j) as vv.
(*|
Now, we case split to see whether this variable was a final variable or one given by
the opponent.
|*)
      destruct i; cbn; destruct (c_view_cat i).
(*|
In case of a final variable the composition is ended, hence guarded, hence eventually
guarded.
|*)
      + rewrite c_view_cat_simpl_l; now do 2 econstructor.
(*|
In the other case, there is an interaction. Since we have looked-up a variable and
obtained another variable, we know it is strictly older and use our induction hypothesis
on the height of the current variable.
|*)
      + rewrite c_view_cat_simpl_r; cbn.
        refine (GNext _).
        unshelve refine (IHvar _ _ _ _ _ _ _ eq_refl).
        rewrite Heqn; clear Heqn; unfold cut_l.
(*|
There is some trickery to apply ``height_decrease``.
|*)
        clear tt ttn a1 a.
        assert (i : is_var (ₐ↓v _ j)).
          rewrite <- Heqvv.
          now econstructor.
        eapply Nat.lt_le_trans; [ | exact (height_decrease (p:=Pas) _ j i) ].
        destruct i; cbn.
        apply v_var_inj in Heqvv.
        rewrite <- Heqvv; unfold var_height'.
        rewrite c_view_cat_simpl_l, c_view_cat_simpl_r; cbn.
        now apply Nat.lt_succ_diag_r.
(*|
Case 2: the looked-up value is not a variable. In this case we look at one step of the
evaluation. If there is a redex we are happy. Else, our resumed configuration was
still a normal form and we can exhibit a proof of the bad instanciation relation, which
enables us to call our other induction hypothesis.
|*)
    - unfold ev_guarded; cbn.
      remember (eval ((vv ᵥ⊛ r_emb r_cat3_1) ⊙ o ⦗ r_cat_rr ᵣ⊛ a_id ⦘)) as tt.
      remember (_observe tt) as ot.
      destruct ot; try now do 2 econstructor.
      destruct r as [ nx ni [ no narg ] ]; unfold m_strat_wrap; cbn.
      destruct (c_view_cat ni); try now do 2 econstructor.
      refine (GNext (IHred (_ ,' _) _ _ _ _ _ _)).

      refine (HeadInst (_ ,' _) (vv ᵥ⊛ r_emb r_cat3_1) o
                (r_cat_rr ᵣ⊛ a_id) (r_cat_r j0) (t ∘ (is_var_ren _ _)) _).
      apply it_eq_unstep; cbn.
      rewrite Heqtt in Heqot; rewrite <- Heqot.
      now econstructor.
  Qed.
(*|
Now the actual proof of eventual guardedness is just about unfolding a bit of the beginning
of the interactions until we attain a resume and can apply our main lemma.
|*)
  Lemma compo_body_guarded {Δ} : eqn_ev_guarded (fun 'T1_0 => compo_body (Δ := Δ)).
  Proof.
    intros [] [ Γ [ c u ] v ]; unfold m_strat_pas in v.
    unfold ev_guarded; cbn.
    pose (ot := _observe (eval c)); change (_observe (eval c)) with ot.
    destruct ot; try now do 2 econstructor.
    destruct r as [ x i [ o a ] ]; unfold m_strat_wrap; cbn.
    destruct (c_view_cat i); try now do 2 econstructor.
    refine (GNext _); apply compo_body_guarded_aux.
  Qed.
(*|
From the previous proof we can directly apply the strong fixed point construction on
eventually guarded equations and obtain a composition operator without any ``Tau`` node
at interaction points.
|*)
  Definition compo_ev_guarded {Δ a} (u : m_strat_act Δ a) (v : m_strat_pas Δ a)
    : delay (obs∙ Δ)
    := iter_ev_guarded _ compo_body_guarded T1_0 (RedT u v).

End with_param.
#[global] Notation "u ∥g v" := (compo_ev_guarded u v) (at level 40).



