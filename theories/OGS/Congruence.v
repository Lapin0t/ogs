(*|
Congruence (Def 6.1)
=====================

We prove in this module that weak bisimilarity is a congruence for composition. The proof
makes a slight technical side step: we prove the composition to be equivalent to an
alternate definition, dully named ``compo_alt``.

Indeed, congruence is a very easy result, demanding basically no assumption. What is
actually hard, is to manage weak bisimilarity proofs, which in contrast to strong
bisimilarity can be hard to tame: instead of synchronizing, at every step they can eat
any number of ``Tau`` node on either side, forcing us to do complex inductions in the
middle of our bisimilarity proofs.

Because of this, since our main definition ``compo`` is the specific case of composition
of two instances of the machine strategy in the OGS game, we know much more than what we
actually care about. Hence we define the much more general ``compo_alt`` composing
*any two abstract strategy* for the OGS game and prove that one congruent w.r.t. weak
bisimilarity. We then connect these two alternative definitions with a strong bisimilarity,
much more structured, hence easy to prove.

.. coq:: none
|*)
From Coinduction Require Import coinduction tactics.

From OGS Require Import Prelude.
From OGS.Utils Require Import Rel.
From OGS.Ctx Require Import All Ctx.
From OGS.OGS Require Import Subst Obs Machine Game Strategy CompGuarded.
From OGS.ITree Require Import Event ITree Eq Delay Structure Properties Guarded.

Section with_param.
(*|
We consider a language abstractly captured as a machine satisfying an
appropriate axiomatization.
|*)
  Context {T C} {CC : context T C} {CL : context_laws T C}.
  Context {val} {VM : subst_monoid val} {VML : subst_monoid_laws val}.
  Context {conf} {CM : subst_module val conf} {CML : subst_module_laws val conf}.
  Context {obs : obs_struct T C} {M : machine val conf obs}.
  Context {ML : machine_laws val conf obs} {VV : var_assumptions val}.
(*|
We start off by defining this new, *opaque* composition.
|*)
  Record compo_alt_t (Δ : C) : Type := AltT {
    alt_ctx : ogs_ctx ;
    alt_act : ogs_act (obs:=obs) Δ alt_ctx ;
    alt_pas : ogs_pas (obs:=obs) Δ alt_ctx
  } .
  #[global] Arguments AltT {Δ Φ} u v : rename.
  #[global] Arguments alt_ctx {Δ}.
  #[global] Arguments alt_act {Δ}.
  #[global] Arguments alt_pas {Δ}.

  Definition compo_alt_body {Δ}
    : compo_alt_t Δ -> delay (compo_alt_t Δ + obs∙ Δ)
    := cofix _compo_body x :=
        go match x.(alt_act).(_observe) with
            | RetF r => RetD (inr r)
            | TauF t => TauD (_compo_body (AltT t x.(alt_pas)))
            | VisF e k => RetD (inl (AltT (x.(alt_pas) e) k))
            end .

  Definition compo_alt {Δ a} (u : ogs_act Δ a) (v : ogs_pas Δ a) : delay (obs∙ Δ)
    := iter_delay compo_alt_body (AltT u v).
(*|
Now we define our bisimulation candidates, for weak and strong bisimilarity.
|*)
  Variant alt_t_weq Δ : relation (compo_alt_t Δ) :=
  | AltWEq {Φ u1 u2 v1 v2}
    : u1 ≈ u2
      -> h_pasvR ogs_hg (it_wbisim (eqᵢ _)) _ v1 v2
      -> alt_t_weq Δ (AltT (Φ:=Φ) u1 v1) (AltT (Φ:=Φ) u2 v2).

  Variant alt_t_seq Δ : relation (compo_alt_t Δ) :=
  | AltSEq {Φ u1 u2 v1 v2}
    : u1 ≊ u2
      -> h_pasvR ogs_hg (it_eq (eqᵢ _)) _ v1 v2
      -> alt_t_seq Δ (AltT (Φ:=Φ) u1 v1) (AltT (Φ:=Φ) u2 v2).
(*|
And prove the tedious but direct weak congruence.
|*)
  #[global] Instance compo_alt_proper {Δ a}
    : Proper (it_wbisim (eqᵢ _) a
                ==> h_pasvR ogs_hg (it_wbisim (eqᵢ _)) a
                ==> it_wbisim (eqᵢ _) T1_0)
        (@compo_alt Δ a).
    intros x y H1 u v H2.
    unshelve eapply (iter_weq (RX := fun _ => alt_t_weq Δ)); [ | now econstructor ].
    clear a x y H1 u v H2; intros [] ?? [ ????? Hu Hv ].
    revert u1 u2 Hu; unfold it_wbisim; coinduction R CIH; intros u1 u2 Hu.
    apply it_wbisim_step in Hu; cbn in *; unfold observe in Hu.
    destruct Hu as [ ? ? r1 r2 rr ].
    dependent destruction rr.
    - dependent destruction r_rel; unshelve econstructor.
      * exact (RetF (inr r3)).
      * exact (RetF (inr r3)).
      * remember (_observe u1) eqn:H; clear H.
        remember (RetF (E:=ogs_e) r3) eqn:H.
        induction r1; [ now rewrite H | eauto ].
      * remember (_observe u2) eqn:H; clear H.
        remember (RetF (E:=ogs_e) r3) eqn:H.
        induction r2; [ now rewrite H | eauto ].
      * now repeat econstructor.
    - unshelve econstructor.
      * exact (TauD (compo_alt_body (AltT t1 v1))).
      * exact (TauD (compo_alt_body (AltT t2 v2))).
      * remember (_observe u1) eqn:H; clear H.
        remember (TauF t1) eqn:H.
        induction r1; [ now rewrite H | auto ].
      * remember (_observe u2) eqn:H; clear H.
        remember (TauF t2) eqn:H.
        induction r2; [ now rewrite H | auto ].
      * auto.
    - unshelve econstructor.
      * exact (RetF (inl (AltT (v1 q) k1))).
      * exact (RetF (inl (AltT (v2 q) k2))).
      * remember (_observe u1) eqn:H; clear H.
        remember (VisF q k1) eqn:H.
        induction r1; [ now rewrite H | auto ].
      * remember (_observe u2) eqn:H; clear H.
        remember (VisF q k2) eqn:H.
        induction r2; [ now rewrite H | auto ].
      * unshelve (do 3 econstructor); eauto.
   Qed.
(*|
We can inject pairs of machine-strategy states into pairs of opaque states, this will help
us define our next bisimulation candidate.
|*)
  Definition reduce_t_inj {Δ} (x : reduce_t Δ) : compo_alt_t Δ
     := AltT (m_strat _ x.(red_act)) (m_stratp _ x.(red_pas)) .
(*|
Now we relate the normal composition and the opaque composition of opacified states.
|*)
  Lemma compo_compo_alt {Δ} {x : reduce_t Δ}
        : iter_delay compo_alt_body (reduce_t_inj x) ≊ iter_delay compo_body x .
  Proof.
    apply (iter_cong_strong (RX := fun _ a b => alt_t_seq _ a (reduce_t_inj b))); cycle 1.

    cbn; destruct (reduce_t_inj x) as [ Φ u v ]; econstructor; [ | intro ]; eauto.
    clear x.

    intros [] ?? H; dependent destruction H.
    destruct b as [ Φ [ c u ] v ]; cbn in *.
    rewrite unfold_mstrat in H; apply it_eq_step in H; cbn in H; unfold observe in H.
    apply it_eq_unstep; cbn.
    remember (_observe u1) as ou1; clear u1 Heqou1.
    remember (_observe (eval c)) as ou2; clear c Heqou2.
    
    destruct ou2.
    - destruct (m_strat_wrap u r).
      + cbn in H; dependent elimination H; cbn.
        do 2 econstructor; exact r_rel.
      + destruct h; cbn in H; dependent elimination H.
        do 3 econstructor.
        * apply H0.
        * exact k_rel.
    - destruct ou1; dependent elimination H.
      econstructor.
      remember (fmap_delay (m_strat_wrap u) t) as t2; clear u t Heqt2.
      revert t1 t2 t_rel; unfold it_eq at 2; coinduction R CIH; intros t1 t2 t_rel.
      apply it_eq_step in t_rel; cbn in t_rel; unfold observe in t_rel; cbn.
      remember (_observe t1) as ot1; clear t1 Heqot1.
      remember (_observe t2) as ot2; clear t2 Heqot2.
      destruct ot2.
      + destruct r.
        * cbn in t_rel; dependent elimination t_rel; cbn.
          do 2 econstructor; exact r_rel.
        * destruct h; dependent elimination t_rel; cbn.
          do 3 econstructor.
          now apply H0.
          exact k_rel.
      + dependent elimination t_rel; econstructor.
        now apply CIH.
      + destruct q.
    - destruct q.
  Qed.
End with_param.
