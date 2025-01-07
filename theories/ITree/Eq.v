(*|
Interaction Trees: (weak) bisimilarity
=======================================

As is usual with coinductive types in Coq, `eq` is not the *right* notion of equivalence.
We define through this file strong and weak bisimilarity of itrees, and their
generalization lifting value relations.

These coinductive relations are implemented using Damien Pous's coinduction_ library.
Indeed, our previous coinductive definitions like ``itree`` where implemented using Coq's
native coinductive types, but their manipulation is a bit brittle due to the syntactic
guardedness criterion. For the case of bisimilarity---which is also a coinductive types---
we have better tools. Indeed bisimilarity is a ``Prop``-valued relation, and since Coq's
``Prop`` universe feature impredicativity, the set of ``Prop``-valued relation enjoy the
structure of a complete lattice. This enables us to derive greatest fixpoints ourselves,
using an off-the-shelf fixpoint construction on complete lattices.

The version of coinduction_ we use constructs greatest fixpoints using the "companion"
construction, enjoying good properties w.r.t. up-to techniques: we will be able to
discharge bisimilarity proof by providing less than a full-blown bisimulation relation.
Since the time of writing, the library has been upgraded to an even more practical
construction based on tower-induction, but we have not yet ported our code to this
upgraded API.

.. _coinduction: https://github.com/damien-pous/coinduction

.. coq:: none
|*)
Require Import Coq.Program.Equality.
From Coinduction Require Import lattice rel coinduction tactics.

From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.
From OGS.ITree Require Import Event ITree.
(*|
Strong bisimilarity
-------------------

Strong bisimilarity is very useful as it is the natural notion of extensional
equality for coinductive types. Here we introduce ``it_eq RR``, a slight generalization
where the relation on the leaves of the tree does not need to be equality on the type
of the leaves, but only a proof of the relation ``RR``, which might be heterogeneous. This
might be described as the relational lifting of itree arising from strong bisimilarity.

We will write ``≅`` for strong bisimilarity, aka ``it_eq (eqᵢ _)``.

First, we define a monotone endofunction ``it_eq_map`` over indexed relations between
trees. Strong bisimilarity is then defined the greatest fixpoint of ``it_eq_map RR``,
for a fixed value relation ``RR``.
|*)
Variant it_eqF {I} E
  {X1 X2} (RX : relᵢ X1 X2) {Y1 Y2} (RR : relᵢ Y1 Y2)
  (i : I) : itreeF E X1 Y1 i -> itreeF E X2 Y2 i -> Prop :=
| EqRet {r1 r2} (r_rel : RX i r1 r2)                : it_eqF _ _ _ _ (RetF r1)   (RetF r2)
| EqTau {t1 t2} (t_rel : RR i t1 t2)                : it_eqF _ _ _ _ (TauF t1)   (TauF t2)
| EqVis {q k1 k2} (k_rel : forall r, RR _ (k1 r) (k2 r)) : it_eqF _ _ _ _ (VisF q k1) (VisF q k2)
.
(*|
.. coq:: none
|*)
#[global] Hint Constructors it_eqF : core.
#[global] Arguments EqRet {I E X1 X2 RX Y1 Y2 RR i r1 r2}.
#[global] Arguments EqTau {I E X1 X2 RX Y1 Y2 RR i t1 t2}.
#[global] Arguments EqVis {I E X1 X2 RX Y1 Y2 RR i q k1 k2}.
(*||*)
Equations it_eqF_mon {I E X1 X2 RX Y1 Y2}
  : Proper (leq ==> leq) (@it_eqF I E X1 X2 RX Y1 Y2) :=
  it_eqF_mon _ _ H1 _ _ _ (EqRet r_rel) := EqRet r_rel ;
  it_eqF_mon _ _ H1 _ _ _ (EqTau t_rel) := EqTau (H1 _ _ _ t_rel) ;
  it_eqF_mon _ _ H1 _ _ _ (EqVis k_rel) := EqVis (fun r => H1 _ _ _ (k_rel r)) .
#[global] Existing Instance it_eqF_mon.

Definition it_eq_map {I} E {X1 X2} RX : mon (relᵢ (@itree I E X1) (@itree I E X2)) := {|
  body RR i x y := it_eqF E RX RR i (observe x) (observe y) ;
  Hbody _ _ H _ _ _ r := it_eqF_mon _ _ H _ _ _ r ;
|}.
(*|
Now the definition of the bisimilarity itself as greatest fixed point. See Def. 10.

.. coq::
   :name: sbisim
|*)
Definition it_eq {I E X1 X2} RX [i] := gfp (@it_eq_map I E X1 X2 RX) i.
#[global] Notation it_eq_t E RX := (t (it_eq_map E RX)).
#[global] Notation it_eq_bt E RX := (bt (it_eq_map E RX)).
#[global] Notation it_eq_T E RX := (T (it_eq_map E RX)).
#[global] Notation "a ≊ b" := (it_eq (eqᵢ _) a b) (at level 20).
(*|
Basic properties
^^^^^^^^^^^^^^^^
|*)
Definition it_eq' {I E X1 X2} RX [i]
  := @it_eqF I E X1 X2 RX (itree E X1) (itree E X2) (it_eq RX) i.

Definition it_eq_step {I E X1 X2 RX} : it_eq RX <= @it_eq_map I E X1 X2 RX (it_eq RX)
  := fun i x y => proj1 (gfp_fp (it_eq_map E RX) i x y) .

Definition it_eq_unstep {I E X1 X2 RX} : @it_eq_map I E X1 X2 RX (it_eq RX) <= it_eq RX
  := fun i x y => proj2 (gfp_fp (it_eq_map E RX) i x y) .

#[global] Instance it_eqbt_mon {I} {E : event I I} {X1 X2} {RX : relᵢ X1 X2}
  : Proper (leq ==> leq) (it_eq_bt E RX).
Proof.
  intros R1 R2 H i x y. apply it_eqF_mon. rewrite H. reflexivity.
Qed.
(*|
Justifying strong bisimulations up-to reflexivity, symmetry, and transitivity.
|*)
Section it_eq_facts.
  Context {I} {E : event I I} {X : psh I} {RX : relᵢ X X}.
(*|
Reversal, symmetry.
|*)
  Lemma it_eqF_sym `{Symmetricᵢ RX} {Y1 Y2} {RR : relᵢ Y1 Y2} : revᵢ (it_eqF E RX RR) <= it_eqF E RX (revᵢ RR).
    intros ? ? ? p; cbn in *; destruct p; try symmetry in r_rel; auto.
  Qed.

  Lemma it_eq_up2sym `{Symmetricᵢ RX} : converseᵢ <= it_eq_t E RX.
  Proof. apply leq_t; repeat intro; now apply it_eqF_sym. Qed.

  #[global] Instance it_eq_t_sym `{Symmetricᵢ RX} {RR} : Symmetricᵢ (it_eq_t E RX RR).
  Proof. apply build_symmetric, (ft_t it_eq_up2sym RR). Qed.
(*|
Reflexivity.
|*)
  Lemma it_eqF_rfl `{Reflexiveᵢ RX} {Y} : eqᵢ _ <= it_eqF E RX (eqᵢ Y).
  Proof. intros ? [] ? <-; auto. Qed.

  Lemma it_eq_up2rfl `{Reflexiveᵢ RX} : const (eqᵢ _) <= it_eq_t E RX.
  Proof. apply leq_t; repeat intro; now apply (it_eqF_rfl), (f_equal observe). Qed.

  #[global] Instance it_eq_t_refl `{Reflexiveᵢ RX} {RR} : Reflexiveᵢ (it_eq_t E RX RR).
  Proof. apply build_reflexive, (ft_t it_eq_up2rfl RR). Qed.
(*|
Concatenation, transitivity.
|*)
  Lemma it_eqF_tra `{Transitiveᵢ RX} {Y1 Y2 Y3} {R1 : relᵢ Y1 Y2}  {R2 : relᵢ Y2 Y3}
        : (it_eqF E RX R1 ⨟ it_eqF E RX R2) <= it_eqF E RX (R1 ⨟ R2).
  Proof.
    intros ? ? ? [ ? [ u v ] ].
    destruct u; dependent destruction v; simpl_depind; eauto.
    econstructor; transitivity r2; auto.
  Qed.

  Lemma it_eq_up2tra `{Transitiveᵢ RX} : squareᵢ <= it_eq_t E RX.
  Proof.
    apply leq_t; intros ? ? ? ? []; cbn in *.
    apply it_eqF_tra; eauto.
  Qed.

  #[global] Instance it_eq_t_trans `{Transitiveᵢ RX} {RR} : Transitiveᵢ (it_eq_t E RX RR).
  Proof. apply build_transitive, (ft_t it_eq_up2tra RR). Qed.
(*|
We can now package the previous properties as equivalences.
|*)
  #[global] Instance it_eq_t_equiv `{Equivalenceᵢ RX} {RR}
    : Equivalenceᵢ (it_eq_t E RX RR).
  Proof. econstructor; typeclasses eauto. Qed.

  #[global] Instance it_eq_bt_equiv `{Equivalenceᵢ RX} {RR}
    : Equivalenceᵢ (it_eq_bt E RX RR).
  Proof.
    apply build_equivalence.
    - apply (fbt_bt it_eq_up2rfl).
    - apply (fbt_bt it_eq_up2sym).
    - apply (fbt_bt it_eq_up2tra).
   Qed.

  #[global] Instance it_eq_t_bt {RR} : Subrelationᵢ (it_eq RX) (it_eq_bt E RX RR).
  Proof.
    intros ? ? ? r.
    apply (gfp_fp (it_eq_map E RX)) in r.
    cbn in *.
    dependent induction r; simpl_depind; auto.
    - econstructor; apply (gfp_t (it_eq_map E RX)); auto.
    - econstructor; intro r; apply (gfp_t (it_eq_map E RX)); auto.
  Qed.

End it_eq_facts.
(*|
Weak bisimilarity
-----------------

Similarly to strong bisimilarity, we define weak bisimilarity as the greatest fixpoint
of a monotone endofunction. A characteristic of weak bisimilarity is that it can
"skip over" a finite number of ``Tau`` nodes on either side. As such, the endofunction
will allow "eating" a number of ``Tau`` nodes before a synchronization step.

Note that ``itree`` encodes deterministic LTSs, hence we do not need to worry about
allowing to strip off ``Tau`` nodes after the synchronization as well.

We will start by defining an inductive "eating" relation, such that intuitively
``it_eat X Y := ∃ n, X = Tau^n(Y)``.

.. coq::
   :name: eat
|*)
Section it_eat.
  Context {I : Type} {E : event I I} {R : psh I}.

  Inductive it_eat i : itree' E R i -> itree' E R i -> Prop :=
  | EatRefl {t} : it_eat i t t
  | EatStep {t1 t2} : it_eat _ (observe t1) t2 -> it_eat i (TauF t1) t2
  .
(*|
.. coq:: none
|*)
  Hint Constructors it_eat : core.
  Arguments EatRefl {i t}.
  Arguments EatStep {i t1 t2} p.
(*|
Let's prove some easy properties.
|*)
  #[global] Instance eat_trans : Transitiveᵢ it_eat.
  Proof.
    intros i x y z r1 r2; dependent induction r1; auto.
  Defined.

  Equations eat_cmp : (revᵢ it_eat ⨟ it_eat) <= (it_eat ∨ᵢ revᵢ it_eat) :=
    eat_cmp i' x' y' (ex_intro _ z' (conj p' q')) := _eat_cmp p' q'
  where _eat_cmp {i x y z}
        : it_eat i x y -> it_eat i x z -> (it_eat i y z \/ it_eat i z y) :=
    _eat_cmp (EatRefl)   q           := or_introl q ;
    _eat_cmp p           (EatRefl)   := or_intror p ;
    _eat_cmp (EatStep p) (EatStep q) := _eat_cmp p q .

  Definition it_eat' : relᵢ (itree E R) (itree E R) :=
    fun i u v => it_eat i u.(_observe) v.(_observe).

  Definition it_eat_tau {i x y} (H : it_eat i (TauF x) (TauF y)) :
    it_eat i x.(_observe) y.(_observe).
  Proof.
    dependent induction H; eauto.
    unfold observe in H; destruct x.(_observe) eqn:Hx; try inversion H; eauto.
  Defined.
End it_eat.
(*|
.. coq:: none
|*)
#[global] Hint Constructors it_eat : core.
#[global] Arguments EatRefl {I E R i t}.
#[global] Arguments EatStep {I E R i t1 t2} p.
(*|
Now we are ready to define the monotone endofunction on indexed relations for
weak bisimilarity.
|*)
Section wbisim.
  Context {I : Type} (E : event I I) {X1 X2 : psh I} (RX : relᵢ X1 X2).

  Variant it_wbisimF RR i (t1 : itree' E X1 i) (t2 : itree' E X2 i) : Prop :=
    | WBisim {x1 x2}
        (r1 : it_eat i t1 x1)
        (r2 : it_eat i t2 x2)
        (rr : it_eqF E RX RR i x1 x2).
(*|
.. coq:: none
|*)
  Arguments WBisim {RR i t1 t2 x1 x2}.
(*|
|*)
  Definition it_wbisim_map : mon (relᵢ (itree E X1) (itree E X2)) :=
    {|
      body RR i x y := it_wbisimF RR i (observe x) (observe y) ;
      Hbody _ _ H _ _ _ '(WBisim r1 r2 rr) := WBisim r1 r2 (it_eqF_mon _ _ H _ _ _ rr) ;
    |}.
(*|
And this is it, we can define heterogeneous weak bisimilarity by ``it_wbisim RR`` for some
value relation ``RR``. See Def. 10.

.. coq::
   :name: wbisim
|*)
  Definition it_wbisim := gfp it_wbisim_map.
  Definition it_wbisim' := it_wbisimF it_wbisim.
End wbisim.
(*|
.. coq:: none
|*)
#[global] Notation it_wbisim_t E RX := (t (it_wbisim_map E RX)).
#[global] Notation it_wbisim_bt E RX := (bt (it_wbisim_map E RX)).
#[global] Notation it_wbisim_T E RX := (T (it_wbisim_map E RX)).
#[global] Arguments it_wbisim {I E X1 X2} RX i.
#[global] Arguments WBisim {I E X1 X2 RX RR i t1 t2 x1 x2}.
#[global] Hint Constructors it_wbisimF : core.
(*|
|*)
#[global] Notation "a ≈ b" := (it_wbisim (eqᵢ _) _ a b) (at level 20).
(*|
Properties
^^^^^^^^^^
|*)
Definition it_wbisim_step {I E X1 X2 RX} :
  it_wbisim RX <= @it_wbisim_map I E X1 X2 RX (it_wbisim RX) :=
  fun i x y => proj1 (gfp_fp (it_wbisim_map E RX) i x y) .

Definition it_wbisim_unstep {I E X1 X2 RX} :
  @it_wbisim_map I E X1 X2 RX (it_wbisim RX) <= it_wbisim RX :=
  fun i x y => proj2 (gfp_fp (it_wbisim_map E RX) i x y) .
(*|
Weak bisimilarity up to synchronization.
|*)
Lemma it_wbisim_up2eqF_t {I E X1 X2 RX} :
  @it_eq_map I E X1 X2 RX <= it_wbisim_t E RX.
Proof.
  apply Coinduction; intros R i x y H.
  cbn in *; dependent destruction H; simpl_depind; econstructor; eauto; econstructor.
  - apply (b_T (it_wbisim_map E RX)), t_rel.
  - intro r; apply (b_T (it_wbisim_map E RX)), k_rel.
Qed.

Section wbisim_facts_het.
  Context {I : Type} {E : event I I} {X1 X2 : psh I} {RX : relᵢ X1 X2}.
(*|
Transitivity will be quite more involved to prove than for strong bisimilarity. In order
to prove it, we will need quite a bit of lemmata for moving synchronization points around.

First a helper for ``go``/``_observe`` ("in"/"out") maps of the final coalgebra.
|*)
  Lemma it_wbisim_obs {i x y} :
    it_wbisim (E:=E) RX i x y ->
    it_wbisim RX i (go x.(_observe)) (go y.(_observe)).
  Proof.
    intro H.
    apply it_wbisim_step in H.
    apply it_wbisim_unstep.
    exact H.
  Qed.
(*|
Strong bisimilarity implies weak bisimilarity.
|*)
  Lemma it_eq_wbisim : it_eq (E:=E) RX <= it_wbisim (E:=E) RX.
  Proof.
    unfold it_wbisim, leq; cbn. unfold Basics.impl.
    coinduction R CIH; intros i x y H.
    apply it_eq_step in H; cbn in *.
    dependent destruction H; simpl_depind; eauto.
  Qed.
(*|
Adding a ``Tau`` left or right.
|*)
  Lemma wbisim_unstep_l {R} {i x y} :
    it_wbisimF E RX R i x (observe y) ->
    it_wbisimF E RX R i x (TauF y).
  Proof.
    intros []. exact (WBisim r1 (EatStep r2) rr).
  Qed.

  Lemma wbisim_unstep_r {R} {i x y} :
    it_wbisimF E RX R i (observe x) y ->
    it_wbisimF E RX R i (TauF x) y.
  Proof.
    intros []. exact (WBisim (EatStep r1) r2 rr).
  Qed.
(*|
Removing a ``Tau`` left or right.
|*)
  Equations wbisim_step_l {i x y} :
    it_wbisim' E RX i x (TauF y) ->
    it_wbisim' E RX i x (observe y)
    :=
    wbisim_step_l (WBisim p (EatRefl) (EqTau r))
      with it_wbisim_step _ _ _ r :=
      { | WBisim w1 w2 s := WBisim (eat_trans _ _ _ _ p (EatStep w1)) w2 s } ;
    wbisim_step_l (WBisim p (EatStep q) v) := WBisim p q v.

  Equations wbisim_step_r {i x y} :
    it_wbisim' E RX i (TauF x) y ->
    it_wbisim' E RX i (observe x) y
    :=
    wbisim_step_r (WBisim (EatRefl) q (EqTau r))
      with it_wbisim_step _ _ _ r :=
      { | WBisim w1 w2 s := WBisim w1 (eat_trans _ _ _ _ q (EatStep w2)) s } ;
    wbisim_step_r (WBisim (EatStep p) q v) := WBisim p q v.
(*|
Pulling a ``Tau`` synchronization point up.
|*)
  Equations wbisim_tau_up_r {i x y z}
    (u : it_eat i x (TauF y))
    (v : it_eqF E RX (it_wbisim RX) i (TauF y) z) :
    it_eqF E RX (it_wbisim RX) i x z
    :=
    wbisim_tau_up_r (EatRefl)   q         := q ;
    wbisim_tau_up_r (EatStep p) (EqTau q) with it_wbisim_step _ _ _ q := {
      | WBisim w1 w2 s :=
          EqTau (it_wbisim_unstep _ _ _ (WBisim (eat_trans _ _ _ _ p (EatStep w1)) w2 s))
      }.

  Equations wbisim_tau_up_l {i x y z}
    (u : it_eqF E RX (it_wbisim RX) i x (TauF y))
    (v : it_eat i z (TauF y)) :
    it_eqF E RX (it_wbisim RX) i x z
    :=
    wbisim_tau_up_l p         (EatRefl)   := p ;
    wbisim_tau_up_l (EqTau p) (EatStep q) with it_wbisim_step _ _ _ p := {
      | WBisim w1 w2 s :=
          EqTau (it_wbisim_unstep _ _ _ (WBisim w1 (eat_trans _ _ _ _ q (EatStep w2)) s))
      }.
(*|
Pushing a ``Ret`` or ``Vis`` synchronization down.
|*)
  Equations wbisim_ret_down_l {i x y r} :
    it_wbisim' E RX i x y ->
    it_eat i y (RetF r) ->
    (it_eat ⨟ it_eqF E RX (it_wbisim RX)) i x (RetF r)
    :=
    wbisim_ret_down_l (WBisim p (EatRefl) w) (EatRefl)   := p ⨟⨟ w ;
    wbisim_ret_down_l w                      (EatStep q) := wbisim_ret_down_l
                                                              (wbisim_step_l w) q.

  Equations wbisim_ret_down_r {i x y r} :
    it_eat i x (RetF r) ->
    it_wbisim' E RX i x y ->
    (it_eqF E RX (it_wbisim RX) ⨟ revᵢ it_eat) i (RetF r) y
    :=
    wbisim_ret_down_r (EatRefl)   (WBisim (EatRefl) q w) := w ⨟⨟ q ;
    wbisim_ret_down_r (EatStep p) w                      := wbisim_ret_down_r p
                                                              (wbisim_step_r w).

  Equations wbisim_vis_down_l {i x y e k} :
    it_wbisim' E RX i x y ->
    it_eat i y (VisF e k) ->
    (it_eat ⨟ it_eqF E RX (it_wbisim RX)) i x (VisF e k)
    :=
    wbisim_vis_down_l (WBisim p (EatRefl) w) (EatRefl)   := p ⨟⨟ w ;
    wbisim_vis_down_l w                      (EatStep q) := wbisim_vis_down_l
                                                              (wbisim_step_l w) q.

  Equations wbisim_vis_down_r {i x y e k} :
    it_eat i x (VisF e k) ->
    it_wbisim' E RX i x y ->
    (it_eqF E RX (it_wbisim RX) ⨟ revᵢ it_eat) i (VisF e k) y
    :=
    wbisim_vis_down_r (EatRefl)   (WBisim (EatRefl) q w) := w ⨟⨟ q ;
    wbisim_vis_down_r (EatStep p) w                      := wbisim_vis_down_r p
                                                              (wbisim_step_r w) .
End wbisim_facts_het.
(*|
We are now ready to prove the useful properties.
|*)
Section wbisim_facts_hom.
  Context {I : Type} {E : event I I} {X : psh I} {RX : relᵢ X X}.
(*|
Registering that strong bisimilarity is a subrelation.
|*)
  #[global] Instance it_eq_wbisim_subrel :
    Subrelationᵢ (it_eq (E:=E) RX) (it_wbisim (E:=E) RX)
    := it_eq_wbisim.
(*|
Reflexivity.
|*)
  Lemma it_wbisim_up2rfl `{Reflexiveᵢ RX} :
    const (eqᵢ _) <= it_wbisim_t E RX.
  Proof.
    apply leq_t.
    repeat intro.
    rewrite H.
    econstructor; eauto.
    now apply it_eqF_rfl.
  Qed.

  #[global] Instance it_wbisim_t_refl `{Reflexiveᵢ RX} {RR} :
    Reflexiveᵢ (it_wbisim_t E RX RR).
  Proof. apply build_reflexive, (ft_t it_wbisim_up2rfl RR). Qed.
(*|
Symmetry.
|*)
  Lemma it_wbisim_up2sym `{Symmetricᵢ RX} :
    converseᵢ <= it_wbisim_t E RX.
  Proof.
    apply leq_t; intros ? ? ? ? [ ? ? r1 r2 rr ].
    refine (WBisim r2 r1 _).
    now apply it_eqF_sym.
  Qed.

  #[global] Instance it_wbisim_t_sym `{Symmetricᵢ RX} {RR} :
    Symmetricᵢ (it_wbisim_t E RX RR).
  Proof. apply build_symmetric, (ft_t it_wbisim_up2sym RR). Qed.

  #[global] Instance it_wbisim_bt_sym `{Symmetricᵢ RX} {RR} :
    Symmetricᵢ (it_wbisim_bt E RX RR).
  Proof. apply build_symmetric, (fbt_bt it_wbisim_up2sym RR). Qed.
(*|
Concatenation, transitivity.
|*)
  Lemma it_wbisimF_tra `{Transitiveᵢ RX} :
    (it_wbisim' E RX ⨟ it_wbisim' E RX) <= it_wbisimF E RX (it_wbisim RX ⨟ it_wbisim RX).
  Proof.
    intros i x y [z [[x1 x2 u1 u2 uS] [y1 y2 v1 v2 vS]]].
    destruct (eat_cmp _ _ _ (u2 ⨟⨟ v1)) as [w | w]; clear z u2 v1.
    - destruct y1.
      + destruct (wbisim_ret_down_l (WBisim u1 EatRefl uS) w) as [z [w1 ww]];
          clear u1 uS w.
        dependent destruction vS; dependent destruction ww.
        refine (WBisim w1 v2 (EqRet _)); now transitivity r.
      + exact (WBisim u1 v2 (it_eqF_tra _ _ _ (uS ⨟⨟ wbisim_tau_up_r w vS))).
      + destruct (wbisim_vis_down_l (WBisim u1 EatRefl uS) w) as [z [w1 ww]];
          clear u1 uS w.
        dependent destruction vS; dependent destruction ww.
        exact (WBisim w1 v2 (EqVis (fun r => k_rel0 r ⨟⨟ k_rel r))).
    - destruct x2.
      + destruct (wbisim_ret_down_r w (WBisim EatRefl v2 vS)) as [z [ww w1]];
          clear v2 vS w.
        dependent destruction uS; dependent destruction ww.
        refine (WBisim u1 w1 (EqRet _)); now transitivity r.
      + exact (WBisim u1 v2 (it_eqF_tra _ _ _ (wbisim_tau_up_l uS w ⨟⨟ vS))).
      + destruct (wbisim_vis_down_r w (WBisim EatRefl v2 vS)) as [z [ww w1]];
          clear v2 vS w.
        dependent destruction uS; dependent destruction ww.
        exact (WBisim u1 w1 (EqVis (fun r => k_rel r ⨟⨟ k_rel0 r))).
  Qed.

  #[global] Instance it_wbisim_tra `{Transitiveᵢ RX} :
    Transitiveᵢ (@it_wbisim I E X X RX).
  Proof.
    apply build_transitive, coinduction; intros ? ? ? [ ? [ u v ] ].
    eapply (Hbody (it_wbisim_map _ _)).
    - apply id_t.
    - apply it_wbisimF_tra.
      refine (_ ⨟⨟ _) ; apply it_wbisim_step; [ exact u | exact v ].
  Qed.
(*|
Packaging the above as equivalence.
|*)
  #[global] Instance it_wbisim_equiv `{Equivalenceᵢ RX} :
    Equivalenceᵢ (it_wbisim (E:=E) RX).
  Proof. econstructor; typeclasses eauto. Qed.
(*|
Eliminating ``Tau`` on both sides.
|*)
  Lemma it_wbisim_tau `{Equivalenceᵢ RX} {i x y} :
    it_wbisim (E:=E) RX i (Tau' x) (Tau' y) -> it_wbisim RX i x y.
  Proof.
    intro H1.
    transitivity (Tau' x).
    apply it_wbisim_unstep.
    econstructor; [ exact EatRefl | exact (EatStep EatRefl) | destruct (observe x); eauto ].
    transitivity (Tau' y).
    exact H1.
    apply it_wbisim_unstep.
    econstructor; [ exact (EatStep EatRefl) | exact EatRefl | destruct (observe y); eauto ].
  Qed.
(*|
We have proven that strong bisimilarity entails weak bisimilarity, but now we prove the
much more powerful fact that we can prove weak bisimilarity *up-to* strong bisimilarity.
That is, we will be allowed to close any weak bisimulation candidate by strong bisimilarity.
Let us first define a helper relation taking a relation to its saturation by strong
bisimilarity.
|*)
  Variant eq_clo (R : relᵢ (itree E X) (itree E X)) i (x y : itree E X i) : Prop :=
    | EqClo {a b} : it_eq RX x a -> it_eq RX b y -> R i a b -> eq_clo R i x y
  .
  #[global] Arguments EqClo {R i x y a b}.
(*|
This helper is monotone...
|*)
  Definition eq_clo_map : mon (relᵢ (itree E X) (itree E X)) :=
    {| body R := eq_clo R ;
      Hbody _ _ H _ _ _ '(EqClo p q r) := EqClo p q (H _ _ _ r) |}.
(*|
... and below the companion of weak bisimilarity, hence justifying the up-to.
|*)
  Lemma it_wbisim_up2eq `{Transitiveᵢ RX} : eq_clo_map <= it_wbisim_t E RX.
  Proof.
    apply Coinduction; intros R i a b [ c d u v [] ].
    apply it_eq_step in u, v; cbn in *.
    remember (observe a) as oa; clear a Heqoa.
    remember (observe b) as ob; clear b Heqob.
    remember (observe c) as oc; clear c Heqoc.
    remember (observe d) as od; clear d Heqod.
    revert oa ob od x2 u r2 v rr; induction r1; intros oa ob od x2 u r2 v rr.
    - revert oa ob u v rr; induction r2; intros oa ob u v rr.
      * destruct rr; dependent elimination u; dependent elimination v;
          refine (WBisim EatRefl EatRefl _); econstructor.
        + transitivity r4; auto; transitivity r1; auto.
        + apply (f_Tf (it_wbisim_map E RX)); exact (EqClo t_rel0 t_rel1 t_rel).
        + intro r; apply (f_Tf (it_wbisim_map E RX)); exact (EqClo (k_rel0 r) (k_rel1 r) (k_rel r)).
      * dependent elimination v.
        apply it_eq_step in t_rel.
        apply wbisim_unstep_l, IHr2; auto.
    - dependent elimination u.
      apply it_eq_step in t_rel.
      apply wbisim_unstep_r, (IHr1 (observe t3) ob od x2); auto.
  Qed.
(*|
We now do the same for up-to eating.
|*)
  Variant eat_clo (R : relᵢ (itree E X) (itree E X)) i (x y : itree E X i) : Prop :=
    | EatClo {a b} : it_eat' i x a -> it_eat' i y b -> R i a b -> eat_clo R i x y
  .
  #[global] Arguments EatClo {R i x y a b}.

  Definition eat_clo_map : mon (relᵢ (itree E X) (itree E X)) :=
    {| body R := eat_clo R ;
       Hbody _ _ H _ _ _ '(EatClo p q r) := EatClo p q (H _ _ _ r) |}.

  Lemma it_wbisim_up2eat `{Transitiveᵢ RX} : eat_clo_map <= it_wbisim_t E RX.
    apply leq_t; intros R i a b [ c d u v [] ].
    unfold it_eat' in u,v; cbn in *; unfold observe in *.
    econstructor.
    * etransitivity; [ exact u | exact r1 ].
    * etransitivity; [ exact v | exact r2 ].
    * revert rr; apply it_eqF_mon.
      intros; econstructor; try econstructor; auto.
  Qed.
End wbisim_facts_hom.
