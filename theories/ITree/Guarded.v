(*|
Guarded Iteration
==================

The ``iter`` combinator, adapted directly from the `Interaction Tree library`_,
happily builds a computation ``iter f`` for any set of equations ``f``.
The resulting computation satisfies in particular an unfolding equation:
``iter f i ≈ f i >>= case_ (iter f) (ret)``
In general, this solution is however not unique, depriving us from a
powerful tool to prove the equivalence of two computations.

.. _Interaction Tree library: https://github.com/DeepSpec/InteractionTrees

Through this file, we recover uniqueness by introducing an alternate
combinator ``iter_guarded`` restricted to so-called *guarded* sets of equations:
they cannot be reduced to immediately returning a new index to iterate over.
Both combinators agree over guarded equations, but the new one satisfies
uniqueness.

Then, we refine the result to allow more sets of equations: not all must
be guarded, but they must always finitely lead to a guarded one.

.. coq:: none
|*)
From Coinduction Require Import coinduction tactics.
From OGS Require Import Prelude.
From OGS.Utils Require Import Rel.
From OGS.ITree Require Import Event ITree Structure Eq Properties.
(*|
Guarded iteration
------------------
|*)
Section guarded.

  Context {I} {E : event I I}.
(*|
A set of equations is an (indexed) family of computations, i.e. body fed to the
combinator.

.. coq::
   :name: equation
|*)
  Definition eqn R X Y : Type := X ⇒ᵢ itree E (Y +ᵢ R) .

  Definition apply_eqn {R X Y} (q : eqn R X Y) : itree E (X +ᵢ R) ⇒ᵢ itree E (Y +ᵢ R) :=
    fun _ t => t >>= fun _ r => match r with
                            | inl x => q _ x
                            | inr y => Ret' (inr y)
                            end .
(*|
A computation is *guarded* if it is not reduced to ``Ret (inl i)``, i.e.
if as part of the loop, this specific iteration will be observable w.r.t.
strong bisimilarity. It therefore may:

- end the iteration
- produce a silent step
- produce an external event

A set of equation is then said to be guarded if all its equations are guarded.

.. coq::
   :name: guarded
|*)
  Variant guarded' {X Y i} : itree' E (X +ᵢ Y) i -> Prop :=
    | GRet y : guarded' (RetF (inr y))
    | GTau t : guarded' (TauF t)
    | GVis e k : guarded' (VisF e k)
  .
  Definition guarded {X Y i} (t : itree E (X +ᵢ Y) i)
    := guarded' t.(_observe).
  Definition eqn_guarded {R X Y} (e : eqn R X Y) : Prop
    := forall i (x : X i), guarded (e i x) .

(*|
The ``iter`` combinator gets away with putting no restriction on the equations
by aggressively guarding with ``Tau`` all recursive calls.
In contrast, by assuming the equations are guarded, we do not need to introduce
any spurious guard: they are only legitimate in the case of returning immediately
a new index, which we can here rule out via ``elim_guarded``.
|*)
  Equations elim_guarded {R X i x} : @guarded' R X i (RetF (inl x)) -> T0 := | ! .

  Definition iter_guarded_aux {R X}
    (e : eqn R X X) (EG : eqn_guarded e)
    : itree E (X +ᵢ R) ⇒ᵢ itree E R
    := cofix CIH i t :=
      t >>= fun _ r =>
          go match r with
            | inl x => match (e _ x).(_observe) as t return guarded' t -> _ with
                      | RetF (inl x) => fun g => ex_falso (elim_guarded g)
                      | RetF (inr r) => fun _ => RetF r
                      | TauF t       => fun _ => TauF (CIH _ t)
                      | VisF q k     => fun _ => VisF q (fun r => CIH _ (k r))
                      end (EG _ x)
            | inr y => RetF y
            end .
(*|
.. coq::
   :name: iterguarded
|*)
  Definition iter_guarded {R X}
    (f : eqn R X X) (EG : eqn_guarded f)
    : X ⇒ᵢ itree E R
    := fun _ x =>
      go (match (f _ x).(_observe) as t return guarded' t -> _ with
          | RetF (inl x) => fun g => ex_falso (elim_guarded g)
          | RetF (inr r) => fun _ => RetF r
          | TauF t       => fun _ => TauF (iter_guarded_aux f EG _ t)
          | VisF q k     => fun _ => VisF q (fun r => iter_guarded_aux f EG _ (k r))
          end (EG _ x)) .
(*|
The absence of a spurious guard is reflected in the unfolding equation:
w.r.t. strong bisimilarity, it directly satisfies what one would expect,
i.e. we run the current equation, and either terminate or jump to the next
one.
|*)
  Lemma iter_guarded_aux_unfold {X Y RY} {_ : Reflexiveᵢ RY}
    (f : eqn Y X X) (EG : eqn_guarded f) {i} (t : itree E (X +ᵢ Y) i)
    : it_eq RY
      (iter_guarded_aux f EG i t)
      (t >>= fun _ r => match r with
                     | inl x => iter_guarded f EG _ x
                     | inr y => Ret' y
                     end).
  Proof.
    revert i t; unfold it_eq; coinduction R CIH; intros i t.
    cbn; pose (ot := _observe t); fold ot.
    destruct ot as [ [] | | ]; cbn.
    1: destruct (EG i x).
    all: econstructor; auto.
    2: intro r.
    all: apply (tt_t (it_eq_map E RY)); cbn; eapply it_eq_up2bind_t; econstructor; auto.
    all: intros ? ? x2 ->; destruct x2; auto.
  Qed.
(*|
.. coq::
   :name: iterguardedfix
|*)
  Lemma iter_guarded_unfold {X Y RY} {_ : Reflexiveᵢ RY}
    (f : eqn Y X X) (EG : eqn_guarded f) {i x}
    : it_eq RY
      (iter_guarded f EG i x)
      (f i x >>= fun _ r => match r with
                         | inl x => iter_guarded f EG _ x
                         | inr y => Ret' y
                         end).
  Proof.
    apply it_eq_unstep; cbn.
    pose (p := EG i x); fold p; unfold guarded in p.
    pose (ot := _observe (f i x)); fold ot in p |- *.
    destruct p; econstructor; [ now apply H | | intro r ]; apply iter_guarded_aux_unfold.
  Qed.
(*|
The payoff: ``iter_guarded`` does not only deliver a solution to the equations,
but it also is unique.

.. coq::
   :name: iterguardeduniq
|*)
  Lemma iter_guarded_uniq {X Y RY} {_ : Equivalenceᵢ RY}
    (f : eqn Y X X) (g : X ⇒ᵢ itree E Y)
    (EG : eqn_guarded f)
    (EQ : forall i x, it_eq RY
                   (g i x)
                   (bind (f i x) (fun _ r => match r with
                                          | inl x => g _ x
                                          | inr y => Ret' y end)))
    : forall i x, it_eq RY (g i x) (iter_guarded f EG i x).
  Proof.
    unfold it_eq; coinduction R CIH; intros i x.
    etransitivity; [ | symmetry; apply it_eq_t_bt, (iter_guarded_unfold f EG) ].
    rewrite (EQ i x); cbn.
    pose (a := (f i x).(_observe)); fold a.
    pose (Ha := EG i x); unfold guarded in Ha; fold a in Ha.
    destruct Ha; cbn; econstructor; auto; [ | intro r ].
    all: change (subst ?f _ ?t) with (bind t f).
    all: eapply (tt_t (it_eq_map E RY)).
    all: refine (it_eq_up2bind_t _ _ _ _ _ _ _); econstructor; eauto.
    all: intros ? ? ? <-; destruct x1; auto.
  Qed.
(*|
Furthermore, w.r.t. weak bisimilarity, we compute the same solution as what ``iter`` does.
|*)
  Lemma guarded_cong' {X Y} {i}
    (s t : itree' E (X +ᵢ Y) i) (EQ : it_eq' (eqᵢ _) s t)
    (g : guarded' s) : guarded' t.
  Proof.
    destruct EQ as [ [] | | ]; [ dependent elimination g | rewrite <- r_rel | | ]; econstructor.
  Qed.

  Definition guarded_cong {X Y} {i} (s t : itree E (X +ᵢ Y) i)
    (EQ : s ≊ t) (g : guarded s) : guarded t :=
    := guarded_cong' s.(_observe) t.(_observe) (it_eq_step _ _ _ EQ) g .
(*|
.. coq::
   :name: iterguardedweak
|*)
  Lemma iter_guarded_iter {X Y}
    (f : eqn Y X X) (EG : eqn_guarded f) {i x}
    : iter_guarded f EG i x ≈ iter f i x .
  Proof.
    revert i x; unfold it_wbisim; coinduction R CIH; intros i x.
    eapply (@fbt_bt _ _ (it_wbisim_map E (eqᵢ Y)) _ it_wbisim_up2eq).
    econstructor.
    apply iter_guarded_unfold.
    symmetry; apply iter_unfold.
    remember (EG _ x) as g; clear Heqg.
    remember (f i x) as t; clear Heqt.
    unfold guarded in g.
    remember (_observe t) as ot.
    destruct g; cbn ; rewrite <- Heqot; cbn.
    econstructor; auto.
    all: econstructor; auto; econstructor; intros.
    all: eapply (tt_t (it_wbisim_map E (eqᵢ Y))).
    all: refine (it_wbisim_up2bind_t _ _ _ _ _ _ _); econstructor; auto.
    all: intros ? ? x2 ->; destruct x2; auto.
    all: eapply (tt_t (it_wbisim_map E (eqᵢ Y))).
    all: cbn; apply it_wbisim_up2eat; econstructor;
      [ exact EatRefl | exact (EatStep EatRefl) | apply CIH ].
  Qed.
(*|
Minor technical lemmas: guardedness is proof irrelevant.
|*)
  Lemma guarded'_irrelevant {R X i t} (p q : @guarded' R X i t) : p = q .
    destruct t; dependent elimination p; dependent elimination q; reflexivity.
  Qed.

  Lemma guarded_irrelevant {R X i t} (p q : @guarded R X i t) : p = q .
    apply guarded'_irrelevant.
  Qed.

End guarded.
(*|
Eventually guarded iteration
------------------------------

For our purpose, proving the soundness of the ogs, guardedness is a bit too
restrictive: while not all equations are guarded, they all inductively lead
to a guarded one. We capture this intuition via the notion of "eventually
guarded" set of equations, and establish similar result to ones in the guarded case.
|*)
Section eventually_guarded.

  Context {I} {E : event I I}.
(*|
A set of equations is eventually guarded if they all admit an inductive path following
its non-guarded indirections that leads to a guarded equation.

.. coq::
   :name: evguarded
|*)
  Unset Elimination Schemes.
  Inductive ev_guarded' {X Y} (e : eqn Y X X) {i} : itree' E (X +ᵢ Y) i -> Prop :=
  | GHead t : guarded' t -> ev_guarded' e t
  | GNext x : ev_guarded' e (e i x).(_observe) -> ev_guarded' e (RetF (inl x))
  .
  #[global] Arguments GHead {X Y e i t}.
  #[global] Arguments GNext {X Y e i x}.

  Scheme ev_guarded'_ind := Induction for ev_guarded' Sort Prop.
  Set Elimination Schemes.

  Definition ev_guarded {X Y} (e : eqn Y X X) {i} (t : itree E (X +ᵢ Y) i)
    := ev_guarded' e t.(_observe).
  Definition eqn_ev_guarded {X Y} (e : eqn Y X X) : Type
    := forall i (x : X i), ev_guarded e (e i x) .

  Equations elim_ev_guarded' {X Y e i x} (g : @ev_guarded' X Y e i (RetF (inl x)))
            : ev_guarded' e (e i x).(_observe) :=
    elim_ev_guarded' (GNext g) := g .
(*|
Given eventually guarded equations ``e``, we can build a set of guarded equations
``eqn_evg_unroll_guarded e``: we simply map all indices to their reachable guarded
equations. Iteration over eventually guarded equations is hence defined as guarded
iteration over their guarded counterpart.
|*)
  Fixpoint evg_unroll' {X Y} (e : eqn Y X X) {i}
    (t : itree' E (X +ᵢ Y) i) (g : ev_guarded' e t) { struct g } : itree' E (X +ᵢ Y) i
    := match t as t' return ev_guarded' e t' -> _ with
       | RetF (inl x) => fun g => evg_unroll' e (e _ x).(_observe) (elim_ev_guarded' g)
       | RetF (inr y) => fun _ => RetF (inr y)
       | TauF t       => fun _ => TauF t
       | VisF q k     => fun _ => VisF q k
       end g .

  Definition evg_unroll {X Y} (e : eqn Y X X) {i}
    (t : itree E (X +ᵢ Y) i) (g : ev_guarded e t) : itree E (X +ᵢ Y) i
    := go (evg_unroll' e t.(_observe) g) .

  Definition eqn_evg_unroll {X Y} (e : eqn Y X X) (H : eqn_ev_guarded e) : eqn Y X X
    := fun _ x => evg_unroll e _ (H _ x) .

  Lemma evg_unroll_guarded' {X Y} (e : eqn Y X X) {i}
    (t : itree' E (X +ᵢ Y) i) (g : ev_guarded' e t) : guarded' (evg_unroll' e t g).
  Proof.
    induction g; auto.
    destruct t as [ [] | | ]; auto.
    dependent elimination g.
  Qed.

  Definition evg_unroll_guarded {X Y} (e : eqn Y X X) {i}
    (t : itree E (X +ᵢ Y) i) (EG : ev_guarded e t) : guarded (evg_unroll e t EG)
    := evg_unroll_guarded' e t.(_observe) EG.

  Definition eqn_evg_unroll_guarded {X Y}
    (e : eqn Y X X) (EG : eqn_ev_guarded e) : eqn_guarded (eqn_evg_unroll e EG)
    := fun _ x => evg_unroll_guarded e _ (EG _ x) .
(*|
.. coq::
   :name: iterevguarded
|*)
  Definition iter_ev_guarded {R X}
    (e : eqn R X X) (EG : eqn_ev_guarded e) : X ⇒ᵢ itree E R
    := fun _ x => iter_guarded _ (eqn_evg_unroll_guarded e EG) _ x .
(*|
Once again, we establish the expected unfolding lemma, for eventually guarded iteration.
|*)
  Lemma evg_unroll'_equation {X Y}
    (e : eqn Y X X) {i} {x : X i} (g : ev_guarded' e (RetF (inl x)))
    : evg_unroll' e (RetF (inl x)) g = evg_unroll' e (e _ x).(_observe) (elim_ev_guarded' g) .
  Proof.
    dependent elimination g; [ dependent elimination g | reflexivity ] .
  Qed.

  Lemma ev_guarded'_irrelevant {R X e i t}
    (p q : @ev_guarded' R X e i t) : p = q .
  Proof.
    induction p.
    - destruct t as [ [] | | ]; [ dependent elimination g | | | ];
        dependent elimination q; f_equal; apply guarded'_irrelevant.
    - dependent elimination q; [ dependent elimination g | ]; f_equal; apply IHp.
  Qed.

  Lemma iter_evg_unfold_lem {X Y RY} {_ : Equivalenceᵢ RY}
    (f : eqn Y X X) (EG : eqn_ev_guarded f) {i x1 x2}
    (p : (f i x1).(_observe) = RetF (inl x2))
    : it_eq RY
        (iter_ev_guarded f EG i x1)
        (iter_ev_guarded f EG i x2).
  Proof.
    unfold iter_ev_guarded at 1.
    etransitivity; [ apply iter_guarded_unfold | ].
    change (iter_guarded _ _ ?i ?x) with (iter_ev_guarded f EG i x).
    unfold eqn_evg_unroll; remember (EG i x1) as q; clear Heqq.
    apply it_eq_unstep; unfold evg_unroll; cbn -[iter_ev_guarded].
    unfold ev_guarded in q; revert q; rewrite p; clear p; intro q.
    rewrite evg_unroll'_equation, (ev_guarded'_irrelevant (elim_ev_guarded' q) (EG _ x2)); clear q.
    change (it_eqF E RY (it_eq RY) i _ (observe ?a))
      with (it_eq_map E RY (it_eq RY) i
              (evg_unroll f (f i x2) (EG i x2) >>= fun (i0 : I) (r : (X +ᵢ Y) i0) =>
                   match r with
                   | inl x => iter_ev_guarded f EG i0 x
                   | inr y => Ret' y
                   end)
              a).
    apply it_eq_step; symmetry; exact (iter_guarded_unfold _ _).
  Qed.

(*|
.. coq::
   :name: iterevguardedfix
|*)
  Lemma iter_evg_unfold {X Y RY} {_ : Equivalenceᵢ RY}
    (f : eqn Y X X) (EG : eqn_ev_guarded f) {i x} :
    : it_eq RY
        (iter_ev_guarded f EG i x)
        (f i x >>= fun _ r => match r with
                           | inl x => iter_ev_guarded f EG _ x
                           | inr y => Ret' y
                           end).
  Proof.
    apply it_eq_unstep; cbn -[iter_ev_guarded].
    remember (EG i x) as g; clear Heqg; unfold ev_guarded in g.
    remember (_observe (f i x)).
    destruct i0 as [ [] | | ].
    apply (it_eq_step _ (iter_ev_guarded f EG i x) (iter_ev_guarded f EG i x0)), iter_evg_unfold_lem; auto.
    all: clear g; cbn; unfold eqn_evg_unroll_guarded at 3, evg_unroll_guarded.
    all: remember (EG i x) as g'; clear Heqg'; unfold ev_guarded in g'.
    all: revert g'; rewrite <- Heqi0; intros g'.
    all: dependent elimination g'; econstructor; auto; intros.
    all: apply iter_guarded_aux_unfold.
  Qed.
(*|
Uniqueness still holds.

.. coq::
   :name: iterevguardeduniq
|*)
  Lemma iter_evg_uniq {X Y RY} {_ : Equivalenceᵢ RY}
    (f : eqn Y X X) (g : X ⇒ᵢ itree E Y)
    (EG : eqn_ev_guarded f)
    (EQ : forall i x,
        it_eq RY
          (g i x)
          (bind (f i x) (fun _ r => match r with
                                 | inl x => g _ x
                                 | inr y => Ret' y end)))
    : forall i x, it_eq RY (g i x) (iter_ev_guarded f EG i x).
  Proof.
    unfold it_eq; coinduction R CIH; intros i x.
    rewrite iter_evg_unfold, (EQ i x).
    remember (EG i x) as Ha; clear HeqHa; unfold ev_guarded in Ha.
    remember (f i x) as t; clear Heqt.
    remember (_observe t) as ot.
    revert t Heqot; induction Ha; intros t' Heqot.
    - dependent elimination g0; cbn; rewrite <- Heqot; econstructor; auto; [ | intro r ].
      all: eapply (tt_t (it_eq_map E RY)).
      all: refine (it_eq_up2bind_t _ _ _ _ _ _ _); econstructor; auto.
      all: intros ? ? x2 ->; destruct x2; auto.
    - cbn; rewrite <- Heqot.
      change (it_eqF E RY ?R i (_observe ?a) (_observe ?b)) with (it_eq_map E RY R i a b).
      rewrite iter_evg_unfold, (EQ i x0).
      apply IHHa; auto.
  Qed.
(*|
And w.r.t. weak bisimilarity, we still perform the same computation.

.. coq::
   :name: iterevguardedweak
|*)
  Lemma iter_evg_iter {X Y}
    (f : eqn Y X X) (EG : eqn_ev_guarded f) {i x}
    : iter_ev_guarded f EG i x ≈ iter f i x .
  Proof.
    revert i x; unfold it_wbisim; coinduction R CIH; intros i x.
    eapply (@fbt_bt _ _ (it_wbisim_map E (eqᵢ Y)) _ it_wbisim_up2eq).
    econstructor.
    apply iter_evg_unfold.
    symmetry; apply iter_unfold.
    remember (EG _ x) as g; clear Heqg.
    remember (f i x) as t; clear Heqt.
    unfold ev_guarded in g.
    remember (_observe t) as ot.
    revert t Heqot; induction g; intros u Heqot.
    - destruct g; cbn ; rewrite <- Heqot; cbn.
      econstructor; auto.
      all: econstructor; auto; econstructor; intros.
      all: eapply (tt_t (it_wbisim_map E (eqᵢ Y))).
      all: refine (it_wbisim_up2bind_t _ _ _ _ _ _ _); econstructor; auto.
      all: intros ? ? x2 ->; destruct x2; auto.
      all: eapply (tt_t (it_wbisim_map E (eqᵢ Y))).
      all: cbn; apply it_wbisim_up2eat; econstructor; [ exact EatRefl | exact (EatStep EatRefl) | apply CIH ].
    - cbn; rewrite <- Heqot.
      change (it_wbisimF E (eqᵢ Y) _ _ (_observe ?a) (TauF ?b)) with
        (it_wbisim_bt E (eqᵢ Y) R _ a (Tau' b)).
      eapply (@fbt_bt _ _ (it_wbisim_map E _)).
      refine (it_wbisim_up2eat).
      econstructor; [ exact EatRefl | exact (EatStep EatRefl) | ].
      eapply (@fbt_bt _ _ (it_wbisim_map E _)).
      apply (it_wbisim_up2eq).
      econstructor.
      apply iter_evg_unfold.
      symmetry; apply iter_unfold.
      now apply IHg.
  Qed.
End eventually_guarded.
