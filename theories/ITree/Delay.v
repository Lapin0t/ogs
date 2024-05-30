(*|
Delay Monad
============

Instead of defining the delay monad from scratch, we construct it as a special case of
``itree``, namely ones with an empty signature ``∅ₑ`` (disallowing ``Vis`` nodes) and
indexed over the singleton type ``T1``.

.. coq:: none
|*)
From Coinduction Require Import coinduction tactics.

From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.
From OGS.ITree Require Import Event ITree Structure Eq.

(*|
The delay monad (Def 4.5) is formalized as an itree over an empty signature: in the
absence of events, ``Tau`` and ``Ret`` are the only possible transitions.

Relevant definitions can be found:

- for the underlying itree datatype, in `ITree/ITree.v <ITree.html>`_,
- for the combinators, in `ITree/Structure.v <Structure.html>`_,
- for the (strong/weak) bisimilarity, in `ITree/Eq.v <Eq.html>`_,
- for guarded iteration (§ 6.2), in `ITree/Guarded.v <Guarded.html>`_.

.. coq::
   :name: delay
|*)
Definition delay (X : Type) : Type := itree ∅ₑ (fun _ => X) T1_0.

(*|
Embedding [delay] into itrees over arbitrary signatures.
|*)
Definition emb_delay {I} {E : event I I} {X i} : delay X -> itree E (X @ i) i :=
  cofix _emb_delay x :=
      go (match x.(_observe) with
         | RetF r => RetF (Fib r)
         | TauF t => TauF (_emb_delay t)
         | VisF e k => match e with end
         end).

#[global] Notation "'RetD' x" := (RetF (x : (fun _ : T1 => _) T1_0)) (at level 40).
#[global] Notation "'TauD' t" := (TauF (t : itree ∅ₑ (fun _ : T1 => _) T1_0)) (at level 40).
(*|
Specialization of the operations to the delay monad. Most of them are a bit cumbersome
since our definition of ``itree`` is indexed, but ``delay`` should not. As such there
is a bit of a dance around the singleton type ``T1`` which is used as index. Too bad,
since Coq does not have typed conversion we don't get definitional eta-law for the unit
type...
|*)
Definition ret_delay {X} : X -> delay X := fun x => Ret' x .

Definition tau_delay {X} : delay X -> delay X :=
  fun t => go (TauF (t : itree ∅ₑ (fun _ : T1 => X) T1_0)) .
(*|
Binding a delay computation in the context of an itree.
|*)
Definition bind_delay {I} {E : event I I} {X Y i}
  : delay X -> (X -> itree E Y i) -> itree E Y i
  := fun x f => bind (emb_delay x) (fun _ '(Fib x) => f x) .
(*|
Simpler definition of bind when the conclusion is again in delay.

.. coq::
   :name: delaybind
|*)
Definition bind_delay' {X Y}
  : delay X -> (X -> delay Y) -> delay Y
  := fun x f => bind x (fun 'T1_0 y => f y).
(*|
Functorial action on maps.
|*)
Definition fmap_delay {X Y} (f : X -> Y) : delay X -> delay Y :=
  fmap (fun _ => f) T1_0 .
(*|
Iteration operator.
|*)
Definition iter_delay {X Y} : (X -> delay (X + Y)) -> X -> delay Y :=
  fun f => iter (fun 'T1_0 => f) T1_0 .
(*|
Alternative to ``bind_delay``, written from scratch.
|*)
Definition subst_delay {I} {E : event I I} {X Y i} (f : X -> itree E Y i)
  : delay X -> itree E Y i
  := cofix _subst_delay x := go match x.(_observe) with
                                | RetF r => (f r).(_observe)
                                | TauF t => TauF (_subst_delay t)
                                | VisF e k => match e with end
                                end .

#[global] Instance subst_delay_eq {I E X RX Y RY i}
    : Proper ((RX ==> it_eq RY (i:=i)) ==> (it_eq (fun _ => RX) (i:=T1_0) ==> it_eq RY (i:=i)))
    (@subst_delay I E X Y i).
Proof.
  intros ? ? Hf; unfold it_eq at 2; unfold respectful; coinduction R CIH; intros t1 t2 H.
  apply it_eq_step in H; cbn in *; unfold observe in H.
  remember (_observe t1) as ot1; clear t1 Heqot1.
  remember (_observe t2) as ot2; clear t2 Heqot2.
  dependent elimination H; cbn.
  - eapply it_eqF_mon; [ apply gfp_t | ].
    specialize (Hf _ _ r_rel); apply it_eq_step in Hf; exact Hf.
  - econstructor; now apply CIH.
  - destruct q.
Qed.
