(*|
Delay Monad
============

Specialization of the itree constructions to the delay monad implemented as an
indexed tree over the empty signature ∅ₑ.
.. coq:: none
|*)

From OGS Require Import Prelude.
From OGS.Game Require Import Event.
From OGS.ITree Require Import ITree Structure.

(*|
The delay monad, defined in Section 5.5 in the paper, is formalized as an itree over
an empty signature: in the absence of events, [τ] and [ret] are the only constructors
inhabited.

Relevant definitions can be found:
- for the underlying itree datatype, in [ITree/ITree.v]
- for the combinators, in [ITree/Structure.v].
- for the (strong/weak) bisimilarity, in [ITree/Eq.v].
- for guarded iteration (Section 6.2), in [ITree/Guarded.v]

.. coq::
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

(*|
Specialization of the operations to the delay monad.
|*)
Definition ret_delay {X} : X -> delay X := fun x => Ret' x .

Definition tau_delay {X} : delay X -> delay X :=
  fun t => go (TauF (t : itree ∅ₑ (fun _ : T1 => X) T1_0)) .

Definition bind_delay {I} {E : event I I} {X Y i}
  : delay X -> (X -> itree E Y i) -> itree E Y i
  := fun x f => bind (emb_delay x) (fun _ '(Fib x) => f x) .

Definition bind_delay' {X Y}
  : delay X -> (X -> delay Y) -> delay Y
  := fun x f => bind x (fun 'T1_0 y => f y).

Definition fmap_delay {X Y} (f : X -> Y) : delay X -> delay Y :=
  fmap (fun _ => f) T1_0 .

Definition iter_delay {X Y} : (X -> delay (X + Y)) -> X -> delay Y :=
  fun f => iter (fun 'T1_0 => f) T1_0 .
