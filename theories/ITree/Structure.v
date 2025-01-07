(*|
Interaction Trees: Structure
==============================

ITrees form an iterative monad. The ``iter`` combinator provided here iterates over
arbitrary sets of equations. The file `ITree/Guarded.v <Guarded.html>`_ provides a
finer iterator, restricted to notions of guarded equations, enjoying an additional
uniqueness property.

.. coq:: none
|*)
From OGS Require Import Prelude.
From OGS.ITree Require Import Event ITree.
(*|
.. coq::
|*)
Section monad.
  Context {I} {E : event I I}.
(*|
Functorial action on maps.
|*)
  Definition fmap {X Y} (f : X ⇒ᵢ Y) : itree E X ⇒ᵢ itree E Y :=
    cofix _fmap _ u :=
      go match u.(_observe) with
         | RetF r => RetF (f _ r)
         | TauF t => TauF (_fmap _ t)
         | VisF e k => VisF e (fun r => _fmap _ (k r))
         end.

(*|
Monadic bind.
|*)
  Definition subst {X Y} (f : X ⇒ᵢ itree E Y) : itree E X ⇒ᵢ itree E Y :=
    cofix _subst _ u :=
      go match u.(_observe) with
         | RetF r => (f _ r).(_observe)
         | TauF t => TauF (_subst _ t)
         | VisF e k => VisF e (fun r => _subst _ (k r))
         end.

  Definition bind {X Y i} x f := @subst X Y f i x.

  Definition kcomp {X Y Z} (f : X ⇒ᵢ itree E Y) (g : Y ⇒ᵢ itree E Z) : X ⇒ᵢ itree E Z :=
    fun i x => bind (f i x) g.
(*|
Iteration operator (Def. 31).

.. coq::
   :name: iter
|*)
  Definition iter {X Y} (f : X ⇒ᵢ itree E (X +ᵢ Y)) : X ⇒ᵢ itree E Y :=
    cofix _iter _ x :=
      bind (f _ x) (fun _ r => go match r with
                              | inl x => TauF (_iter _ x)
                              | inr y => RetF y
                              end) .
End monad.

#[global] Notation "f <$> x" := (fmap f _ x) (at level 30).
#[global] Notation "x >>= f" := (bind x f) (at level 30).
#[global] Notation "f =<< x" := (subst f _ x) (at level 30).
#[global] Notation "f >=> g" := (kcomp f g) (at level 30).
