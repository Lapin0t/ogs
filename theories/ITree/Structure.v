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

  Definition eat_one_tau {X i} (t : itree E X i) : itree E X i :=
    go match t.(_observe) with
       | RetF x => RetF x
       | TauF t => t.(_observe)
       | VisF q k => VisF q k
       end .
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
Iteration operator.

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
(*|
Given a map between events, we can translate the interaction trees. This exhibits
``itree`` itself as a functor from the category of events to the category of endofunctors
on indexed sets.
|*)
Definition emap {I} {A B : event I I} (F : A ⇒ₑ B) {X} : itree A X ⇒ᵢ itree B X :=
  cofix _emap _ u :=
      go match u.(_observe) with
         | RetF r => RetF r
         | TauF t => TauF (_emap _ t)
         | VisF e k => VisF (F.(ea_qry) e)
                           (fun r => _emap _ (rew (F.(ea_nxt)) in k (F.(ea_rsp) r)))
         end.
