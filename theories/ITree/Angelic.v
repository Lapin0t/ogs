From OGS Require Import Utils.
From OGS.ITree Require Import Event Cat ITree.

(** "Angelic" (vs "daemonic") indexed containers (and itrees), are
    indexed itrees that know at which indice they start and *end*. The
    nomenclature is borrowed from McBride's "Kleisly Arrow of
    Outrageous Fortune" and is meant to evocate daemonic uncertainty
    and angelic knowledge. More practically instead of representing
    these functors as (daemonic):

       (I → Type) → (J → Type)

    we represent them as (angelic):

       I → J → Type → Type

    This is less powerful in the theory, but enables us to write nicer
    to use types for some combinators, reminescent of Hoar-logic
    triplets. Some people (like the Idris `Effect` system) implement
    directly this flavor of indexed containers, but we prefer the more
    categorically well-behaved flavor, and implement the angelic
    flavor on top.  This is done using the "X @ i" operator, which is
    closely related to the fiber construction. It has type

      "@" : Type → I → I → Type

    and is such that `(X @ i) j` is equal to `X` whenever `i = j` and
    empty otherwise.
*)

Definition itreeₐ {I} (E : event I I) i j X : Type := itree E (X @ j) i.

Section angelic.
Context {I : Type} {E : event I I}.

Definition tauₐ {X i j} (t : itreeₐ E i j X) : itreeₐ E i j X := tau t.
Definition retₐ {X i} (x : X) : itreeₐ E i i X := ret (pin _ x).
Definition visₐ {X i j} q (k : forall r, itreeₐ E _ j X) : itreeₐ E i j X := vis q k.

Definition bindₐ {X Y i j} (x : itreeₐ E i j X) (f : X -> itree E Y j)
                       : itree E Y i :=
 x >>= fib_into (itree _ _) f.

Notation "x !>= f" := (bindₐ x f) (at level 30).

Definition iterₐ {X Y i} (f : X -> itreeₐ E i i (X + Y)) : X -> itreeₐ E i i Y :=
  cofix _iter x := f x !>= fun r => match r with
                                 | inl x => tauₐ (_iter x)
                                 | inr y => retₐ y
                                 end.
End angelic.
#[global] Notation "x !>= f" := (bindₐ x f) (at level 30).


(** Non-dependent itrees, ie itrees that are trivially indexed benefit
    a bit from the angelic encoding, since when we will get to leaves
    we will automatically pattern match on the (trivial) index.
    Unrolling definitions, we prefer to define:

      itree_nondep E X := itree E (X @ T1_0) T1_0

    instead of:

      itree_nondep E X := itree E (fun _ => X) T1_0
*)
Module NonDep.
  Definition itree (E : NonDep.event) X : Type := itreeₐ E T1_0 T1_0 X.

  Context {E : NonDep.event}.

  Definition tau {E X} (t : itree E X) : itree E X := tau t.
  Definition ret {E X} (x : X) : itree E X := ret (pin _ x).
  Definition vis {E X} (q : NonDep.qry E) (k : forall r, itree E X) : itree E X :=
    vis q (fun r => match E.(nxt) q r with T1_0 => k r end).
End NonDep.
