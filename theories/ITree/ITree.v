(*|
Interaction Trees: Definition
==============================

We implement a subset of the Interaction Tree library in an indexed setting.
These indices provide dynamic control over the set of available external events
during the computation. In particular, the interface is composed of some ``event I I``,
i.e.:

- a family of available query at each index;
- a domain of answers associated to each query;
- a transition function assigning the new index associated with the answer

.. coq:: none
|*)
From OGS Require Import Prelude.
From OGS.ITree Require Import Event.
(*|
Indexed Interaction Trees
---------------------------

.. coq::
   :name: itree
|*)
Section itree.
  Context {I : Type}.
  Context (E : event I I).
  Context (R : psh I).

  Variant itreeF (REC : psh I) (i : I) : Type :=
    | RetF (r : R i) : itreeF REC i
    | TauF (t : REC i) : itreeF REC i
    | VisF (q : E.(e_qry) i) (k : forall (r : E.(e_rsp) q), REC (E.(e_nxt) r)) : itreeF REC i
  .
  Derive NoConfusion for itreeF.

  CoInductive itree (i : I) : Type := go { _observe : itreeF itree i }.

End itree.
(*|
.. coq:: none
|*)
Declare Scope itree_scope.
Bind Scope itree_scope with itree.
Delimit Scope itree_scope with itree.
Local Open Scope itree_scope.

Arguments itree {I} E R i.
Arguments itreeF {I} E R REC i.
Arguments RetF {I E R REC i} r.
Arguments TauF {I E R REC i} t.
Arguments VisF {I E R REC i} q k.
Arguments _observe {I E R i} t : rename.
Arguments go {I E R i} t : rename.
(*|
|*)
Notation itree' E R := (itreeF E R (itree E R)).
(*|
The following function defines the coalgebra structure.
|*)
Definition observe {I E R i} (t : @itree I E R i) : itree' E R i := t.(_observe).

Notation Ret' x := (go (RetF x)).
Notation Tau' t := (go (TauF t)).
Notation Vis' e k := (go (VisF e k)).
