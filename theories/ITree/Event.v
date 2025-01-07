(*|
Game event
==========

In order to specify the set of visible moves of an indexed interaction tree, we use the
notion of indexed polynomial functor. See "Indexed Containers" by Thorsten Altenkirch,
Neil Ghani, Peter Hancock, Conor McBride, and Peter Morris.

.. coq:: none
|*)
From OGS Require Import Prelude.
From OGS.Utils Require Export Psh.
(*|
In our interaction-oriented nomenclature, an indexed container consists of a family of
queries ``e_qry``, a family of responses ``e_rsp`` and a function assigning the next
index to each response ``e_nxt``.
|*)
Record event (I J : Type) : Type := Event {
  e_qry : I -> Type ;
  e_rsp : forall i, e_qry i -> Type ;
  e_nxt : forall i (q : e_qry i), e_rsp i q -> J
}.
(*|
.. coq:: none
|*)
Arguments e_qry {I J e}.
Arguments e_rsp {I J e i} q.
Arguments e_nxt {I J e i q} r.
(*|
Finally we can interpret an ``event`` as a functor from families over ``J`` to families
over ``I``.
|*)
Definition e_interp {I J} (E : event I J) (X : psh J) : psh I :=
  fun i => { q : E.(e_qry) i & forall (r : E.(e_rsp) q), X (E.(e_nxt) r) } .
(*|
We define the empty event.
|*)
Definition emptyₑ {I} : event I I :=
  {| e_qry := fun _ => T0 ;
     e_rsp := fun _ => ex_falso ;
     e_nxt := fun _ x => ex_falso x |}.

#[global] Notation "∅ₑ" := (emptyₑ).
