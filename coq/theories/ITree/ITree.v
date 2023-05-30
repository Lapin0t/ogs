From OGS Require Import Prelude.
From OGS.Game Require Import Event.

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

Notation itree' E R := (itreeF E R (itree E R)).

Definition observe {I E R i} (t : @itree I E R i) : itree' E R i := t.(_observe).

Notation Ret' x := (go (RetF x)).
Notation Tau' t := (go (TauF t)).
Notation Vis' e k := (go (VisF e k)).
