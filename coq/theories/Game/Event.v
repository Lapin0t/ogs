From OGS Require Import Utils.

Record event (I J : Type) : Type := Event {
    e_qry : I -> Type ;
    e_rsp : forall i, e_qry i -> Type ;
    e_nxt : forall i (q : e_qry i), e_rsp i q -> J
}.
Arguments e_qry {I J e}.
Arguments e_rsp {I J e i} q.
Arguments e_nxt {I J e i q} r.

Definition e_interp {I J} (E : event I J) (X : psh J) : psh I :=
  fun i => { q : E.(e_qry) i & forall (r : E.(e_rsp) q), X (E.(e_nxt) r) } .

Definition emptyₑ {I} : event I I :=
  {| e_qry := fun _ => T0 ;
     e_rsp := fun _ => ex_falso ;
     e_nxt := fun _ x => ex_falso x |}.

#[global] Notation "∅ₑ" := (emptyₑ).
