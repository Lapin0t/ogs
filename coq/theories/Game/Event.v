From OGS Require Import Prelude.
From OGS.Utils Require Export Psh.

Record event (I J : Type) : Type := Event {
    e_qry : I -> Type ;
    e_rsp : forall i, e_qry i -> Type ;
    e_nxt : forall i (q : e_qry i), e_rsp i q -> J
}.
Arguments e_qry {I J e}.
Arguments e_rsp {I J e i} q.
Arguments e_nxt {I J e i q} r.

Record earr {I J} (A B : event I J) : Type := EArr {
  ea_qry : forall i, A.(e_qry) i -> B.(e_qry) i ;
  ea_rsp : forall i a, B.(e_rsp) (ea_qry i a) -> A.(e_rsp) a ;
  ea_nxt : forall i a b, A.(e_nxt) (ea_rsp i a b) = B.(e_nxt) b
}.
Arguments ea_qry {I J A B e i}.
Arguments ea_rsp {I J A B e i a}.
Arguments ea_nxt {I J A B e i a b}.
#[global] Notation "A ⇒ₑ B" := (earr A B) (at level 50).

Definition e_interp {I J} (E : event I J) (X : psh J) : psh I :=
  fun i => { q : E.(e_qry) i & forall (r : E.(e_rsp) q), X (E.(e_nxt) r) } .

Definition emptyₑ {I} : event I I :=
  {| e_qry := fun _ => T0 ;
     e_rsp := fun _ => ex_falso ;
     e_nxt := fun _ x => ex_falso x |}.

#[global] Notation "∅ₑ" := (emptyₑ).

Definition ex_falsoₑ {I} {E : event I I} : ∅ₑ ⇒ₑ E :=
  {| ea_qry := fun _ (q : ∅ₑ.(e_qry) _) => match q with end ;
     ea_rsp := fun _ q => match q with end ;
     ea_nxt := fun _ q => match q with end |}.
