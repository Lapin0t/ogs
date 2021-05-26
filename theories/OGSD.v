From OGS Require Import Utils EventD ITreeD RecD.

Definition itcomp (X : Type) : Type := itree evoid (fun _ => X) t1_0.

Record ogs_spec : Type := OGS_SPEC {
  idx_p : Type ;
  idx_o : Type ;
  act_p : idx_p -> Type ;
  act_o : idx_o -> Type ;
  leaf_p : idx_p -> Type ;
  conf_p : idx_p -> Type ;
  conf_o : idx_o -> Type ;
  nxt_p : forall i, act_p i -> idx_o ;
  nxt_o : forall i, act_o i -> idx_p ;
  app_o : forall i (oa : act_o i), conf_o i -> conf_p (nxt_o i oa) ;
  play : forall i, conf_p i -> itcomp (leaf_p i + { p : act_p i & conf_o (nxt_p i p) })
}.

Section OGS.
  Variable spec : ogs_spec.

  Variant ogs_idx : Type :=
  | Player : spec.(idx_p) -> ogs_idx
  | Opponent : spec.(idx_o) -> ogs_idx
  .

  Variant ogs_qry : ogs_idx -> Type :=
  | StepP {i} : spec.(act_p) i -> ogs_qry (Player i)
  | StepO {i} : ogs_qry (Opponent i)
  .

  Equations ogs_rsp {i} : ogs_qry i -> Type :=
    ogs_rsp (StepP _) := T1 ;
    ogs_rsp (@StepO i) := spec.(act_o) i.

  Equations ogs_nxt {i} (q : ogs_qry i) : ogs_rsp q -> ogs_idx :=
    ogs_nxt (StepP pa) t1_0 := Opponent (spec.(nxt_p) _ pa) ;
    ogs_nxt (StepO)    oa   := Player (spec.(nxt_o) _ oa) .

  Definition e_ogs : event ogs_idx :=
    Event ogs_qry (@ogs_rsp) (@ogs_nxt).

  Equations ogs_leaf : ogs_idx -> Type :=
    ogs_leaf (Player i) := spec.(leaf_p) i ;
    ogs_leaf (Opponent i) := T0.

  Definition ogs {i} : spec.(conf_p) i -> itree e_ogs ogs_leaf (Player i).
    cofix _ogs.
    intro c_init.
    refine (translate _ eelim0 _ _ (spec.(play) _ c_init) ?>= _).
    refine (rec _).
    refine (fun mrec _).
    refine (rec ).
