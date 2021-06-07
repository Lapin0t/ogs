Set Equations Transparent.
From OGS Require Import Utils CatD EventD ITreeD RecD AngelicD.


Record ogs_spec : Type := OGS_SPEC {
  idx_p : Type ;                         (* index at player move *)
  idx_o : Type ;                         (* index at opponent move *)
  act_p : idx_p -> Type ;                 (* player actions *)
  act_o : idx_o -> Type ;                 (* opponent actions *)
  conf_p : idx_p -> Type ;                (* player states *)
  conf_o : idx_o -> Type ;                (* opponent states *)
  nxt_p : forall i, act_p i -> idx_o ;         (* player index transition *)
  nxt_o : forall i, act_o i -> idx_p ;         (* opponent index transition *)
  (* player state transition *)
  app_p : forall i (pa : act_p i), conf_p i -> conf_o (nxt_p i pa) ;
  (* opponent state transition *)
  app_o : forall i (oa : act_o i), conf_o i -> conf_p (nxt_o i oa) ;
  play : forall i, conf_p i -> comp (act_p i)  (* player action computation (strategy) *)
}.

Section OGS.
  Variable spec : ogs_spec.

  Variant ogs_idx : Type :=
  | Player : spec.(idx_p) -> ogs_idx
  | Opponent : spec.(idx_o) -> ogs_idx
  .

  Equations ogs_conf : ogs_idx -> Type :=
    ogs_conf (Player i) := spec.(conf_p) i ;
    ogs_conf (Opponent i) := spec.(conf_o) i .

  Equations ogs_qry : ogs_idx -> Type :=
    ogs_qry (Player i) := spec.(act_p) i ;
    ogs_qry (Opponent i) := T1.

  Equations ogs_rsp i : ogs_qry i -> Type :=
    ogs_rsp (Player i)   _ := T1 ;
    ogs_rsp (Opponent i) _ := spec.(act_o) i.

  Equations ogs_nxt i (q : ogs_qry i) : ogs_rsp i q -> ogs_idx :=
    ogs_nxt (Player i)   pa   _  := Opponent (spec.(nxt_p) _ pa) ;
    ogs_nxt (Opponent i) _    oa := Player (spec.(nxt_o) _ oa) .

  Definition e_ogs : event ogs_idx ogs_idx :=
    Event ogs_qry ogs_rsp ogs_nxt.

  Definition stepP {X i} (pa : spec.(act_p) i) t : itree e_ogs X (Player i) :=
    Vis (pa : qry e_ogs (Player i)) (fun 't1_0 => t).
  Definition stepO {X i} k : itree e_ogs X (Opponent i) :=
    Vis (t1_0 : qry e_ogs (Opponent i)) k.

  Definition ogs : ogs_conf ⇒ᵢ itree e_ogs (fun _ => T0) :=
    iter (fun i =>
      match i as i return (ogs_conf i -> itree _ _ i) with
      | Player i => fun c => emb_comp _ _ (spec.(play) i c)
                         !>= fun pa => stepP pa (Ret (inl (spec.(app_p) i pa c)))
      | Opponent i => fun c => stepO (fun oa => Ret (inl (spec.(app_o) i oa c)))
    end).
End OGS.
