From OGS Require Import Utils Ctx CatD EventD ITreeD RecD AngelicD.
From ExtLib.Data Require Import Nat Fin List Unit.
Set Primitive Projections.
Set Implicit Arguments.
Set Equations Transparent.

(* taking the "OGS" of an uniform event *)
Definition ogs {I J} (U : uniform_event I J)
           : event (I * list (kon U)) (J * list (kon U)) :=
  Event (fun '(j , ks) => u_qry U j)
        (fun '(j , ks) q => { i : _ & k_rsp U ((u_rsp U q ++ ks) .[i]) })
        (fun '(j , ks) q r => (k_nxt U (projT2 r) , u_rsp U q ++ ks)).

Definition ogs_conf {I} {U : uniform_event I I}
             (X : I -> Type) (ks : list (kon U)) : Type :=
  dvec (fun k => forall r : k_rsp U k, X (k_nxt U r)) ks.

Definition ogs_emb {I} {U : uniform_event I I} {X : I -> Type}
           : forall {i ks},
             ogs_conf (itree U X) ks
           -> itree U X i
           -> itree (ogs U) (X ∘ fst) (i , ks) :=
  cofix _ogs_emb i ks c x := match (observe x) with
    | RetF x => Ret (x : X (fst (i , ks)))
    | TauF t => Tau (_ogs_emb i ks c t)
    | VisF e k => Vis (e : qry (ogs U) (i , ks)) (fun r =>
                   let c' := d_concat _ _ c (curry2' k) in
                   _ogs_emb _ _ c' (d_get _ c' _ _))
    end.

From OGS Require Import EqD.

Definition eutt_conf {I} {U : uniform_event I I} {X ks}
           : ogs_conf (itree U X) ks -> ogs_conf (itree U X) ks -> Prop :=
  fun c0 c1 => forall i (r : k_rsp U (ks .[i])), d_get ks c0 i r ≈ d_get ks c1 i r.

Theorem ogs_sound {I} {U : uniform_event I I} {X i ks}
        (c0 c1 : ogs_conf (itree U X) ks) (a b : itree U X i)
        : ogs_emb c0 a ≈ ogs_emb c1 b -> eutt_conf c0 c1 * (a ≈ b).
Admitted.

Theorem ogs_complete {I} {U : uniform_event I I} {X i ks}
        (c0 c1 : ogs_conf (itree U X) ks) (a b : itree U X i)
        : (a ≈ b) -> eutt_conf c0 c1 -> ogs_emb c0 a ≈ ogs_emb c1 b.
Admitted.
