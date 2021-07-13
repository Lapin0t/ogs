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

Definition ogs_emb {I} {U : uniform_event I I} {X : I -> Type}
           : forall {i ks}, itree U X i
           -> dvec (fun k => forall r : k_rsp U k, itree U X (k_nxt U r)) ks
           -> itree (ogs U) (X ∘ fst) (i , ks) :=
  cofix _ogs_emb i ks x c := match (observe x) with
    | RetF x => Ret (x : X (fst (i , ks)))
    | TauF t => Tau (_ogs_emb i ks t c)
    | VisF e k => Vis (e : qry (ogs U) (i , ks)) (fun r =>
                   let c' := d_concat ks (u_rsp U e) c (fun i r => k (i ,& r)) in
                   _ogs_emb _ _ (d_get _ c' _ _) c')
    end.
