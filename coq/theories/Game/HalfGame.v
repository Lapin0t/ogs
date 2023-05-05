Import EqNotations.
From OGS Require Import Utils.
From OGS.Utils Require Import Rel.

Record half_game (I J : Type) := {
 g_move : I -> Type ;
 g_next : forall i, g_move i -> J
}.
Arguments g_move {I J h} i.
Arguments g_next {I J h i} m.

Definition h_actv {I J} (H : half_game I J) (X : psh J) : psh I :=
  fun i => { m : H.(g_move) i & X (H.(g_next) m) } .

Definition h_actvR {I J} (H : half_game I J) {X Y : psh J} (R : relᵢ X Y)
  : relᵢ (h_actv H X) (h_actv H Y) :=
  fun i u v => exists p : projT1 u = projT1 v , R _ (rew p in projT2 u) (projT2 v) .

Definition h_pasv {I J} (H : half_game I J) (X : psh J) : psh I :=
  fun i => forall (m : H.(g_move) i), X (H.(g_next) m) .

Definition h_pasvR {I J} (H : half_game I J) {X Y : psh J} (R : relᵢ X Y)
  : relᵢ (h_pasv H X) (h_pasv H Y) := fun i u v => forall m, R _ (u m) (v m) .

Equations h_sync {I J} (H : half_game I J) {X Y : psh J}
          : ⦉ h_actv H X ×ᵢ h_pasv H Y ⦊ᵢ -> ⦉ Y ×ᵢ X ⦊ᵢ :=
  h_sync H (i ,' ((m ,' x) , k)) := (_ ,' (k m , x)) .

Record game (I J : Type) : Type := {
  g_client : half_game I J ;
  g_server : half_game J I
}.
Arguments g_client {I J}.
Arguments g_server {I J}.

From OGS.Game Require Import Event.

Definition e_of_g {I J} (G : game I J) : event I I :=
  {| e_qry := fun i => G.(g_client).(g_move) i ;
     e_rsp := fun i q => G.(g_server).(g_move) (G.(g_client).(g_next) q) ;
     e_nxt := fun i q r => G.(g_server).(g_next) r |} .
