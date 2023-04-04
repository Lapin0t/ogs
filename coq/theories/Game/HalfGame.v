From OGS Require Import Utils.

Record half_game (I J : Type) := {
    move : I -> Type ;
    next : forall i, move i -> J
}.
Arguments move {I J h} i.
Arguments next {I J h i} m.

Definition h_actv {I J} (H : half_game I J) (X : psh J) : psh I :=
  fun i => { m : H.(move) i & X (H.(next) m) } .

Definition h_pasv {I J} (H : half_game I J) (X : psh J) : psh I :=
  fun i => forall (m : H.(move) i), X (H.(next) m) .

Equations h_sync {I J} (H : half_game I J) {X Y : psh J}
          : ⦉ h_actv H X ×ᵢ h_pasv H Y ⦊ᵢ -> ⦉ Y ×ᵢ X ⦊ᵢ :=
  h_sync H (i ,' ((m ,' x) , k)) := (_ ,' (k m , x)) .
