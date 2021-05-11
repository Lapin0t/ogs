Variant enfE_qry (n : nat) : Type := | ENValQ
| ENRedexQ (i : fin n).

Equations enfE_rsp {n} : enfE_qry n -> Type :=
  enfE_rsp (ENValQ) := fin 1 ;
  enfE_rsp (ENRedexQ i) := fin 2.

Equations enfE_nxt {n} (q : enfE_qry n) (r : enfE_rsp q) : nat :=
  @enfE_nxt n ENValQ F0 := n ;
  @enfE_nxt n (ENRedexQ i) F0 := (S n) ;
  @enfE_nxt n (ENRedexQ i) (FS F0) := n.

Variant K_ty : Type := KCtx | KVal.
Definition scope : Type := list (K_ty * nat).

Variant term : Type :=.
Variant ogsI : Type :=
| Player (s : scope) (n : nat)
| Opponent (s : scope).

Derive NoConfusion for ogsI.
  
Variant ogsE_q : ogsI -> Type :=
| PA {s n} : ogsE_q (Player s n)
| PQ {s n} : fin n -> ogsE_q (Player s n)
| OQ {s} : fin (length s) -> ogsE_q (Opponent s).

Equations ogsE_r {i} : ogsE_q i -> Type :=
  ogsE_r (@PA s n) := fin 1 ;
  ogsE_r (@PQ s n i) := fin 1 ;
  ogsE_r (@OQ s i) := fin 1 .

Equations ogsE_n {i} (q : ogsE_q i) : ogsE_r q -> ogsI :=
  @ogsE_n (Player s n) (@PA s n) F0 := Opponent (cons (KVal, n) s) ;
  ogsE_n (@PQ s n i) F0 := Opponent (cons (KVal , n) (cons (KCtx , S n) s));
  ogsE_n (@OQ s i) F0 := Player s (snd (l_get s i)).
