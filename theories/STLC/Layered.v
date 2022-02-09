Set Primitive Projections.

From Coq Require Import Logic.
Import EqNotations.
Require Import Psatz.

From ExtLib.Data Require Import List Fin.

From OGS Require Import Utils.
From OGS.ITree Require Import Cat Event Dual ITree Rec Angelic Eq.
From OGS.STLC Require Import Ctx Syntax.

From Equations Require Import Equations.
Set Equations Transparent.

Variant ctx_any {X} (P : X -> Type) (Γ : Ctx.ctx X) : Type :=
| CAny {x} : Γ ∋ x -> P x -> ctx_any P Γ
.

Definition enf_answer : half_game ty neg_ctx :=
  {| move := a_val ;
     next := @a_cext |} .

Definition enf_question : half_game neg_ty (neg_ctx * ty) :=
  {| move := t_obs ;
     next := @t_obs_nxt |} .


(*

I = ty
J = neg_ty

TANS : I => list J
TREQ : J => list J * I

!TREQ ⊸ TANS

par : I => J -> list I => J

(t1 ⊗ t2 ⊗ t3) ⊸ t

par TREQ : list J => list J * I

AA := par TREQ + TANS : list J * I => list J * I + list J

par TREQ + TANS || join (par TREQ + TANS , par TREQ) 

BASE := TANS | par TREQ : I => list J => list J * I


 



the type game:
c_mv : I -> Type                    # a_val: type answer
c_nxt {i} : c_mv i -> list J        # a_cext: spawn *several* continuations
s_mv : J -> Type                    # ty_obs: server move on 1 given continuation
s_nxt {j} : s_mv j -> I             # ty_obs_goal: server transition to new goal
s_ext {j} : s_mv j -> list J        # ty_obs_args: spawning new continuations


*)

Definition frame : Type := neg_ctx * ty.

Variant enf_play (Γ : neg_ctx) : option ty -> Type :=
| RET {x} : a_val x -> enf_play Γ (Some x)
| CALL {x} {y : neg_ty} : (Γ : ctx) ∋ (y : ty) -> t_obs y -> enf_play Γ x
.
Arguments RET {Γ x} v.
Arguments CALL {Γ x y} i o.

Record v_kont : Type := VKont { vk_ctx : neg_ctx ;
                                vk_ty : ty }.
Record c_kont : Type := CKont { ck_ctx : neg_ctx ;
                                ck_in : ty ;
                                ck_out : ty }.

Equations v_play : v_kont -> Type := 
