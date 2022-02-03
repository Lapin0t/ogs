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

(*



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
