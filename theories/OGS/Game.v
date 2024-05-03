(*|
The OGS Game (§ 5.1 and 5.2)
==============================
|*)

From OGS Require Import Prelude.
From OGS.Utils Require Import Rel.
From OGS.Ctx Require Import All Ctx.
From OGS.OGS Require Import Obs.
From OGS.ITree Require Import Event ITree.

Reserved Notation "↓⁺ Ψ" (at level 9).
Reserved Notation "↓⁻ Ψ" (at level 9).
Reserved Notation "↓[ p ] Ψ" (at level 9).

(*|
Games (§ 5.1)
===============
Levy and Staton's general notion of game.
|*)

(*|
An half games (Def 5.1) is composed of "moves" as an indexed family of types,
and a [next] map computing the next index following a move.
|*)
Record half_game (I J : Type) := {
 g_move : I -> Type ;
 g_next : forall i, g_move i -> J
}.
Arguments g_move {I J h} i.
Arguments g_next {I J h i} m.

(*|
Action (h_actv) and reaction (h_pasv) functors (Def 5.8)
|*)
Definition h_actv {I J} (H : half_game I J) (X : psh J) : psh I :=
  fun i => { m : H.(g_move) i & X (H.(g_next) m) } .

Definition h_actvR {I J} (H : half_game I J) {X Y : psh J} (R : relᵢ X Y)
  : relᵢ (h_actv H X) (h_actv H Y) :=
  fun i u v => exists p : projT1 u = projT1 v , R _ (rew p in projT2 u) (projT2 v) .

Definition h_pasv {I J} (H : half_game I J) (X : psh J) : psh I :=
  fun i => forall (m : H.(g_move) i), X (H.(g_next) m) .

Definition h_pasvR {I J} (H : half_game I J) {X Y : psh J} (R : relᵢ X Y)
  : relᵢ (h_pasv H X) (h_pasv H Y) := fun i u v => forall m, R _ (u m) (v m) .

(*|
A game (Def 5.4) is composed of two compatible half games.
|*)
Record game (I J : Type) : Type := {
  g_client : half_game I J ;
  g_server : half_game J I
}.
Arguments g_client {I J}.
Arguments g_server {I J}.

Definition e_of_g {I J} (G : game I J) : event I I :=
  {| e_qry := fun i => G.(g_client).(g_move) i ;
     e_rsp := fun i q => G.(g_server).(g_move) (G.(g_client).(g_next) q) ;
     e_nxt := fun i q r => G.(g_server).(g_next) r |} .

(*|
OGS Games (§ 5.2)
==================
|*)

Variant polarity : Type := Act | Pas .
Derive NoConfusion for polarity.

Equations p_switch : polarity -> polarity :=
  p_switch Act := Pas ;
  p_switch Pas := Act .
#[global] Notation "p ^" := (p_switch p) (at level 5).

Section with_param.
(*|
We consider an observation structure.
|*)
  Context `{CC : context T C} {obs : obs_struct T C}.

  Definition ogs_ctx := ctx C.

(*|
Interleaved contexts (Def 5.12)
Collapsing functions (Def 5.13)
|*)
  Equations join_pol : polarity -> ogs_ctx -> C :=
    join_pol Act ∅ₓ       := ∅ ;
    join_pol Act (Ψ ▶ₓ Γ) := join_pol Pas Ψ +▶ Γ ;
    join_pol Pas ∅ₓ       := ∅ ;
    join_pol Pas (Ψ ▶ₓ Γ) := join_pol Act Ψ .

  Notation "↓⁺ Ψ" := (join_pol Act Ψ).
  Notation "↓⁻ Ψ" := (join_pol Pas Ψ).
  Notation "↓[ p ] Ψ" := (join_pol p Ψ).

(*|
Half games and games (Def 5.15)
|*)
  Definition ogs_hg : half_game ogs_ctx ogs_ctx :=
    {| g_move Ψ := obs∙ ↓⁺Ψ ;
       g_next Ψ m := Ψ ▶ₓ m_dom m |} .

  Definition ogs_g : game ogs_ctx ogs_ctx :=
    {| g_client := ogs_hg ;
       g_server := ogs_hg  |} .

  Definition ogs_e : event ogs_ctx ogs_ctx := e_of_g ogs_g.

  Definition ogs_act (Δ : C) : psh ogs_ctx := itree ogs_e (fun _ => obs∙ Δ).
  Definition ogs_pas (Δ : C) : psh ogs_ctx := h_pasv ogs_hg (ogs_act Δ).

End with_param.

#[global] Notation "↓⁺ Ψ" := (join_pol Act Ψ).
#[global] Notation "↓⁻ Ψ" := (join_pol Pas Ψ).
#[global] Notation "↓[ p ] Ψ" := (join_pol p Ψ).
