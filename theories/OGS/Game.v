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

An half games (Def 5.1) is composed of "moves" as an indexed family of types,
and a "next" map computing the next index following a move.

.. coq::
   :name: halfgame
|*)
Record half_game (I J : Type) := {
 g_move : I -> Type ;
 g_next : forall i, g_move i -> J
}.
(*|
.. coq:: none
|*)
Arguments g_move {I J h} i.
Arguments g_next {I J h i} m.
(*|
Action (h_actv) and reaction (h_pasv) functors (Def 5.8)

.. coq::
   :name: actionreaction
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

.. coq::
   :name: game
|*)
Record game (I J : Type) : Type := {
  g_client : half_game I J ;
  g_server : half_game J I
}.
(*|
.. coq:: none
|*)
Arguments g_client {I J}.
Arguments g_server {I J}.
(*|
Given a game, we can construct an ``event``. See `ITree/Event.v <Event.html>`_
|*)
Definition e_of_g {I J} (G : game I J) : event I I :=
  {| e_qry := fun i => G.(g_client).(g_move) i ;
     e_rsp := fun i q => G.(g_server).(g_move) (G.(g_client).(g_next) q) ;
     e_nxt := fun i q r => G.(g_server).(g_next) r |} .
(*|
The OGS Game (§ 5.2)
====================

First let us define a datatype for polarities, active and passive (called "waiting") in
the paper.
|*)
Variant polarity : Type := Act | Pas .
Derive NoConfusion for polarity.

Equations p_switch : polarity -> polarity :=
  p_switch Act := Pas ;
  p_switch Pas := Act .
#[global] Notation "p ^" := (p_switch p) (at level 5).

Section with_param.
(*|
We consider an observation structure, given by a set of types ``T``, a notion of contexts
``C`` and a operator giving the observations and their domain. See
`Ctx/Family.v <Family.html#oper>`_ and `OGS/Obs.v <Obs.html>`_.
|*)
  Context `{CC : context T C} {obs : obs_struct T C}.
(*|
Interleaved contexts (Def 5.12) are given by the free context structure over ``C``.

.. coq::
   :name: ogsctx
|*)
  Definition ogs_ctx := ctx C.
(*|
We define the collapsing functions (Def 5.13).

.. coq::
   :name: ctxcollapse
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
Finally we define the OGS half-game and game (Def 5.15).

.. coq::
   :name: ogsgame
|*)
  Definition ogs_hg : half_game ogs_ctx ogs_ctx :=
    {| g_move Ψ := obs∙ ↓⁺Ψ ;
       g_next Ψ m := Ψ ▶ₓ m_dom m |} .

  Definition ogs_g : game ogs_ctx ogs_ctx :=
    {| g_client := ogs_hg ;
       g_server := ogs_hg  |} .
(*|
We define the event of OGS moves.
|*)
  Definition ogs_e : event ogs_ctx ogs_ctx := e_of_g ogs_g.
(*|
And finally we define active OGS strategies and passive OGS strategies.

.. coq::
   :name: ogsstrat
|*)
  Definition ogs_act (Δ : C) : psh ogs_ctx := itree ogs_e (fun _ => obs∙ Δ).
  Definition ogs_pas (Δ : C) : psh ogs_ctx := h_pasv ogs_hg (ogs_act Δ).

End with_param.

#[global] Notation "↓⁺ Ψ" := (join_pol Act Ψ).
#[global] Notation "↓⁻ Ψ" := (join_pol Pas Ψ).
#[global] Notation "↓[ p ] Ψ" := (join_pol p Ψ).
