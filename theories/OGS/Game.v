(*|
The OGS Game (§ 5.1 and 5.2)
==============================
|*)

From OGS Require Import Prelude.
From OGS.Utils Require Import Ctx Rel.
From OGS.OGS Require Import Subst Obs Machine.
From OGS.ITree Require Import Event ITree Eq Delay Structure Properties Guarded.

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

Equations h_sync {I J} (H : half_game I J) {X Y : psh J}
          : ⦉ h_actv H X ×ᵢ h_pasv H Y ⦊ᵢ -> ⦉ Y ×ᵢ X ⦊ᵢ :=
  h_sync H (i ,' ((m ,' x) , k)) := (_ ,' (k m , x)) .

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

Section withFam.

(*|
We consider a language abstractly captured as a machine
|*)
  Context {bT : baseT}.
  Context {bV : baseV}.
  Context {bC : baseC}.
  Context {sV : subst_monoid bV}.
  Context {sC : subst_module bV bC}.
  Context {oS : observation_structure}.
  Context {M: machine}.
(*|
Satisfying an appropriate axiomatization
|*)
  Context {sVL: subst_monoid_laws}.
  Context {sCL: subst_module_laws}.
  Context {VA : var_assumptions} .
  Context {ML: machine_laws}.

(*|
Interleaved contexts (Def 5.12)
Collapsing functions (Def 5.13, see Utils/Ctx.v for auxiliary definitions)
|*)
  Definition alt_ext : Type := ctx (context).
  Notation "↓⁺ a" := (join_even a) (at level 9).
  Notation "↓⁻ a" := (join_odd a) (at level 9).
  Notation "↓[ b ] a" := (join_even_odd_aux b a) (at level 9).

(*|
Half games and games (Def 5.15)
|*)
  Definition ogs_hg : half_game alt_ext alt_ext :=
    {| g_move := fun es => obs∙ ↓⁺es ;
       g_next := fun es m => (es ▶ dom∙ m) |} .

  Definition ogs_g : game alt_ext alt_ext :=
    {| g_client := ogs_hg ;
       g_server := ogs_hg  |} .

  Definition ogs_e : event alt_ext alt_ext := e_of_g ogs_g.

  Definition ogs_act (Δ : context) : psh alt_ext := itree ogs_e (fun _ => obs∙ Δ).
  Definition ogs_pas (Δ : context) : psh alt_ext := h_pasv ogs_hg (ogs_act Δ).

End withFam.

Notation "↓⁺ a" := (join_even a) (at level 9).
Notation "↓⁻ a" := (join_odd a) (at level 9).
Notation "↓[ b ] a" := (join_even_odd_aux b a) (at level 9).
Notation "Ⓟ" := true.
Notation "Ⓞ" := false.

