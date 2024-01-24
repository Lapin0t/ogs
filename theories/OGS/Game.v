(*|
The OGS Game (§ 5.4)
=====================

|*)

From OGS Require Import Prelude.
From OGS.Utils Require Import Ctx Rel.
From OGS.Game Require Import HalfGame Event.
From OGS.OGS Require Import Subst Obs Machine.
From OGS.ITree Require Import ITree Eq Delay Structure Properties Guarded.

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

