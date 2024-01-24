(*|
Evaluation Structure (Definition 4.7)
=======================================
Abstract characterization of the evaluation structure of a programming
language.
We have here a minor mismatch between the formalization and the paper:
we have realized a posteriori a more elegant way to decompose the abstract
machine as exposed in the paper.
Here, instead of only requiring an embedding of normal forms into configurations,
we require an application function describing how to rebuild a configuration
from a value, an observation, and an assignment.
This less minimalist axiomatization puts the dependencies of our modules slightly
backwards compared to the paper's Section 4.
Here, evaluation structures, dubbed [machine]s, are parameterized by a substitution
monoid of values, a substitution module of configurations, and an observation structure,
instead of coming first.

Patching the development for following the paper's presentation would be slightly
technical due to the technicality of the mechanized proofs involved, but essentially
straightforward.

.. coq:: none
|*)
From OGS Require Import Prelude.
From OGS.Utils Require Import Ctx Rel.
From OGS.Game Require Import HalfGame Event.
From OGS.OGS Require Import Subst Obs.
From OGS.ITree Require Import Eq Delay.

Section withFam.
  Context {bT : baseT}.
  Context {bV : baseV}.
  Context {bC : baseC}.
  Context {sV : subst_monoid bV}.
  Context {sC : subst_module bV bC}.
  Context {oS : observation_structure}.

(*|
Evaluation structures, telling us how to evaluate a configuration,
 and how to stitch one back together from the data sent by Opponent.
|*)
  Class machine : Type := {
      eval {Γ} : conf Γ -> delay (nf' Γ) ;
      app {Γ x} (v : val Γ x) (m : obs x) (r : dom m ⇒ᵥ Γ) : conf Γ ;
    }.

  Context {M : machine}.

  Definition eval_to_obs {Γ} (t : conf Γ) : delay (obs∙ Γ) :=
    fmap_delay (obs'_of_nf' Γ) (eval t) .

(*|
The ≺ relation (Def 6.7)
|*)
  Variant head_inst_nostep (u : { x : typ & obs x }) : { x : typ & obs x } -> Prop :=
  | HeadInst {Γ y} (v : val Γ y) (m : obs y) (e : dom m ⇒ᵥ Γ) (p : is_var v -> False) (i : Γ ∋ projT1 u)
             : eval_to_obs (app v m e) ≊ ret_delay (projT1 u ,' (i , projT2 u)) ->
               head_inst_nostep u (y ,' m) .

(*|
Axiomatization of the machine
|*)
   Class machine_laws : Prop := {

(*|
[app] respects [ass_eq], to avoid relying on functional extensionality
|*)
       app_proper {Γ x v m} :: Proper (ass_eq (dom m) Γ ==> eq) (@app _ Γ x v m) ;

(*|
[app] commutes with substitution
|*)
        app_sub {Γ1 Γ2 x} (e : Γ1 ⇒ᵥ Γ2) (v : val Γ1 x) (m : obs x) (r : dom m ⇒ᵥ Γ1)
       : e ⊛ₜ app v m r = app (e ⊛ᵥ v) m (e ⊛ r) ;

(*|
Core hypothesis over the evaluator (Def 4.23):
"Substituting, then evaluating"
is equivalent to
"Evaluating, then substituting, then evaluating once more"
|*)
        eval_sub {Γ Δ} (c : conf Γ) (e : Γ ⇒ᵥ Δ)
       : eval (e ⊛ₜ c)
         ≋ bind_delay' (eval c) (fun u => eval (app (e _ (nf'_var u)) (nf'_obs u) (e ⊛ nf'_val u))) ;

(*|
Evaluating the embedding of a normal form is equivalent to returning the normal form (Def. 4.7)
|*)
     eval_nf_ret {Γ} (u : nf' Γ)
       : eval (app (v_var _ (nf'_var u)) (nf'_obs u) (nf'_val u))
         ≋ ret_delay u ;

(*|
The machine has finite redexes (§ 6.2). Necessary for establishing that the composition
can be defined by eventually guarded iteration.
|*)
    eval_app_not_var : well_founded head_inst_nostep ;
  } .

  Definition app' {Γ Δ} (u : Γ ⇒ᵥ Δ) (v : nf∙ Γ) : conf Δ :=
    app (u _ (nf'_var v)) (nf'_obs v) (u ⊛ nf'_val v) .

End withFam.
