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
monoid of values, a substitution module of configurations, and an observation structure, instead of coming first.

Patching the development for following the paper's presentation would be slightly
technical due to the technicality of the mechanized proofs involved, but essentially
straightforward.

.. coq:: none
|*)
From OGS Require Import Prelude.
From OGS.Utils Require Import Rel.
From OGS.Ctx Require Import All.
From OGS.OGS Require Import Subst Obs.
From OGS.ITree Require Import Event Eq Delay.

Section with_param.
  Context `{CC : context T C}.

(*|
Evaluation structures, telling us how to evaluate a configuration,
and how to stitch one back together from the data sent by Opponent.
|*)
Class machine (val : Fam₁ T C) (conf : Fam₀ T C) (obs : obs_struct T C) := {
  eval : conf ⇒₀ (delay ∘ nf obs val) ;
  oapp [Γ x] (v : val Γ x) (o : obs x) : dom o =[val]> Γ -> conf Γ ;
}.
#[global] Arguments eval {_ _ _ _} [_].
#[global] Arguments oapp {_ _ _ _} [_ _].

Definition evalₒ `{machine val conf obs}
  : conf ⇒₀ (delay ∘ obs∙) :=
  fun _ t => then_to_obs (eval t) .
#[global] Arguments evalₒ {_ _ _ _} [_].

Notation "v ⊙ o ⦗ a ⦘" := (oapp v o a) (at level 20).

Definition emb `{machine val conf obs} {_ : subst_monoid val}
  : nf obs val ⇒₀ conf
  := fun _ n => oapp (v_var (nf_var n)) (nf_obs n) (nf_args n) .
#[global] Arguments emb {_ _ _ _ _} [_].

(*|
The ≺ relation (Def 6.7)
|*)
Variant head_inst_nostep `{machine val conf obs} {VM : subst_monoid val} 
        (u : sigT obs) : sigT obs -> Prop :=
| HeadInst {Γ y} (v : val Γ y) (o : obs y) (a : dom o =[val]> Γ) (i : Γ ∋ projT1 u)
    : ¬(is_var v)
    -> evalₒ (v ⊙ o⦗a⦘) ≊ ret_delay (i ⋅ projT2 u)
    -> head_inst_nostep u (y ,' o) .

(*|
Axiomatization of the machine
|*)
Class machine_laws val conf obs {M : machine val conf obs} {VM : subst_monoid val}
      {CM : subst_module val conf} := {

(*|
[app] respects [asgn_eq], to avoid relying on functional extensionality
|*)
   oapp_proper {Γ x} {v : val Γ x} {o} :: Proper (asgn_eq (dom o) Γ ==> eq) (oapp v o) ;

(*|
[app] commutes with substitution
|*)
   app_sub {Γ1 Γ2 x} (v : val Γ1 x) (o : obs x) (a : dom o =[val]> Γ1) (b : Γ1 =[val]> Γ2)
   : (v ⊙ o⦗a⦘) ₜ⊛ b = (v ᵥ⊛ b) ⊙ o⦗a ⊛ b⦘ ;

(*|
Core hypothesis over the evaluator (Def 4.23): "Substituting, then evaluating"
is equivalent to "Evaluating, then substituting, then evaluating once more"
|*)
   eval_sub {Γ Δ} (c : conf Γ) (a : Γ =[val]> Δ)
   : eval (c ₜ⊛ a) ≋ bind_delay' (eval c) (fun n => eval (emb n ₜ⊛ a)) ;

(*|
Evaluating the embedding of a normal form is equivalent to returning the normal
form (Def. 4.7)
|*)
   eval_nf_ret {Γ} (u : nf obs val Γ)
   : eval (emb u) ≋ ret_delay u ;

(*|
The machine has finite redexes (§ 6.2). Necessary for establishing that the composition
can be defined by eventually guarded iteration.
|*)
    eval_app_not_var : well_founded head_inst_nostep ;
  } .

(*
  Definition app' {Γ Δ} (u : Γ ⇒ᵥ Δ) (v : nf∙ Γ) : conf Δ :=
    app (u _ (nf'_var v)) (nf'_obs v) (u ⊛ nf'_val v) .
*)

End with_param.

#[global] Notation "v ⊙ o ⦗ a ⦘" := (oapp v o a) (at level 20).
