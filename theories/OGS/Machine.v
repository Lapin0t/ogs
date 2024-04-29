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

(*|
Evaluation structures, telling us how to evaluate a configuration,
and how to stitch one back together from the data sent by Opponent.
|*)
Class machine {T} (val : Fam₁ T) (conf : Fam T) (obs : obs_struct T) : Type := {
  eval : conf ⇒₀ (delay ∘ nf obs val) ;
  app : (val ∥ obs#val) ⇒₀ conf ;
}.
#[global] Arguments eval {_ _ _ _ _} [_].
#[global] Arguments app {_ _ _ _ _} [_].

Definition eval_to_obs `{machine T val conf obs} : conf ⇒₀ (delay ∘ obs∙) :=
  fun _ t => then_to_obs (eval t) .

Definition app' `{machine T val conf obs} {Γ x} v (o : obs x) (a : dom o =[val]> Γ)
  := app (Cut v (OFill o a)) .   

Definition emb `{machine T val conf obs} `{subst_monoid T val} : nf obs val ⇒₀ conf
  := app ⦿₀ (f_cut_map v_var f_id₁) .
#[global] Arguments emb {_ _ _ _ _ _} [_] _ /.

(*|
The ≺ relation (Def 6.7)
|*)
Variant head_inst_nostep `{machine T val conf obs} `{subst_monoid T val} 
        (u : sigT obs) : sigT obs -> Prop :=
| HeadInst {Γ y} (v : val y Γ) (_ : ¬(is_var v)) (m : obs y) (a : dom m =[val]> Γ)
      (i : projT1 u ∈ Γ) (_ : eval_to_obs _ (app' v m a) ≊ ret_delay (Cut i (projT2 u)))
    : head_inst_nostep u (y ,' m) .

(*|
Axiomatization of the machine
|*)
 Class machine_laws `{machine T val conf obs} `{subst_monoid T val} `{subst_module T val conf}: Prop := {

(*|
[app] respects [asgn_eq], to avoid relying on functional extensionality
|*)
   (*app_proper {Γ x v m} :: Proper (asgn_eq (dom m) Γ ==> eq) (@app _ Γ x v m) ;*)

(*|
[app] commutes with substitution
|*)
   app_sub {Γ1 Γ2 x} (e : Γ1 =[val]> Γ2) (v : val x Γ1) (m : obs x) (r : dom m =[val]> Γ1)
   : app' v m r ₜ⊛ e = app' (v ᵥ⊛ e) m (r ⊛ e) ;

(*|
Core hypothesis over the evaluator (Def 4.23):
"Substituting, then evaluating"
is equivalent to
"Evaluating, then substituting, then evaluating once more"
|*)
   eval_sub {Γ Δ} (c : conf Γ) (e : Γ =[val]> Δ)
   : eval (c ₜ⊛ e)
     ≋ bind_delay' (eval c) (fun n => eval (emb n ₜ⊛ e)) ;

(*|
Evaluating the embedding of a normal form is equivalent to returning the normal form (Def. 4.7)
|*)
   eval_nf_ret {Γ} (u : nf obs val Γ)
   : eval (emb u)
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
