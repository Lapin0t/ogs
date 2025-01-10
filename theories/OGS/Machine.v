(*|
Evaluation structure and language machine
=========================================

In this file we pull everything together and define evaluation structures and
the abstract characterization of a language machine, together with all the associated
laws.

Note that we have here a minor mismatch between the formalization and the paper:
we have realized a posteriori a more elegant way to decompose the abstract
machine as exposed in the paper.

Here, instead of only requiring an embedding of normal forms into
configurations (``refold``, from Def. 11), we require an *observation
application* function ``oapp`` describing how to build a configuration
from a value, an observation, and an assignment. Since normal forms are triples
of a variable, an observation and an assignment, the sole difference is in the
first component: instead of just a variable, ``oapp`` takes any value. Both
are easily interdefineable. While ``refold`` is more compact to introduce,
it is slightly more cumbersome to work with, which is why we axiomatize ``oapp``
directly.

Patching the development to follow more closely the paper's presentation would be slightly
technical due to the technicality of the mechanized proofs involved, but essentially
straightforward.

.. coq:: none
|*)
From OGS Require Import Prelude.
From OGS.Utils Require Import Rel.
From OGS.Ctx Require Import All Subst.
From OGS.OGS Require Import Obs.
From OGS.ITree Require Import Event Eq Delay.

Section with_param.
  Context `{CC : context T C}.
(*|
We here define what is called an evaluation structure in the paper (Def. 11). It tells
us how to evaluate a configuration to a normal form and how to stitch one back together
from the data sent by Opponent. 

.. coq::
   :name: machine
|*)
Class machine (val : Fam₁ T C) (conf : Fam₀ T C) (obs : obs_struct T C) := {
  eval : conf ⇒₀ (delay ∘ nf obs val) ;
  oapp [Γ x] (v : val Γ x) (o : obs x) : dom o =[val]> Γ -> conf Γ ;
}.
(*|
.. coq:: none
|*)
#[global] Arguments eval {_ _ _ _} [_].
#[global] Arguments oapp {_ _ _ _} [_ _].
(*|
Next we define "evaluating then observing" (Def. 14).

.. coq::
   :name: evalobs
|*)
Definition evalₒ `{machine val conf obs}
  : conf ⇒₀ (delay ∘ obs∙) :=
  fun _ t => then_to_obs (eval t) .
(*|
.. coq:: none
|*)
#[global] Arguments evalₒ {_ _ _ _} [_].
(*|
|*)
Notation "v ⊙ o ⦗ a ⦘" := (oapp v o a) (at level 20).
(*|
We can readily define the embedding from normal forms to configurations (i.e., we can
derive what is called ``refold`` in the paper).

.. coq::
   :name: embed
|*)
Definition emb `{machine val conf obs} {_ : subst_monoid val}
  : nf obs val ⇒₀ conf
  := fun _ n => oapp (v_var (nf_var n)) (nf_obs n) (nf_args n) .
(*|
.. coq:: none
|*)
#[global] Arguments emb {_ _ _ _ _} [_].
(*|
Next we define the "bad instanciation" relation (Def. 28).

.. coq::
   :name: badinst
|*)
Variant head_inst_nostep `{machine val conf obs} {VM : subst_monoid val} 
        (u : sigT obs) : sigT obs -> Prop :=
| HeadInst {Γ y} (v : val Γ y) (o : obs y) (a : dom o =[val]> Γ) (i : Γ ∋ projT1 u)
    : ¬(is_var v)
    -> evalₒ (v ⊙ o⦗a⦘) ≊ ret_delay (i ⋅ projT2 u)
    -> head_inst_nostep u (y ,' o) .
(*|
Finally we define the structure containing all the remaining axioms of a language
machine (Def. 13).
|*)
Class machine_laws val conf obs {M : machine val conf obs}
  {VM : subst_monoid val} {CM : subst_module val conf} := {
(*|
``oapp`` respects pointwise equality of assignments.
|*)
   oapp_proper {Γ x} {v : val Γ x} {o} :: Proper (asgn_eq (dom o) Γ ==> eq) (oapp v o) ;
(*|
``oapp`` commutes with substitutions. This is the equivalent of the second
equation at the end of Def. 13, in terms of ``oapp`` instead of ``refold``.

.. coq::
   :name: evalrespsub
|*)
   app_sub {Γ1 Γ2 x} (v : val Γ1 x) (o : obs x) (a : dom o =[val]> Γ1) (b : Γ1 =[val]> Γ2)
   : (v ⊙ o⦗a⦘) ₜ⊛ b = (v ᵥ⊛ b) ⊙ o⦗a ⊛ b⦘ ;
(*|
"evaluation respects substitution". This is the core hypothesis of the OGS
soundness, stating essentially "substituting, then evaluating" is equivalent to
"evaluating, then substituting, then evaluating once more". It is the equvalent
of the first equation at the end of Def. 13.

.. coq::
|*)
   eval_sub {Γ Δ} (c : conf Γ) (a : Γ =[val]> Δ)
   : eval (c ₜ⊛ a) ≋ bind_delay' (eval c) (fun n => eval (emb n ₜ⊛ a)) ;
(*|
Evaluating the embedding of a normal form is equivalent to returning the normal
form. This is part of the evaluation structure (Def. 11) in the paper.

.. coq::
|*)
   eval_nf_ret {Γ} (u : nf obs val Γ)
   : eval (emb u) ≋ ret_delay u ;
(*|
At last the mystery hypothesis, stating that the machine has focused redexes (Def. 28).
It is necessary for establishing that the composition can be defined by eventually
guarded iteration.

.. coq::
|*)
    eval_app_not_var : well_founded head_inst_nostep ;
  } .
End with_param.
(*|
Finally we define a cute notation for applying an observation to a value.
|*)
#[global] Notation "v ⊙ o ⦗ a ⦘" := (oapp v o a) (at level 20).
