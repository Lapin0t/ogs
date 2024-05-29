(*|
A Minimal Example: Call-by-Value Simply Typed Lambda Calculus
=============================================================

We demonstrate how to instantiate our framework to define the OGS associated
to the CBV λ-calculus. With the instance comes the proof that bisimilarity of
the OGS entails substitution equivalence, which coincides with
CIU-equivalence.

.. note:: This example is designed to be minimal, hiding by nature some
   difficulties. In particular it has no positive types, which simplifies the
   development a lot.

.. coq:: none
|*)
From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.
From OGS.Ctx Require Import All Ctx Covering.
From OGS.ITree Require Import ITree Delay.
From OGS.OGS Require Import Subst Obs Soundness.
(*|
Syntax
------

Types
^^^^^

As discussed in the paper, our framework applies not really to a language but
more to an abstract machine. In order to ease this instanciation, we will
focus directly on a CBV machine and define evaluation contexts early on.
Working with intrinsically typed syntax, we need to give types to these
contexts: we will type them by the "formal negation" of the type of their
hole. In order to do so we first define the usual types `ty0` of STLC with
functions and a ground type.
|*)
Declare Scope ty_scope .
Inductive ty0 : Type :=
| ι : ty0
| Arr : ty0 -> ty0 -> ty0
.
Notation "A → B" := (Arr A B) (at level 40) : ty_scope .
(*|
.. coq:: none
|*)
Derive NoConfusion for ty0 .
Delimit Scope ty_scope with ty .
Bind Scope ty_scope with ty0 .
(*|
We then define "tagged types", where `t+ a` will be the type of terms of type
`a`, and `t- a` the type of evaluation contexts of hole `a`.
|*)
Variant ty : Type :=
| VTy : ty0 -> ty
| KTy : ty0 -> ty
.
Notation "+ t" := (VTy t) (at level 5) : ty_scope .
Notation "¬ t" := (KTy t) (at level 5) : ty_scope .
Coercion VTy : ty0 >-> ty .
(*|
.. coq:: none
|*)
Derive NoConfusion for ty .
Bind Scope ty_scope with ty .
Open Scope ty_scope .
(*|
Typing Contexts
^^^^^^^^^^^^^^^

Typing contexts are now simply defined as lists of tagged types. This is
perhaps the slightly surprising part: contexts will now contain "continuation
variables". Rest assured terms will make no use of them. These are solely
needed for evaluation contexts: as they are only typed with their hole, we are
missing the type of their outside. We fix this problem by *naming* the outside
and make evaluation contexts end with a continuation variable.

.. note:: Our choices make a bit more sense if we realize that what we are
   writing is exactly the subset of λμ-calculus that is the image of the CBV
   translation from λ-calculus.

..
|*)
Definition t_ctx : Type := ctx ty .
(*|
.. coq:: none
|*)
Bind Scope ctx_scope with t_ctx .
(*|
Terms and Values and ...
^^^^^^^^^^^^^^^^^^^^^^^^

We now have all that is needed to define terms, which we define mutually with
values. As discussed above, they are are indexed by a list of tagged types (of
which they only care about the non-negated elements) and by an untagged type.

The only fanciness is the recursive lambda abstraction, which we include to
safeguard ourselves from accidentally using the fact that the language is
strongly normalizing.
|*)
Inductive term (Γ : t_ctx) : ty0 -> Type :=
| Val {a} : val Γ a -> term Γ a
| App {a b} : term Γ (a → b) -> term Γ a -> term Γ b
with val (Γ : t_ctx) : ty0 -> Type :=
| Var {a} : Γ ∋ + a -> val Γ a
| TT : val Γ ι
| Lam {a b} : term (Γ ▶ₓ (a → b) ▶ₓ a) b -> val Γ (a → b)
.
(*|
.. coq:: none
|*)
Arguments Val {Γ a} v .
Arguments App {Γ a b} t1 t2 .
Arguments Var {Γ a} i .
Arguments TT {Γ} .
Arguments Lam {Γ a b} t .
#[global] Coercion Val : val >-> term.
(*|
Evaluation contexts follow. As discussed, there is a "covariable" case, to
"end" the context. The other cases are usual: evaluating the argument of an
application and evaluating the function.
|*)
Inductive ev_ctx (Γ : t_ctx) : ty0 -> Type :=
| K0 {a} : Γ ∋ ¬ a -> ev_ctx Γ a
| K1 {a b} : term Γ (a → b) -> ev_ctx Γ b -> ev_ctx Γ a
| K2 {a b} : val Γ a -> ev_ctx Γ b -> ev_ctx Γ (a → b)
.
(*|
.. coq:: none
|*)
Arguments K0 {Γ a} i .
Arguments K1 {Γ a b} t π .
Arguments K2 {Γ a b} v π .
(*|
Next are the machine states. They consist of an explicit cut and represent
a term in the process of being executed in some context. Notice how states
they are only indexed by a typing context: these are proper "diverging
programs".
|*)
Definition state := term ∥ₛ ev_ctx.
(*|
Finally the last of syntactic categories: "machine values". This category is
typed with a tagged type and encompasses both values (for non-negated types)
and evaluation contexts (for negated types). The primary use-case for this
category is to denote "things by which we can substitute (tagged) variables".

In fact when working with intrinsically-typed syntax, substitution is modelled
as a monoidal multiplication (see [AACMM21]_ and [FS22]_). We will prove later
that `val_m Γ` is indeed a monoid relative to `has Γ` and that contexts and
assignments form a category.
|*)
Equations val_m : t_ctx -> ty -> Type :=
  val_m Γ (+ a) := val Γ a ;
  val_m Γ (¬ a) := ev_ctx Γ a .
(*|
Together with machine values we define a smart constructor for "machine var",
embedding tagged variables into these generalized values. It conveniently
serves as the identity assignment, a fact we use to give it this mysterious
point-free style type, which desugars to `forall a, Γ ∋ a -> val_m Γ a`.
|*)
Equations a_id {Γ} : Γ =[val_m]> Γ :=
  a_id (+ _) i := Var i ;
  a_id (¬ _) i := K0 i .
(*|
Substitution and Renaming
-------------------------

In order to define substitution we first need to dance the intrinsically-typed
dance and define renamings, from which we will derive weakenings and then only
define substitution.

Renaming
^^^^^^^^

Lets write intrinsically-typed parallel renaming for all of our syntactic
categories! If you have never seen such intrinsically-typed definitions you
might be surprised by the absence of error-prone de-bruijn index manipulation.
Enjoy this beautiful syntax traversal!
|*)
Equations t_rename {Γ Δ} : Γ ⊆ Δ -> term Γ ⇒ᵢ term Δ :=
  t_rename f _ (Val v)     := Val (v_rename f _ v) ;
  t_rename f _ (App t1 t2) := App (t_rename f _ t1) (t_rename f _ t2) ;
with v_rename {Γ Δ} : Γ ⊆ Δ -> val Γ ⇒ᵢ val Δ :=
  v_rename f _ (Var i)    := Var (f _ i) ;
  v_rename f _ (TT)       := TT ;
  v_rename f _ (Lam t) := Lam (t_rename (r_shift2 f) _ t) .

Equations e_rename {Γ Δ} : Γ ⊆ Δ -> ev_ctx Γ ⇒ᵢ ev_ctx Δ :=
  e_rename f _ (K0 i)   := K0 (f _ i) ;
  e_rename f _ (K1 t π) := K1 (t_rename f _ t) (e_rename f _ π) ;
  e_rename f _ (K2 v π) := K2 (v_rename f _ v) (e_rename f _ π) .

Equations s_rename {Γ Δ} : Γ ⊆ Δ -> state Γ -> state Δ :=
  s_rename f (Cut t π) := Cut (t_rename f _ t) (e_rename f _ π).

Equations m_rename {Γ Δ} : Γ ⊆ Δ -> val_m Γ ⇒ᵢ val_m Δ :=
  m_rename f (+ _) v := v_rename f _ v ;
  m_rename f (¬ _) π := e_rename f _ π .

#[global] Arguments s_rename _ _ _ /.
#[global] Arguments m_rename _ _ _ /.
(*|
We can recast `m_rename` as an operator on assigments, more precisely as
renaming an assigment on the left.
|*)
Definition a_ren {Γ1 Γ2 Γ3} : Γ2 ⊆ Γ3 -> Γ1 =[val_m]> Γ2 -> Γ1 =[val_m]> Γ3 :=
  fun f g _ i => m_rename f _ (g _ i) .
(*|
The following bunch of notations will help us to keep the code readable:
|*)
Notation "t ₜ⊛ᵣ r" := (t_rename r%asgn _ t) (at level 14).
Notation "v ᵥ⊛ᵣ r" := (v_rename r%asgn _ v) (at level 14).
Notation "π ₑ⊛ᵣ r" := (e_rename r%asgn _ π) (at level 14).
Notation "v ₘ⊛ᵣ r" := (m_rename r%asgn _ v) (at level 14).
Notation "s ₛ⊛ᵣ r" := (s_rename r%asgn s) (at level 14).
Notation "a ⊛ᵣ r" := (a_ren r%asgn a) (at level 14) : asgn_scope.
(*|
As discussed above, we can now obtain our precious weakenings. Here are the
three we will need.
|*)
Definition t_shift {Γ a} := @t_rename Γ (Γ ▶ₓ a) r_pop.
Definition m_shift2 {Γ a b} := @m_rename Γ (Γ ▶ₓ a ▶ₓ b) (r_pop ᵣ⊛ r_pop).
Definition a_shift2 {Γ Δ a b} (f : Γ =[val_m]> Δ)
  : (Γ ▶ₓ a ▶ₓ b) =[val_m]> (Δ ▶ₓ a ▶ₓ b)
  := [ [ a_map f m_shift2 ,ₓ a_id a (pop top) ] ,ₓ a_id b top ].
(*|
Substitutions
^^^^^^^^^^^^^

With weakenings in place we are now equipped to define substitutions. This
goes pretty much like renaming. We have abstained from defining generic syntax
traversal tools like Allais et al's "Kits" to keep our example minimal... And
incidentally showcase the intrinsically-typed style with Matthieu Sozeau's
Equations.
|*)
Equations t_subst {Γ Δ} : Γ =[val_m]> Δ -> term Γ ⇒ᵢ term Δ :=
  t_subst f _ (Val v)     := Val (v_subst f _ v) ;
  t_subst f _ (App t1 t2) := App (t_subst f _ t1) (t_subst f _ t2) ;
with v_subst {Γ Δ} : Γ =[val_m]> Δ -> val Γ ⇒ᵢ val Δ :=
  v_subst f _ (Var i)    := f _ i ;
  v_subst f _ (TT)       := TT ;
  v_subst f _ (Lam t) := Lam (t_subst (a_shift2 f) _ t) .

Equations e_subst {Γ Δ} : Γ =[val_m]> Δ -> ev_ctx Γ ⇒ᵢ ev_ctx Δ :=
  e_subst f _ (K0 i)   := f _ i ;
  e_subst f _ (K1 t π) := K1 (t_subst f _ t) (e_subst f _ π) ;
  e_subst f _ (K2 v π) := K2 (v_subst f _ v) (e_subst f _ π) .
(*|
These notations will make everything shine.
|*)
Notation "t `ₜ⊛ a" := (t_subst a%asgn _ t) (at level 30).
Notation "v `ᵥ⊛ a" := (v_subst a%asgn _ v) (at level 30).
Notation "π `ₑ⊛ a" := (e_subst a%asgn _ π) (at level 30).
(*|
These two last substitutions, for states and generalized values, are the ones
we will give to the abstract interface. For categorical abstraction reasons,
the abstract interface has the argument reversed for substitutions: first
the state or value, then the assignment as second argument. To ease instanciation
we will hence do so too. The type is given with tricky combinators but expands to:

  m_subst Γ a : val_m Γ a -> forall Δ, Γ =[val_m]> Δ -> val_m Δ a

|*)
Equations m_subst : val_m ⇒₁ ⟦ val_m , val_m ⟧₁ :=
  m_subst _ (+ _) v _ f := v `ᵥ⊛ f ;
  m_subst _ (¬ _) π _ f := π `ₑ⊛ f .

Definition s_subst : state ⇒₀ ⟦ val_m , state ⟧₀ :=
  fun _ s _ f => (s.(cut_l) `ₜ⊛ f) ⋅ (s.(cut_r) `ₑ⊛ f).
#[global] Arguments s_subst _ _ /.
(*|
We can now instanciate the substitution monoid and module structures.
|*)
#[global] Instance val_m_monoid : subst_monoid val_m :=
  {| v_var := @a_id ; v_sub := m_subst |} .
#[global] Instance state_module : subst_module val_m state :=
  {| c_sub := s_subst |} .
(*|
Finally we define a more usual substitution function which only substitutes
the top two variables instead of doing parallel substitution.
|*)
Definition assign2 {Γ a b} v1 v2
  : (Γ ▶ₓ a ▶ₓ b) =[val_m]> Γ
  := [ [ a_id ,ₓ v1 ] ,ₓ v2 ] .
Definition t_subst2 {Γ a b c} (t : term _ c) v1 v2 := t `ₜ⊛ @assign2 Γ a b v1 v2.
Notation "t /[ v1 , v2 ]" := (t_subst2 t v1 v2) (at level 50, left associativity).
(*|
An Evaluator
------------

As motivated earlier, the evaluator will be a defined as a state-machine, the
core definition being a state-transition function. To stick to the intrinsic
style, we wish that this state-machine stops only at *evidently* normal forms,
instead of stoping at states which happen to be in normal form. Perhaps more
simply said, we want to type the transition function as `state Γ → (state
Γ + nf Γ)`, where returning in the right component means stoping and outputing
a normal form.

In order to do this we first need to define normal forms! But instead of
defining an inductive definition of normal forms as is customary, we will take
an other route more tailored to OGS based on ultimate patterns.

Patterns and Observations
^^^^^^^^^^^^^^^^^^^^^^^^^

As discussed in the paper, a central aspect of OGS is to circumvent the
problem of naive trace semantics for higher-order languages by mean of
a notion of "abstract values", or more commonly *ultimate patterns*, which
define the "shareable part" of a value. For clarity reasons, instead of
patterns we here take the dual point of view of "observations", which can be
seen as patterns at the dual type (dual in the sense of swapping the tag). For
our basic λ-calculus, all types are negative -- that is, unsheareble -- hence
the observations are pretty simple:

- Observing a continuation of type `¬ a` means returning a (hidden) value to
  it. In terms of pattern this corresponds to the "fresh variable" pattern
  `Var x`.

- Observing a function of type `a → b` means giving it a hidden value and
  a hidden continuation. In terms of patterns this corresponds to the
  "application" co-pattern `K2 (Var x) (K0 y)`.
|*)
Variant obs : ty -> Type :=
| ORet {a} : obs (¬ a)
| OApp {a b} : obs (a → b)
.
(*|
As observations correspond to a subset of (machine) values where all the
variables are "fresh", these variables have no counter-part in de-bruijn
notation (there is no meaningful notion of freshness). As such we have not
indexed `obs` by any typing context, but to complete the definition we now
need to define a projection into typing contexts denoting the "domain",
"support" or more accurately "set of nameless fresh variables" of an
observation.
|*)
Equations obs_dom {a} : obs a -> t_ctx :=
  obs_dom (@ORet a)   := ∅ ▶ₓ + a ;
  obs_dom (@OApp a b) := ∅ ▶ₓ + a ▶ₓ ¬ b .
(*|
These two definitions together form an operator.
|*)
Definition obs_op : Oper ty t_ctx :=
  {| o_op := obs ; o_dom := @obs_dom |} .
Notation ORet' := (ORet : o_op obs_op _).
Notation OApp' := (OApp : o_op obs_op _).
(*|
Given a value, an observation on its type and a value for each fresh variable
of the observation, we can "refold" everything and form a new state which will
indeed observe this value.
|*)
Equations obs_app {Γ a} (v : val_m Γ a) (p : obs a) (γ : obs_dom p =[val_m]> Γ) : state Γ :=
  obs_app v OApp γ := Val v ⋅ K2 (γ _ (pop top)) (γ _ top) ;
  obs_app π ORet γ := Val (γ _ top) ⋅ (π : ev_ctx _ _) .
(*|
Normal forms
^^^^^^^^^^^^

Normal forms for CBV λ-calculus can be characterized as either a value `v` or
a stuck application in evaluation context `E[x v]` (see "eager-normal forms"
in [L05]_). Now it doesn't take much squinting to see that in our setting,
this corresponds respectively to states of the form `⟨ v | K0 x ⟩` and `⟨ Var
x | K2 v π ⟩`. Squinting a bit more, we can reap the benefits of our unified
treatment of terms and contexts and see that both of these cases work in the
same way: normal states are states given by a variable facing an observation
whose fresh variables have been substituted with values.

Having already defined observation and their set of fresh variables, an
observation stuffed with values in typing context `Γ` can be represented
simply by a formal substitution of an observation `o` and an assigment
`obs_dom o =[val]> Γ`. This "split" definition of normal forms is the one we
will take.
|*)
Definition nf := c_var ∥ₛ (obs_op # val_m).
(*|
The CBV Machine
^^^^^^^^^^^^^^^

Everything is now in place to define our state transition function. The
reduction rules should come to no surprise:

(1) `⟨ t1 t2 | π ⟩ → ⟨ t2 | t1 ⋅1 π ⟩`

(2) `⟨ v | x ⟩` normal

(3) `⟨ v | t ⋅1 π ⟩ →  ⟨ t | v ⋅2 π ⟩`

(4) `⟨ x | v ⋅2 π ⟩` normal

(5) `⟨ λfx.t | v ⋅2 π ⟩ → ⟨ t[f↦λfx.t; x↦v] |  π ⟩`

Rules 1,3,5 step to a new configuration, while cases 2,4 are stuck on normal
forms.
|*)
Equations eval_step {Γ : t_ctx} : state Γ -> sum (state Γ) (nf Γ) :=
  eval_step (Cut (App t1 t2)      (π))      := inl (Cut t2 (K1 t1 π)) ;
  eval_step (Cut (Val v)          (K0 i))   := inr (i ⋅ ORet' ⦇ [ ! ,ₓ v ] ⦈) ;
  eval_step (Cut (Val v)          (K1 t π)) := inl (Cut t (K2 v π)) ;
  eval_step (Cut (Val (Var i))    (K2 v π)) := inr (i ⋅ OApp' ⦇ [ [ ! ,ₓ v ] ,ₓ π ] ⦈) ;
  eval_step (Cut (Val (Lam t)) (K2 v π)) := inl (Cut (t /[ Lam t , v ]) π) .
(*|
Having defined the transition function, we can now iterate it inside the delay
monad. This constructs a possibly non-terminating computation ending with
a normal form.
|*)
Definition stlc_eval {Γ : t_ctx} : state Γ -> delay (nf Γ)
  := iter_delay (ret_delay ∘ eval_step).
(*|
Properties
----------

We have now finished all the computational parts of the instanciation, but all
the proofs are left to be done. Before attacking the OGS-specific hypotheses,
we will need to prove the usual standard lemmata on renaming and substitution.

There will be a stack of lemmata which will all pretty much be simple
inductions on the syntax, so we start by introducing some helpers for this. In
fact it is not completely direct to do since terms and values are mutually
defined: we will need to derive a mutual induction principle.
|*)
Scheme term_mut := Induction for term Sort Prop
   with val_mut := Induction for val Sort Prop .
(*|
Annoyingly, Coq treats this mutual induction principle as two separate
induction principles. They both have the exact same premises but differ in
their conclusion. Thus we define a datatype for these premises, to avoid
duplicating the proofs. Additionally, evaluation contexts are not defined
mutually with terms and values, but it doesn't hurt to prove their properties
simultaneously too, so `syn_ind_args` is in fact closer to the premises of
a three-way mutual induction principle between terms, values and evaluation
contexts.
|*)
Record syn_ind_args (P_t : forall Γ A, term Γ A -> Prop)
                    (P_v : forall Γ A, val Γ A -> Prop)
                    (P_e : forall Γ A, ev_ctx Γ A -> Prop) :=
  {
    ind_val {Γ a} v (_ : P_v Γ a v) : P_t Γ a (Val v) ;
    ind_app {Γ a b} t1 (_ : P_t Γ (a → b) t1) t2 (_ : P_t Γ a t2) : P_t Γ b (App t1 t2) ;
    ind_var {Γ a} i : P_v Γ a (Var i) ;
    ind_tt {Γ} : P_v Γ (ι) (TT) ;
    ind_lamrec {Γ a b} t (_ : P_t _ b t) : P_v Γ (a → b) (Lam t) ;
    ind_kvar {Γ a} i : P_e Γ a (K0 i) ;
    ind_kfun {Γ a b} t (_ : P_t Γ (a → b) t) π (_ : P_e Γ b π) : P_e Γ a (K1 t π) ;
    ind_karg {Γ a b} v (_ : P_v Γ a v) π (_ : P_e Γ b π) : P_e Γ (a → b) (K2 v π)
  } .

Lemma term_ind_mut P_t P_v P_e (H : syn_ind_args P_t P_v P_e) Γ a t : P_t Γ a t .
  destruct H; now apply (term_mut P_t P_v).
Qed.

Lemma val_ind_mut P_t P_v P_e (H : syn_ind_args P_t P_v P_e) Γ a v : P_v Γ a v .
  destruct H; now apply (val_mut P_t P_v).
Qed.

Lemma ctx_ind_mut P_t P_v P_e (H : syn_ind_args P_t P_v P_e) Γ a π : P_e Γ a π .
  induction π.
  - apply (ind_kvar _ _ _ H).
  - apply (ind_kfun _ _ _ H); auto; apply (term_ind_mut _ _ _ H).
  - apply (ind_karg _ _ _ H); auto; apply (val_ind_mut _ _ _ H).
Qed.
(*|
Now equipped we can start with the first lemma: renaming respects pointwise
equality of assignments. As discussed, we will prove this by mutual induction
on our three "base" syntactic categories of terms, values and evaluation
contexts, and then we will also deduce it for the three "derived" notions of
machine values, states and assigments. Sometimes some of the derived notions
will be omitted if it is not needed later on.

This proof, like all the following ones will follow a simple pattern:
a simplification; an application of congruence; a fixup for the two-time
shifted assigment in the case of λ; finally a call to the induction
hypothesis.

.. note:: Here is definitely where the generic syntax traversal kit of
   Guillaume Allais et al would shine. Indeed the proof pattern i outlined can
   really be formalized into a generic proof.

..
|*)
Definition t_ren_proper_P Γ a (t : term Γ a) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> t ₜ⊛ᵣ f1 = t ₜ⊛ᵣ f2 .
Definition v_ren_proper_P Γ a (v : val Γ a) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> v ᵥ⊛ᵣ f1 = v ᵥ⊛ᵣ f2 .
Definition e_ren_proper_P Γ a (π : ev_ctx Γ a) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> π ₑ⊛ᵣ f1 = π ₑ⊛ᵣ f2 .
Lemma ren_proper_prf : syn_ind_args t_ren_proper_P v_ren_proper_P e_ren_proper_P.
  econstructor.
  all: unfold t_ren_proper_P, v_ren_proper_P, e_ren_proper_P.
  all: intros; cbn; f_equal; eauto.
  all: eapply H; now apply r_shift2_eq.
Qed.

#[global] Instance t_ren_eq {Γ Δ}
  : Proper (asgn_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@t_rename Γ Δ).
  intros f1 f2 H1 a x y ->; now apply (term_ind_mut _ _ _ ren_proper_prf).
Qed.
#[global] Instance v_ren_eq {Γ Δ}
  : Proper (asgn_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@v_rename Γ Δ).
  intros f1 f2 H1 a x y ->; now apply (val_ind_mut _ _ _ ren_proper_prf).
Qed.
#[global] Instance e_ren_eq {Γ Δ}
  : Proper (asgn_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@e_rename Γ Δ).
  intros f1 f2 H1 a x y ->; now apply (ctx_ind_mut _ _ _ ren_proper_prf).
Qed.
#[global] Instance m_ren_eq {Γ Δ}
  : Proper (asgn_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@m_rename Γ Δ).
  intros ? ? H1 [] _ ? ->; cbn in *; now rewrite H1.
Qed.
#[global] Instance s_ren_eq {Γ Δ}
  : Proper (asgn_eq _ _ ==> eq ==> eq) (@s_rename Γ Δ).
  intros ? ? H1 _ x ->; destruct x; unfold s_rename; cbn; now rewrite H1.
Qed.
#[global] Instance a_ren_eq {Γ1 Γ2 Γ3}
  : Proper (asgn_eq _ _ ==> asgn_eq _ _ ==> asgn_eq _ _) (@a_ren Γ1 Γ2 Γ3).
  intros ? ? H1 ? ? H2 ? ?; apply (m_ren_eq _ _ H1), H2.
Qed.
#[global] Instance a_shift2_eq {Γ Δ x y} : Proper (asgn_eq _ _ ==> asgn_eq _ _) (@a_shift2 Γ Δ x y).
  intros ? ? H ? v.
  do 2 (dependent elimination v; cbn; auto).
  now rewrite H.
Qed.
(*|
Lemma 2: renaming-renaming assocativity. I say "associativity" because it
definitely looks like associativity if we disregard the subscripts. More
precisely it could be described as the composition law a right action.
|*)
Definition t_ren_ren_P Γ1 a (t : term Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 ⊆ Γ3),
    (t ₜ⊛ᵣ f1) ₜ⊛ᵣ f2 = t ₜ⊛ᵣ (f1 ᵣ⊛ f2).
Definition v_ren_ren_P Γ1 a (v : val Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 ⊆ Γ3),
    (v ᵥ⊛ᵣ f1) ᵥ⊛ᵣ f2 = v ᵥ⊛ᵣ (f1 ᵣ⊛ f2).
Definition e_ren_ren_P Γ1 a (π : ev_ctx Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 ⊆ Γ3),
    (π ₑ⊛ᵣ f1) ₑ⊛ᵣ f2 = π ₑ⊛ᵣ (f1 ᵣ⊛ f2).

Lemma ren_ren_prf : syn_ind_args t_ren_ren_P v_ren_ren_P e_ren_ren_P .
  econstructor.
  all: unfold t_ren_ren_P, v_ren_ren_P, e_ren_ren_P.
  all: intros; cbn; f_equal; auto.
  rewrite H; apply t_ren_eq; auto.
  intros ? v; now do 2 (dependent elimination v; eauto).
Qed.

Lemma t_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 ⊆ Γ3) a (t : term Γ1 a) 
    : (t ₜ⊛ᵣ f1) ₜ⊛ᵣ f2 = t ₜ⊛ᵣ (f1 ᵣ⊛ f2).
  now apply (term_ind_mut _ _ _ ren_ren_prf).
Qed.
Lemma v_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 ⊆ Γ3) a (v : val Γ1 a) 
    : (v ᵥ⊛ᵣ f1) ᵥ⊛ᵣ f2 = v ᵥ⊛ᵣ (f1 ᵣ⊛ f2).
  now apply (val_ind_mut _ _ _ ren_ren_prf).
Qed.
Lemma e_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 ⊆ Γ3) a (π : ev_ctx Γ1 a) 
    : (π ₑ⊛ᵣ f1) ₑ⊛ᵣ f2 = π ₑ⊛ᵣ (f1 ᵣ⊛ f2).
  now apply (ctx_ind_mut _ _ _ ren_ren_prf).
Qed.
Lemma m_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 ⊆ Γ3) a (v : val_m Γ1 a) 
    : (v ₘ⊛ᵣ f1) ₘ⊛ᵣ f2 = v ₘ⊛ᵣ (f1 ᵣ⊛ f2).
  destruct a; [ now apply v_ren_ren | now apply e_ren_ren ].
Qed.
Lemma s_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 ⊆ Γ3) (s : state Γ1) 
    : (s ₛ⊛ᵣ f1) ₛ⊛ᵣ f2 = s ₛ⊛ᵣ (f1 ᵣ⊛ f2).
  destruct s; apply (f_equal2 Cut); [ now apply t_ren_ren | now apply e_ren_ren ].
Qed.
(*|
Lemma 3: left identity law of renaming.
|*)
Definition t_ren_id_l_P Γ a (t : term Γ a) : Prop := t ₜ⊛ᵣ r_id = t .
Definition v_ren_id_l_P Γ a (v : val Γ a) : Prop := v ᵥ⊛ᵣ r_id = v .
Definition e_ren_id_l_P Γ a (π : ev_ctx Γ a) : Prop := π ₑ⊛ᵣ r_id = π.
Lemma ren_id_l_prf : syn_ind_args t_ren_id_l_P v_ren_id_l_P e_ren_id_l_P .
  econstructor.
  all: unfold t_ren_id_l_P, v_ren_id_l_P, e_ren_id_l_P.
  all: intros; cbn; f_equal; auto.
  rewrite <- H at 2; apply t_ren_eq; auto.
  intros ? v; now do 2 (dependent elimination v; eauto).
Qed.

Lemma t_ren_id_l {Γ} a (t : term Γ a) : t ₜ⊛ᵣ r_id = t .
  now apply (term_ind_mut _ _ _ ren_id_l_prf).
Qed.
Lemma v_ren_id_l {Γ} a (v : val Γ a) : v ᵥ⊛ᵣ r_id = v.
  now apply (val_ind_mut _ _ _ ren_id_l_prf).
Qed.
Lemma e_ren_id_l {Γ} a (π : ev_ctx Γ a) : π ₑ⊛ᵣ r_id = π .
  now apply (ctx_ind_mut _ _ _ ren_id_l_prf).
Qed.
Lemma m_ren_id_l {Γ} a (v : val_m Γ a) : v ₘ⊛ᵣ r_id = v .
  destruct a; [ now apply v_ren_id_l | now apply e_ren_id_l ].
Qed.
Lemma s_ren_id_l {Γ} (s : state Γ) : s ₛ⊛ᵣ r_id = s.
  destruct s; apply (f_equal2 Cut); [ now apply t_ren_id_l | now apply e_ren_id_l ].
Qed.
(*|
Lemma 4: right identity law of renaming. This one basically holds
definitionally, it only needs a case split for some of the derived notions. We
will also prove a consequence on weakenings: identity law.
|*)
Lemma m_ren_id_r {Γ Δ} (f : Γ ⊆ Δ) {a} (i : Γ ∋ a) : a_id _ i ₘ⊛ᵣ f = a_id _ (f _ i) .
  now destruct a.
Qed.
Lemma a_ren_id_r {Γ Δ} (f : Γ ⊆ Δ) : a_id ⊛ᵣ f ≡ₐ f ᵣ⊛ a_id .
  intros ??; now apply m_ren_id_r.
Qed.
Lemma a_shift2_id {Γ x y} : @a_shift2 Γ Γ x y a_id ≡ₐ a_id.
  intros ? v; do 2 (dependent elimination v; auto).
  exact (m_ren_id_r _ _).
Qed.
(*|
Lemma 5: shifting assigments commutes with left and right renaming.
|*)
Lemma a_shift2_s_ren {Γ1 Γ2 Γ3 a b} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val_m]> Γ3)
  : @a_shift2 _ _ a b (f1 ᵣ⊛ f2) ≡ₐ r_shift2 f1 ᵣ⊛ a_shift2 f2 .
  intros ? v; do 2 (dependent elimination v; auto).
Qed.
Lemma a_shift2_a_ren {Γ1 Γ2 Γ3 a b} (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 ⊆ Γ3)
      : @a_shift2 _ _ a b (f1 ⊛ᵣ f2) ≡ₐ a_shift2 f1 ⊛ᵣ r_shift2 f2 .
  intros ? v.
  do 2 (dependent elimination v; cbn; [ symmetry; exact (a_ren_id_r _ _ _) | ]).
  unfold a_ren; cbn - [ m_rename ]; unfold m_shift2; now rewrite 2 m_ren_ren.
Qed.
(*|
Lemma 6: substitution respects pointwise equality of assigments.
|*)
Definition t_sub_proper_P Γ a (t : term Γ a) : Prop :=
  forall Δ (f1 f2 : Γ =[val_m]> Δ), f1 ≡ₐ f2 -> t `ₜ⊛ f1 = t `ₜ⊛ f2 .
Definition v_sub_proper_P Γ a (v : val Γ a) : Prop :=
  forall Δ (f1 f2 : Γ =[val_m]> Δ), f1 ≡ₐ f2 -> v `ᵥ⊛ f1 = v `ᵥ⊛ f2 .
Definition e_sub_proper_P Γ a (π : ev_ctx Γ a) : Prop :=
  forall Δ (f1 f2 : Γ =[val_m]> Δ), f1 ≡ₐ f2 -> π `ₑ⊛ f1 = π `ₑ⊛ f2.
Lemma sub_proper_prf : syn_ind_args t_sub_proper_P v_sub_proper_P e_sub_proper_P.
  econstructor.
  all: unfold t_sub_proper_P, v_sub_proper_P, e_sub_proper_P.
  all: intros; cbn; f_equal; auto.
  now apply H, a_shift2_eq.
Qed.

#[global] Instance t_sub_eq {Γ Δ}
  : Proper (asgn_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@t_subst Γ Δ).
  intros ? ? H1 a _ ? ->; now apply (term_ind_mut _ _ _ sub_proper_prf).
Qed.
#[global] Instance v_sub_eq {Γ Δ}
  : Proper (asgn_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@v_subst Γ Δ).
  intros ? ? H1 a _ ? ->; now apply (val_ind_mut _ _ _ sub_proper_prf).
Qed.
#[global] Instance e_sub_eq {Γ Δ}
  : Proper (asgn_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@e_subst Γ Δ).
  intros ? ? H1 a _ ? ->; now apply (ctx_ind_mut _ _ _ sub_proper_prf).
Qed.
#[global] Instance m_sub_eq
  : Proper (∀ₕ Γ, ∀ₕ _, eq ==> ∀ₕ Δ, asgn_eq Γ Δ ==> eq) m_subst.
  intros ? [] ?? -> ??? H1; cbn in *; now rewrite H1.
Qed.
#[global] Instance s_sub_eq
  : Proper (∀ₕ Γ, eq ==> ∀ₕ Δ, asgn_eq Γ Δ ==> eq) s_subst.
  intros ??[] -> ??? H1; cbn; now rewrite H1.
Qed.
(*
#[global] Instance a_comp_eq {Γ1 Γ2 Γ3} : Proper (ass_eq _ _ ==> ass_eq _ _ ==> ass_eq _ _) (@a_comp Γ1 Γ2 Γ3).
  intros ? ? H1 ? ? H2 ? ?; unfold a_comp, s_map; now rewrite H1, H2.
Qed.
*)
(*|
Lemma 7: renaming-substitution "associativity".
|*)
Definition t_ren_sub_P Γ1 a (t : term Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 ⊆ Γ3) ,
    (t `ₜ⊛ f1) ₜ⊛ᵣ f2 = t `ₜ⊛ (f1 ⊛ᵣ f2) .
Definition v_ren_sub_P Γ1 a (v : val Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 ⊆ Γ3) ,
    (v `ᵥ⊛ f1) ᵥ⊛ᵣ f2 = v `ᵥ⊛ (f1 ⊛ᵣ f2) .
Definition e_ren_sub_P Γ1 a (π : ev_ctx Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 ⊆ Γ3) ,
    (π `ₑ⊛ f1) ₑ⊛ᵣ f2 = π `ₑ⊛ (f1 ⊛ᵣ f2) .
Lemma ren_sub_prf : syn_ind_args t_ren_sub_P v_ren_sub_P e_ren_sub_P.
  econstructor.
  all: unfold t_ren_sub_P, v_ren_sub_P, e_ren_sub_P.
  all: intros; cbn; f_equal.
  all: try rewrite a_shift2_a_ren; auto.
Qed.

Lemma t_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 ⊆ Γ3) a (t : term Γ1 a)
  : (t `ₜ⊛ f1) ₜ⊛ᵣ f2 = t `ₜ⊛ (f1 ⊛ᵣ f2) .
  now apply (term_ind_mut _ _ _ ren_sub_prf).
Qed.
Lemma v_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 ⊆ Γ3) a (v : val Γ1 a)
  : (v `ᵥ⊛ f1) ᵥ⊛ᵣ f2 = v `ᵥ⊛ (f1 ⊛ᵣ f2) .
  now apply (val_ind_mut _ _ _ ren_sub_prf).
Qed.
Lemma e_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 ⊆ Γ3) a (π : ev_ctx Γ1 a)
  : (π `ₑ⊛ f1) ₑ⊛ᵣ f2 = π `ₑ⊛ (f1 ⊛ᵣ f2) .
  now apply (ctx_ind_mut _ _ _ ren_sub_prf).
Qed.
Lemma m_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 ⊆ Γ3) a (v : val_m Γ1 a)
  : (v ᵥ⊛ f1) ₘ⊛ᵣ f2 = v ᵥ⊛ (f1 ⊛ᵣ f2) .
  destruct a; [ now apply v_ren_sub | now apply e_ren_sub ].
Qed.
Lemma s_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 ⊆ Γ3) (s : state Γ1)
  : (s ₜ⊛ f1) ₛ⊛ᵣ f2 = s ₜ⊛ (f1 ⊛ᵣ f2) .
  destruct s; cbn; now rewrite t_ren_sub, e_ren_sub.
Qed.
(*|
Lemma 8: substitution-renaming "associativity".
|*)
Definition t_sub_ren_P Γ1 a (t : term Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val_m]> Γ3) ,
  (t ₜ⊛ᵣ f1) `ₜ⊛ f2 = t `ₜ⊛ (f1 ᵣ⊛ f2) .
Definition v_sub_ren_P Γ1 a (v : val Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val_m]> Γ3) ,
  (v ᵥ⊛ᵣ f1) `ᵥ⊛ f2 = v `ᵥ⊛ (f1 ᵣ⊛ f2) .
Definition e_sub_ren_P Γ1 a (π : ev_ctx Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val_m]> Γ3) ,
  (π ₑ⊛ᵣ f1) `ₑ⊛ f2 = π `ₑ⊛ (f1 ᵣ⊛ f2) .
Lemma sub_ren_prf : syn_ind_args t_sub_ren_P v_sub_ren_P e_sub_ren_P.
  econstructor.
  all: unfold t_sub_ren_P, v_sub_ren_P, e_sub_ren_P.
  all: intros; cbn; f_equal; auto.
  now rewrite a_shift2_s_ren.
Qed.

Lemma t_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val_m]> Γ3) a (t : term Γ1 a)
  : (t ₜ⊛ᵣ f1) `ₜ⊛ f2 = t `ₜ⊛ (f1 ᵣ⊛ f2) .
  now apply (term_ind_mut _ _ _ sub_ren_prf).
Qed.
Lemma v_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val_m]> Γ3) a (v : val Γ1 a)
  : (v ᵥ⊛ᵣ f1) `ᵥ⊛ f2 = v `ᵥ⊛ (f1 ᵣ⊛ f2) .
  now apply (val_ind_mut _ _ _ sub_ren_prf).
Qed.
Lemma e_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val_m]> Γ3) a (π : ev_ctx Γ1 a)
  : (π ₑ⊛ᵣ f1) `ₑ⊛ f2 = π `ₑ⊛ (f1 ᵣ⊛ f2) .
  now apply (ctx_ind_mut _ _ _ sub_ren_prf).
Qed.
Lemma m_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val_m]> Γ3) a (v : val_m Γ1 a)
  : (v ₘ⊛ᵣ f1) ᵥ⊛ f2 = v ᵥ⊛ (f1 ᵣ⊛ f2) .
  destruct a; [ now apply v_sub_ren | now apply e_sub_ren ].
Qed.
Lemma s_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val_m]> Γ3) (s : state Γ1)
  : (s ₛ⊛ᵣ f1) ₜ⊛ f2 = s ₜ⊛ (f1 ᵣ⊛ f2) .
  destruct s; cbn; now rewrite t_sub_ren, e_sub_ren.
Qed.
(*|
Lemma 9: left identity law of substitution.
|*)
Definition t_sub_id_l_P Γ a (t : term Γ a) : Prop := t `ₜ⊛ a_id = t .
Definition v_sub_id_l_P Γ a (v : val Γ a) : Prop := v `ᵥ⊛ a_id = v .
Definition e_sub_id_l_P Γ a (π : ev_ctx Γ a) : Prop := π `ₑ⊛ a_id = π .
Lemma sub_id_l_prf : syn_ind_args t_sub_id_l_P v_sub_id_l_P e_sub_id_l_P.
  econstructor.
  all: unfold t_sub_id_l_P, v_sub_id_l_P, e_sub_id_l_P.
  all: intros; cbn; f_equal; auto.
  now rewrite a_shift2_id.
Qed.

Lemma t_sub_id_l {Γ} a (t : term Γ a) : t `ₜ⊛ a_id = t .
  now apply (term_ind_mut _ _ _ sub_id_l_prf).
Qed.
Lemma v_sub_id_l {Γ} a (v : val Γ a) : v `ᵥ⊛ a_id = v .
  now apply (val_ind_mut _ _ _ sub_id_l_prf).
Qed.
Lemma e_sub_id_l {Γ} a (π : ev_ctx Γ a) : π `ₑ⊛ a_id = π .
  now apply (ctx_ind_mut _ _ _ sub_id_l_prf).
Qed.
Lemma m_sub_id_l {Γ} a (v : val_m Γ a) : v ᵥ⊛ a_id = v .
  destruct a; [ now apply v_sub_id_l | now apply e_sub_id_l ].
Qed.
Lemma s_sub_id_l {Γ} (s : state Γ) : s ₜ⊛ a_id = s .
  destruct s; cbn; now rewrite t_sub_id_l, e_sub_id_l.
Qed.
(*|
Lemma 9: right identity law of substitution. As for renaming, this one is
mostly by definition.
|*)
Lemma m_sub_id_r {Γ1 Γ2} {a} (i : Γ1 ∋ a) (f : Γ1 =[val_m]> Γ2) : a_id a i ᵥ⊛ f = f a i.
  now destruct a.
Qed.
(*|
Lemma 10: shifting assigments respects composition.
|*)
Lemma a_shift2_comp {Γ1 Γ2 Γ3 a b} (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 =[val_m]> Γ3) 
  : @a_shift2 _ _ a b (f1 ⊛ f2) ≡ₐ a_shift2 f1 ⊛ a_shift2 f2 .
  intros ? v. 
  do 2 (dependent elimination v; [ symmetry; exact (m_sub_id_r _ _) | ]).
  cbn; unfold m_shift2; now rewrite m_ren_sub, m_sub_ren.
Qed.
(*|
Lemma 11: substitution-substitution associativity, ie composition law.
|*)
Definition t_sub_sub_P Γ1 a (t : term Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 =[val_m]> Γ3) ,
  t `ₜ⊛ (f1 ⊛ f2) = (t `ₜ⊛ f1) `ₜ⊛ f2 .
Definition v_sub_sub_P Γ1 a (v : val Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 =[val_m]> Γ3) ,
  v `ᵥ⊛ (f1 ⊛ f2) = (v `ᵥ⊛ f1) `ᵥ⊛ f2 .
Definition e_sub_sub_P Γ1 a (π : ev_ctx Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 =[val_m]> Γ3) ,
  π `ₑ⊛ (f1 ⊛ f2) = (π `ₑ⊛ f1) `ₑ⊛ f2 .
Lemma sub_sub_prf : syn_ind_args t_sub_sub_P v_sub_sub_P e_sub_sub_P.
  econstructor.
  all: unfold t_sub_sub_P, v_sub_sub_P, e_sub_sub_P.
  all: intros; cbn; f_equal; auto.
  now rewrite a_shift2_comp.
Qed.

Lemma t_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 =[val_m]> Γ3) a (t : term Γ1 a)
  : t `ₜ⊛ (f1 ⊛ f2) = (t `ₜ⊛ f1) `ₜ⊛ f2 .
  now apply (term_ind_mut _ _ _ sub_sub_prf).
Qed.
Lemma v_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 =[val_m]> Γ3) a (v : val Γ1 a)
  : v `ᵥ⊛ (f1 ⊛ f2) = (v `ᵥ⊛ f1) `ᵥ⊛ f2 .
  now apply (val_ind_mut _ _ _ sub_sub_prf).
Qed.
Lemma e_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 =[val_m]> Γ3) a (π : ev_ctx Γ1 a)
  : π `ₑ⊛ (f1 ⊛ f2) = (π `ₑ⊛ f1) `ₑ⊛ f2 .
  now apply (ctx_ind_mut _ _ _ sub_sub_prf).
Qed.
Lemma m_sub_sub {Γ1 Γ2 Γ3} a (v : val_m Γ1 a) (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 =[val_m]> Γ3)
  : v ᵥ⊛ (f1 ⊛ f2) = (v ᵥ⊛ f1) ᵥ⊛ f2 .
  destruct a; [ now apply v_sub_sub | now apply e_sub_sub ].
Qed.
Lemma s_sub_sub {Γ1 Γ2 Γ3} (s : state Γ1) (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 =[val_m]> Γ3) 
  : s ₜ⊛ (f1 ⊛ f2) = (s ₜ⊛ f1) ₜ⊛ f2 .
  destruct s; cbn; now rewrite t_sub_sub, e_sub_sub.
Qed.
Lemma a_sub2_sub {Γ Δ a b} (f : Γ =[val_m]> Δ) (v1 : val_m Γ a) (v2 : val_m Γ b)
  : a_shift2 f ⊛ assign2 (v1 ᵥ⊛ f) (v2 ᵥ⊛ f) ≡ₐ (assign2 v1 v2) ⊛ f .
  intros ? v.
  do 2 (dependent elimination v; [ cbn; now rewrite m_sub_id_r | ]).
  cbn; unfold m_shift2; rewrite m_sub_ren, m_sub_id_r.
  now apply m_sub_id_l.
Qed.
Lemma t_sub2_sub {Γ Δ x y z} (f : Γ =[val_m]> Δ) (t : term (Γ ▶ₓ x ▶ₓ y) z) v1 v2
  : (t `ₜ⊛ a_shift2 f) /[ v1 ᵥ⊛ f , v2 ᵥ⊛ f ] = (t /[ v1 , v2 ]) `ₜ⊛ f.
  unfold t_subst2; now rewrite <- 2 t_sub_sub, a_sub2_sub.
Qed.
(*|
The Actual Instance
-------------------

Having proved all the basic syntactic properties of STLC, we are now ready to
instanciate our framework!

As we only have negative types, we instanciate the interaction specification
with types and observations. Beware that in more involved cases, the notion of
"types" we give to the OGS construction does not coincide with the
"language types": you should only give the negative types, or more intuitively,
"non-shareable" types.

As hinted at the beginning, we instanciate the abstract value notion with our
"machine values". They form a suitable monoid, which means we get a category
of assigments, for which we now provide the proof of the laws.
|*)
#[global] Instance stlc_val_laws : subst_monoid_laws val_m :=
  {| v_sub_proper := @m_sub_eq ;
     v_sub_var := @m_sub_id_r ;
     v_var_sub := @m_sub_id_l ;
     Subst.v_sub_sub := @m_sub_sub |} .
(*|
Configurations are instanciated with our states, and what we have proved
earlier amounts to showing they are a right-module on values.
|*)
# [global] Instance stlc_conf_laws : subst_module_laws val_m state :=
  {| c_sub_proper := @s_sub_eq ;
     c_var_sub := @s_sub_id_l ;
     c_sub_sub := @s_sub_sub |} .
(*|
In our generic theorem, there is a finicky lemma that is the counter-part to
the exclusion of any "infinite chit-chat" that one finds in other accounts of
OGS and other game semantics. The way we have proved it requires a little bit
more structure on values. Specifically, we need to show that `a_id` is
injective and that its fibers are decidable and invert renamings. These
technicalities are easily shown by induction on values but help us to
distinguish conveniently between values which are variables and others.
|*)
#[global] Instance stlc_var_laws : var_assumptions val_m.
  econstructor.
  - intros ? [] ?? H; now dependent destruction H.
  - intros ? [] []; try now apply Yes; exact (Vvar _).
    all: apply No; intro H; dependent destruction H.
  - intros ?? [] v r H; induction v; dependent destruction H; exact (Vvar _).
Qed.
(*|
We now instanciate the machine with `stlc_eval` as the active step ("compute
the next observable action") and `obs_app` as the passive step ("resume from
a stuck state").
|*)
#[global] Instance stlc_machine : machine val_m state obs_op :=
  {| eval := @stlc_eval ;
     oapp := @obs_app |} .
(*|
All that is left is to prove our theorem-specific hypotheses. All but another
technical lemma for the chit-chat problem are again coherence conditions
between `eval` and `app` and the monoidal structure of values and
configurations.

.. coq:: none
|*)
From Coinduction Require Import coinduction lattice rel tactics.
From OGS.ITree Require Import Eq.

Ltac refold_eval :=
  change (Structure.iter _ _ ?a) with (stlc_eval a);
  change (Structure.subst (fun pat : T1 => let 'T1_0 := pat in ?f) T1_0 ?u)
    with (bind_delay' u f).
(*||*)
#[global] Instance stlc_machine_law : machine_laws val_m state obs_op.
  econstructor; cbn; intros.
(*|
The first one proves that `obs_app` respects pointwise equality of assigments.
|*)
  - intros ?? H1; dependent elimination o; cbn; repeat (f_equal; auto).
(*|
The second one proves a commutation law of `obs_app` with renamings.
|*)
  - destruct x; dependent elimination o; cbn; f_equal.
(*|
The meat of our abstract proof is this next one. We need to prove that our
evaluator respects substitution in a suitable sense: evaluating a substituted
configuration must be the same thing as evaluating the configuration, then
"substituting" the normal form and continuing the evaluation.

While potentially scary, the proof is direct and this actually amount to
checking that indeed, when unrolling our evaluator, this is what happens.
|*)
  - revert c a; unfold comp_eq, it_eq; coinduction R CIH; intros c e.
    cbn; funelim (eval_step c); cbn.
    + destruct (e ¬ a0 i); auto.
      remember (v `ᵥ⊛ e) as v'; clear H v Heqv'.
      dependent elimination v'; cbn; auto.
    + econstructor; refold_eval; apply CIH.
    + remember (e + (a2 → b0) i) as vv; clear H i Heqvv.
      dependent elimination vv; cbn; auto.
    + econstructor;
       refold_eval;
       change (Lam (t `ₜ⊛ _)) with (Lam t `ᵥ⊛ e);
       change (?v `ᵥ⊛ ?a) with ((v : val_m _ (+ _)) ᵥ⊛ a).
      rewrite t_sub2_sub.
      apply CIH.
    + econstructor; refold_eval; apply CIH.
(*|
Just like the above proof had the flavor of a composition law of module, this
one has the flavor of an identity law. It states that evaluating a normal form
is the identity computation.
|*)
  - destruct u as [ a i [ p γ ] ]; cbn.
    dependent elimination p; cbn.
    all: unfold comp_eq; apply it_eq_unstep; cbn; econstructor.
    all: econstructor; intros ? v; do 3 (dependent elimination v; auto).
(*|
This last proof is the technical condition we hinted at. It is a proof of
well-foundedness of some relation, and what it amounts to is that if we
repeatedly instantiate the head variable of a normal form by a value which is
not a variable, after a finite number of times doing so we will eventually
reach something that is not a normal form.

For our calculus this number is at most 2, the pathological state being
`⟨ x | y ⟩`, which starts by being stuck on `y`, but when instanciating by
some non-variable `π`, `⟨ x | π ⟩` is still stuck, this time on `x`. After
another step it will definitely be unstuck and evaluation will be able to do
a reduction step.

It is slightly tedious to prove but amount again to a "proof by case
splitting".
|*)
  - intros [ x p ].
    destruct x; dependent elimination p; econstructor.
    * intros [ z p ] H.
      dependent elimination p; dependent elimination H.
      all: dependent elimination v; try now destruct (t0 (Vvar _)).
      all: apply it_eq_step in i0; now inversion i0.
    * intros [ z p ] H.
      dependent elimination p; dependent elimination H; cbn in *.
      dependent elimination v; try now destruct (t0 (Vvar _)).
      + apply it_eq_step in i0; now inversion i0.
      + remember (a1 _ Ctx.top) as vv; clear a1 Heqvv.
        dependent elimination vv;
          apply it_eq_step in i0; cbn in i0; dependent elimination i0.
        inversion r_rel.
      + econstructor; intros [ z p ] H.
        dependent elimination p; dependent elimination H.
        all: dependent elimination v0; try now destruct (t1 (Vvar _)).
        all: apply it_eq_step in i2; now inversion i2.
Qed.
(*|
At this point we have finished all the hard work! We already enjoy the generic
correctness theorem but don't know it yet! Lets define some shorthands for
some generic notions applied to our case, to make it a welcoming nest.

The whole semantic is parametrized by typing scope `Δ` of "final channels".
Typically this can be instanciated with the singleton `[ ¬ ans ]` for some
chosen type `ans`, which will correspond with the outside type of the
testing-contexts from CIU-equivalence. Usually this answer type is taken among
the positive (or shareable) types of our language, but in fact using our
observation machinery we can project the value of any type onto its "shareable
part". This is why our generic proof abstracts over this answer type and even
allows several of them at the same time (that is, `Δ`). In our case, as all
types in our language are unshareable, the positive part of any value is
pretty useless: it is always a singleton. Yet our notion of testing still
distinguishes terminating from non-terminating programs.

As discussed in the paper, the "native output" of the generic theorem is
correctness with respect to an equivalence we call "substitution equivalence".
We will recover a more standard CIU later on.
|*)
Definition subst_eq Δ {Γ} : relation (state Γ) :=
  fun u v => forall σ : Γ =[val_m]> Δ, evalₒ (u ₜ⊛ σ) ≈ evalₒ (v ₜ⊛ σ) .
Notation "x ≈S[ Δ ]≈ y" := (subst_eq Δ x y) (at level 10).
(*|
Our semantic objects live in what is defined in the generic construction as
`ogs_act`, that is active strategies for the OGS game. They come with their
own notion of equivalence, weak bisimilarity and we get to interpret states
into semantic objects.
|*)
Definition sem_act Δ Γ := ogs_act (obs := obs_op) Δ (∅ ▶ₓ Γ) .

Definition ogs_weq_act Δ {Γ} : relation (sem_act Δ Γ) := fun u v => u ≈ v .
Notation "u ≈[ Δ ]≈ v" := (ogs_weq_act Δ u v) (at level 40).

Definition interp_act_s Δ {Γ} (c : state Γ) : sem_act Δ Γ :=
  m_strat (∅ ▶ₓ Γ) (inj_init_act Δ c) .
Notation "OGS⟦ t ⟧" := (interp_act_s _ t) .
(*|
We can now obtain our instance of the correctness result!
|*)
Theorem stlc_subst_correct Δ {Γ} (x y : state Γ)
  : OGS⟦x⟧ ≈[Δ]≈ OGS⟦y⟧ -> x ≈S[Δ]≈ y .
  exact (ogs_correction Δ x y).
Qed.
(*|
Recovering CIU-equivalence
^^^^^^^^^^^^^^^^^^^^^^^^^^

CIU-equivalence more usually defined as a relation on terms (and not some
states), and involves an evaluation context. In our formalism it amounts to
the following definition.
|*)
Definition ciu_eq Δ {Γ a} : relation (term Γ a) :=
  fun u v => forall (σ : Γ =[val_m]> Δ) (π : ev_ctx Δ a),
      evalₒ ((u `ₜ⊛ σ) ⋅ π) ≈ evalₒ ((v `ₜ⊛ σ) ⋅ π) .
Notation "x ≈C[ Δ ]≈ y" := (ciu_eq Δ x y) (at level 10).
(*|
Now from a term we can always construct a state by naming it, that is, placing
the term opposite of a fresh context variable.
|*)
Definition c_init {Γ a} (t : term Γ a) : state (Γ ▶ₓ ¬ a)
  := t_shift _ t ⋅ K0 Ctx.top .
Notation "T⟦ t ⟧" := (OGS⟦ c_init t ⟧) .
(*|
Similarly, from an evaluation context and a substitution, we can form an
extended substitution. Without surprise these two constructions simplify well
in terms of substitution.
|*)
Definition a_of_sk {Γ Δ a} (σ : Γ =[val_m]> Δ) (π : ev_ctx Δ a)
  : (Γ ▶ₓ ¬ a) =[val_m]> Δ := σ ▶ₐ (π : val_m _ (¬ _)) .

Lemma sub_init {Γ Δ a} (t : term Γ a) (σ : Γ =[val_m]> Δ) (π : ev_ctx Δ a)
  : (t `ₜ⊛ σ) ⋅ π = c_init t ₜ⊛ a_of_sk σ π  .
  cbn; unfold t_shift; now rewrite t_sub_ren.
Qed.
(*|
We can now obtain a correctness theorem with respect to standard
CIU-equivalence by embedding terms into states. Proving that CIU-equivalence
entails our substitution equivalence is left to the reader!
|*)
Theorem stlc_ciu_correct Δ {Γ a} (x y : term Γ a)
  : T⟦ x ⟧ ≈[Δ]≈ T⟦ y ⟧ -> x ≈C[Δ]≈ y .
  intros H σ k; rewrite 2 sub_init.
  now apply stlc_subst_correct.
Qed.
(*|
.. [AACMM21] Guillaume Allais et al, "A type- and scope-safe universe of
   syntaxes with binding: their semantics and proofs", 2021.
.. [FS22] Marcelo Fiore & Dmitrij Szamozvancev, "Formal Metatheory of
   Second-Order Abstract Syntax", 2022.
.. [L05] Soren Lassen, "Eager Normal Form Bisimulation", 2005.
|*)
