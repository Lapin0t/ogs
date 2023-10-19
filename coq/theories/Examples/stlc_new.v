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
From OGS Require Import Prelude .
From OGS.Utils Require Import Psh Rel Ctx .
From OGS.ITree Require Import ITree Delay .
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
Inductive ty0 : Type :=
| ι : ty0
| Arr : ty0 -> ty0 -> ty0
.
(*|
.. coq:: none
|*)
Derive NoConfusion for ty0 .
Declare Scope ty_scope .
Delimit Scope ty_scope with ty .
Bind Scope ty_scope with ty0 .
(*|
.. coq::
|*)
Notation "A → B" := (Arr A B) (at level 40) : ty_scope .
(*|
We then define "tagged types", where `t+ a` will be the type of terms of type
`a`, and `t- a` the type of evaluation contexts of hole `a`.
|*)
Variant ty : Type :=
| VTy : ty0 -> ty
| KTy : ty0 -> ty
.
Notation "+ t" := (VTy t) (at level 20) : ty_scope .
Notation "¬ t" := (KTy t) (at level 20) : ty_scope .
(*|
.. coq:: none
|*)
Derive NoConfusion for ty .
Bind Scope ty_scope with ty .
Open Scope ty_scope .
Coercion VTy : ty0 >-> ty .
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
Definition t_ctx : Type := Ctx.ctx ty .
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
| LamRec {a b} : term (Γ ▶ (a → b) ▶ a) b -> val Γ (a → b)
.
(*|
.. coq:: none
|*)
Arguments Val {Γ a} v .
Arguments App {Γ a b} t1 t2 .
Arguments Var {Γ a} i .
Arguments LamRec {Γ a b} t .
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
Variant state (Γ : t_ctx) : Type :=
| Cut {a} : term Γ a -> ev_ctx Γ a -> state Γ
.
(*|
.. coq:: none
|*)
Arguments Cut {Γ a} t π.
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
  v_rename f _ (LamRec t) := LamRec (t_rename (r_shift2 f) _ t) .

Equations e_rename {Γ Δ} : Γ ⊆ Δ -> ev_ctx Γ ⇒ᵢ ev_ctx Δ :=
  e_rename f _ (K0 i)   := K0 (f _ i) ;
  e_rename f _ (K1 t π) := K1 (t_rename f _ t) (e_rename f _ π) ;
  e_rename f _ (K2 v π) := K2 (v_rename f _ v) (e_rename f _ π) .

Equations s_rename {Γ Δ} : Γ ⊆ Δ -> state Γ -> state Δ :=
  s_rename f (Cut t π) := Cut (t_rename f _ t) (e_rename f _ π).

Equations m_rename {Γ Δ} : Γ ⊆ Δ -> val_m Γ ⇒ᵢ val_m Δ :=
  m_rename f (+ _) v := v_rename f _ v ;
  m_rename f (¬ _) π := e_rename f _ π .
(*|
We can recast `m_rename` as an operator on assigments, more precisely as
renaming an assigment on the left.
|*)
Definition a_ren {Γ1 Γ2 Γ3} : Γ2 ⊆ Γ3 -> Γ1 =[val_m]> Γ2 -> Γ1 =[val_m]> Γ3 :=
  fun f g _ i => m_rename f _ (g _ i) .
(*|
The following bunch of notations will help us to keep the code readable:
|*)
Notation "f ᵣ⊛ₜ t" := (t_rename f _ t) (at level 30, right associativity).
Notation "f ᵣ⊛ᵥ v" := (v_rename f _ v) (at level 30, right associativity).
Notation "f ᵣ⊛ₑ π" := (e_rename f _ π) (at level 30, right associativity).
Notation "f ᵣ⊛ₘ v" := (m_rename f _ v) (at level 30, right associativity).
Notation "f ᵣ⊛ₛ s" := (s_rename f s) (at level 30, right associativity).
Notation "f ᵣ⊛ g" := (a_ren f g) (at level 30, right associativity).
(*|
As discussed above, we can now obtain our precious weakenings. Here are the
three we will need.
|*)
Definition t_shift {Γ a} := @t_rename Γ (Γ ▶ a) s_pop.
Definition m_shift2 {Γ a b} := @m_rename Γ (Γ ▶ a ▶ b) (s_pop ⊛ᵣ s_pop).
Definition a_shift2 {Γ Δ a b} (f : Γ =[val_m]> Δ) :=
  s_map m_shift2 f ▶ₐ a_id a (pop top) ▶ₐ a_id b top .
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
  v_subst f _ (LamRec t) := LamRec (t_subst (a_shift2 f) _ t) .

Equations e_subst {Γ Δ} : Γ =[val_m]> Δ -> ev_ctx Γ ⇒ᵢ ev_ctx Δ :=
  e_subst f _ (K0 i)   := f _ i ;
  e_subst f _ (K1 t π) := K1 (t_subst f _ t) (e_subst f _ π) ;
  e_subst f _ (K2 v π) := K2 (v_subst f _ v) (e_subst f _ π) .

Equations s_subst {Γ Δ} : Γ =[val_m]> Δ -> state Γ -> state Δ :=
  s_subst f (Cut t π) := Cut (t_subst f _ t) (e_subst f _ π).

Equations m_subst {Γ Δ} : Γ =[val_m]> Δ -> val_m Γ ⇒ᵢ val_m Δ :=
  m_subst f (+ _) v := v_subst f _ v ;
  m_subst f (¬ _) π := e_subst f _ π .
(*|
Like renaming, substitution is recast as composition of assigments.
|*)
Definition a_comp {Γ1 Γ2 Γ3} : Γ2 =[val_m]> Γ3 -> Γ1 =[val_m]> Γ2 -> Γ1 =[val_m]> Γ3 :=
  fun f g _ i => m_subst f _ (g _ i) .
(*|
These notations will make everything shine.
|*)
Notation "f ⊛ₜ t" := (t_subst f _ t) (at level 30, right associativity).
Notation "f ⊛ᵥ v" := (v_subst f _ v) (at level 30, right associativity).
Notation "f ⊛ₑ π" := (e_subst f _ π) (at level 30, right associativity).
Notation "f ⊛ₘ v" := (m_subst f _ v) (at level 30, right associativity).
Notation "f ⊛ₛ s" := (s_subst f s) (at level 30, right associativity).
Notation "f ⊛ g" := (a_comp f g) (at level 30, right associativity).
(*|
Finally we define a more usual substitution function which only substitutes
the top two variables instead of doing parallel substitution.
|*)
Definition assign2 {Γ a b} v1 v2 : (Γ ▶ a ▶ b) =[val_m]> Γ := a_id ▶ₐ v1 ▶ₐ v2 .
Definition t_subst2 {Γ a b c} (t : term _ c) v1 v2 := @assign2 Γ a b v1 v2 ⊛ₜ t.
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
  obs_dom (@ORet a)   := ∅ ▶ + a ;
  obs_dom (@OApp a b) := ∅ ▶ + a ▶ ¬ b .
(*|
Given a value, an observation on its type and a value for each fresh variable
of the observation, we can "refold" everything and form a new state which will
indeed observe this value.
|*)
Equations obs_app {Γ a} (v : val_m Γ a) (p : obs a) (γ : obs_dom p =[val_m]> Γ) : state Γ :=
  obs_app v (OApp) γ := Cut (Val v) (K2 (γ _ (pop top)) (γ _ top)) ;
  obs_app π (ORet) γ := Cut (Val (γ _ top)) π .
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
Definition nf  (Γ : t_ctx) : Type := { a : ty & (Γ ∋ a) × { o : obs a & obs_dom o =[val_m]> Γ } } .
(*|
The CBV Machine
^^^^^^^^^^^^^^^

Everything is now in place to define our state transition function. The
reduction rules should come to no surprise:

(1) `⟨ t1 t2 | π ⟩ → ⟨ t2 | t1 ⋅₁ π ⟩`

(2) `⟨ v | x ⟩` normal

(3) `⟨ v | t ⋅₁ π ⟩ →  ⟨ t | v ⋅₂ π ⟩`

(4) `⟨ x | v .₂ π ⟩` normal

(5) `⟨ λfx.t | v ⋅₂ π ⟩ → ⟨ t[f↦λfx.t; x↦v] |  π ⟩`

Rules 1,3,5 step to a new configuration, while cases 2,4 are stuck on normal
forms.
|*)
Equations eval_aux {Γ : t_ctx} : state Γ -> (state Γ + nf Γ) :=
  eval_aux (Cut (App t1 t2)      (π))      := inl (Cut t2 (K1 t1 π)) ;
  eval_aux (Cut (Val v)          (K0 i))   := inr (_ ,' (i, (ORet ,' (∅ₐ ▶ₐ v)))) ;
  eval_aux (Cut (Val v)          (K1 t π)) := inl (Cut t (K2 v π)) ;
  eval_aux (Cut (Val (Var i))    (K2 v π)) := inr (_,' (i, (OApp ,' (∅ₐ ▶ₐ v ▶ₐ π)))) ;
  eval_aux (Cut (Val (LamRec t)) (K2 v π)) := inl (Cut (t /[ LamRec t , v ]) π) .
(*|
Having defined the transition function, we can now iterate it inside the delay
monad. This constructs a possibly non-terminating computation ending with
a normal form.
|*)
Definition eval {Γ : t_ctx} : state Γ -> delay (nf Γ)
  := iter_delay (ret_delay ∘ eval_aux).
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
    ind_lamrec {Γ a b} t (_ : P_t _ b t) : P_v Γ (a → b) (LamRec t) ;
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
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> f1 ᵣ⊛ₜ t = f2 ᵣ⊛ₜ t .
Definition v_ren_proper_P Γ a (v : val Γ a) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> f1 ᵣ⊛ᵥ v = f2 ᵣ⊛ᵥ v .
Definition e_ren_proper_P Γ a (π : ev_ctx Γ a) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> f1 ᵣ⊛ₑ π = f2 ᵣ⊛ₑ π .
Lemma ren_proper_prf : syn_ind_args t_ren_proper_P v_ren_proper_P e_ren_proper_P.
  econstructor.
  all: unfold t_ren_proper_P, v_ren_proper_P, e_ren_proper_P.
  all: intros; cbn; f_equal; auto.
  all: apply H.
  now do 2 apply r_shift_eq.
Qed.

#[global] Instance t_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@t_rename Γ Δ).
  intros f1 f2 H1 a x y ->; now apply (term_ind_mut _ _ _ ren_proper_prf).
Qed.
#[global] Instance v_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@v_rename Γ Δ).
  intros f1 f2 H1 a x y ->; now apply (val_ind_mut _ _ _ ren_proper_prf).
Qed.
#[global] Instance e_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@e_rename Γ Δ).
  intros f1 f2 H1 a x y ->; now apply (ctx_ind_mut _ _ _ ren_proper_prf).
Qed.
#[global] Instance m_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@m_rename Γ Δ).
  intros ? ? H1 [] _ ? ->; cbn in *; now rewrite H1.
Qed.
#[global] Instance s_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> eq ==> eq) (@s_rename Γ Δ).
  intros ? ? H1 _ x ->; destruct x; cbn; now rewrite H1.
Qed.
#[global] Instance a_ren_eq {Γ1 Γ2 Γ3}
  : Proper (ass_eq _ _ ==> ass_eq _ _ ==> ass_eq _ _) (@a_ren Γ1 Γ2 Γ3).
  intros ? ? H1 ? ? H2 ? ?; apply (m_ren_eq _ _ H1), H2.
Qed.
#[global] Instance a_shift2_eq {Γ Δ x y} : Proper (ass_eq _ _ ==> ass_eq _ _) (@a_shift2 Γ Δ x y).
  intros ? ? H ? h.
  do 2 (dependent elimination h; cbn; auto).
  unfold s_map; now rewrite H.
Qed.
(*|
Lemma 2: renaming-renaming assocativity. I say "associativity" because it
definitely looks like associativity if we disregard the subscripts. More
precisely it could be described as the composition law a right action.
|*)
Definition t_ren_ren_P Γ1 a (t : term Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2),
    f1 ᵣ⊛ₜ (f2 ᵣ⊛ₜ t) = (f1 ⊛ᵣ f2) ᵣ⊛ₜ t .
Definition v_ren_ren_P Γ1 a (v : val Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2),
    f1 ᵣ⊛ᵥ (f2 ᵣ⊛ᵥ v) = (f1 ⊛ᵣ f2) ᵣ⊛ᵥ v .
Definition e_ren_ren_P Γ1 a (π : ev_ctx Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2),
    f1 ᵣ⊛ₑ (f2 ᵣ⊛ₑ π) = (f1 ⊛ᵣ f2) ᵣ⊛ₑ π .

Lemma ren_ren_prf : syn_ind_args t_ren_ren_P v_ren_ren_P e_ren_ren_P .
  econstructor.
  all: unfold t_ren_ren_P, v_ren_ren_P, e_ren_ren_P.
  all: intros; cbn; f_equal; auto.
  all: unfold r_shift2; now repeat rewrite r_shift_comp.
Qed.

Lemma t_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) a (t : term Γ1 a)
  : f1 ᵣ⊛ₜ (f2 ᵣ⊛ₜ t) = (f1 ⊛ᵣ f2) ᵣ⊛ₜ t .
  now apply (term_ind_mut _ _ _ ren_ren_prf).
Qed.
Lemma v_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) a (v : val Γ1 a)
  : f1 ᵣ⊛ᵥ (f2 ᵣ⊛ᵥ v) = (f1 ⊛ᵣ f2) ᵣ⊛ᵥ v .
  now apply (val_ind_mut _ _ _ ren_ren_prf).
Qed.
Lemma e_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) a (π : ev_ctx Γ1 a)
  : f1 ᵣ⊛ₑ (f2 ᵣ⊛ₑ π) = (f1 ⊛ᵣ f2) ᵣ⊛ₑ π .
  now apply (ctx_ind_mut _ _ _ ren_ren_prf).
Qed.
Lemma m_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) a (v : val_m Γ1 a)
  : f1 ᵣ⊛ₘ (f2 ᵣ⊛ₘ v) = (f1 ⊛ᵣ f2) ᵣ⊛ₘ v .
  destruct a; [ now apply v_ren_ren | now apply e_ren_ren ].
Qed.
Lemma s_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) (s : state Γ1)
  : f1 ᵣ⊛ₛ (f2 ᵣ⊛ₛ s) = (f1 ⊛ᵣ f2) ᵣ⊛ₛ s .
  destruct s; apply (f_equal2 Cut); [ now apply t_ren_ren | now apply e_ren_ren ].
Qed.
(*|
Lemma 3: left identity law of renaming.
|*)
Definition t_ren_id_l_P Γ a (t : term Γ a) : Prop := r_id ᵣ⊛ₜ t = t .
Definition v_ren_id_l_P Γ a (v : val Γ a) : Prop := r_id ᵣ⊛ᵥ v = v .
Definition e_ren_id_l_P Γ a (π : ev_ctx Γ a) : Prop := r_id ᵣ⊛ₑ π = π .
Lemma ren_id_l_prf : syn_ind_args t_ren_id_l_P v_ren_id_l_P e_ren_id_l_P .
  econstructor.
  all: unfold t_ren_id_l_P, v_ren_id_l_P, e_ren_id_l_P.
  all: intros; cbn; f_equal; auto.
  unfold r_shift2; now repeat rewrite r_shift_id.
Qed.

Lemma t_ren_id_l {Γ} a (t : term Γ a) : r_id ᵣ⊛ₜ t = t .
  now apply (term_ind_mut _ _ _ ren_id_l_prf).
Qed.
Lemma v_ren_id_l {Γ} a (v : val Γ a) : r_id ᵣ⊛ᵥ v = v .
  now apply (val_ind_mut _ _ _ ren_id_l_prf).
Qed.
Lemma e_ren_id_l {Γ} a (π : ev_ctx Γ a) : r_id ᵣ⊛ₑ π = π .
  now apply (ctx_ind_mut _ _ _ ren_id_l_prf).
Qed.
Lemma m_ren_id_l {Γ} a (v : val_m Γ a) : r_id ᵣ⊛ₘ v = v .
  destruct a; [ now apply v_ren_id_l | now apply e_ren_id_l ].
Qed.
Lemma s_ren_id_l {Γ} (s : state Γ) : r_id ᵣ⊛ₛ s = s .
  destruct s; apply (f_equal2 Cut); [ now apply t_ren_id_l | now apply e_ren_id_l ].
Qed.
(*|
Lemma 4: right identity law of renaming. This one basically holds
definitionally, it only needs a case split for some of the derived notions. We
will also prove a consequence on weakenings: identity law.
|*)
Lemma m_ren_id_r {Γ Δ} (f : Γ ⊆ Δ) {a} (i : Γ ∋ a) : f ᵣ⊛ₘ a_id a i = a_id a (f a i) .
  now destruct a.
Qed.
Lemma a_ren_id_r {Γ Δ} (f : Γ ⊆ Δ) : f ᵣ⊛ a_id ≡ₐ a_id ⊛ᵣ f .
  intros ? ?; now apply m_ren_id_r.
Qed.
Lemma a_shift2_id {Γ x y} : @a_shift2 Γ Γ x y a_id ≡ₐ a_id.
  unfold a_shift2, m_shift2; intros ? h.
  do 2 (dependent elimination h; cbn; auto).
  exact (m_ren_id_r _ _).
Qed.
(*|
Lemma 5: shifting assigments commutes with left and right renaming.
|*)
Lemma a_shift2_s_ren {Γ1 Γ2 Γ3 a b} (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 ⊆ Γ2)
  : @a_shift2 _ _ a b (f1 ⊛ᵣ f2) ≡ₐ a_shift2 f1 ⊛ᵣ r_shift2 f2 .
  intros ? h; do 2 (dependent elimination h; auto).
Qed.
Lemma a_shift2_a_ren {Γ1 Γ2 Γ3 a b} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val_m]> Γ2)
      : @a_shift2 _ _ a b (f1 ᵣ⊛ f2) ≡ₐ r_shift2 f1 ᵣ⊛ a_shift2 f2 .
  unfold r_shift2, r_shift, a_shift2, m_shift2, a_ren; intros ? h.
  do 2 (dependent elimination h; cbn; [ symmetry; exact (a_ren_id_r _ _ _) | ]).
  unfold s_map; now rewrite 2 m_ren_ren.
Qed.
(*|
Lemma 6: substitution respects pointwise equality of assigments.
|*)
Definition t_sub_proper_P Γ a (t : term Γ a) : Prop :=
  forall Δ (f1 f2 : Γ =[val_m]> Δ), f1 ≡ₐ f2 -> f1 ⊛ₜ t = f2 ⊛ₜ t .
Definition v_sub_proper_P Γ a (v : val Γ a) : Prop :=
  forall Δ (f1 f2 : Γ =[val_m]> Δ), f1 ≡ₐ f2 -> f1 ⊛ᵥ v = f2 ⊛ᵥ v .
Definition e_sub_proper_P Γ a (π : ev_ctx Γ a) : Prop :=
  forall Δ (f1 f2 : Γ =[val_m]> Δ), f1 ≡ₐ f2 -> f1 ⊛ₑ π = f2 ⊛ₑ π .
Lemma sub_proper_prf : syn_ind_args t_sub_proper_P v_sub_proper_P e_sub_proper_P.
  econstructor.
  all: unfold t_sub_proper_P, v_sub_proper_P, e_sub_proper_P.
  all: intros; cbn; f_equal; auto.
  now apply H, a_shift2_eq.
Qed.

#[global] Instance t_sub_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@t_subst Γ Δ).
  intros ? ? H1 a _ ? ->; now apply (term_ind_mut _ _ _ sub_proper_prf).
Qed.
#[global] Instance v_sub_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@v_subst Γ Δ).
  intros ? ? H1 a _ ? ->; now apply (val_ind_mut _ _ _ sub_proper_prf).
Qed.
#[global] Instance e_sub_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@e_subst Γ Δ).
  intros ? ? H1 a _ ? ->; now apply (ctx_ind_mut _ _ _ sub_proper_prf).
Qed.
#[global] Instance m_sub_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@m_subst Γ Δ).
  intros ? ? H1 [] _ ? ->; cbn in *; now rewrite H1.
Qed.
#[global] Instance s_sub_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> eq ==> eq) (@s_subst Γ Δ).
  intros ? ? H1 _ x ->; destruct x; cbn; now rewrite H1.
Qed.
#[global] Instance a_comp_eq {Γ1 Γ2 Γ3} : Proper (ass_eq _ _ ==> ass_eq _ _ ==> ass_eq _ _) (@a_comp Γ1 Γ2 Γ3).
  intros ? ? H1 ? ? H2 ? ?; unfold a_comp; now rewrite H1, H2.
Qed.
(*|
Lemma 7: renaming-substitution "associativity".
|*)
Definition t_ren_sub_P Γ1 a (t : term Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val_m]> Γ2),
    f1 ᵣ⊛ₜ (f2 ⊛ₜ t) = (f1 ᵣ⊛ f2) ⊛ₜ t .
Definition v_ren_sub_P Γ1 a (v : val Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val_m]> Γ2),
    f1 ᵣ⊛ᵥ (f2 ⊛ᵥ v) = (f1 ᵣ⊛ f2) ⊛ᵥ v .
Definition e_ren_sub_P Γ1 a (π : ev_ctx Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val_m]> Γ2),
    f1 ᵣ⊛ₑ (f2 ⊛ₑ π) = (f1 ᵣ⊛ f2) ⊛ₑ π .
Lemma ren_sub_prf : syn_ind_args t_ren_sub_P v_ren_sub_P e_ren_sub_P.
  econstructor.
  all: unfold t_ren_sub_P, v_ren_sub_P, e_ren_sub_P.
  all: intros; cbn; f_equal.
  all: try rewrite a_shift2_a_ren; auto.
Qed.

Lemma t_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val_m]> Γ2) a (t : term Γ1 a)
  : f1 ᵣ⊛ₜ (f2 ⊛ₜ t) = (f1 ᵣ⊛ f2) ⊛ₜ t .
  now apply (term_ind_mut _ _ _ ren_sub_prf).
Qed.
Lemma v_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val_m]> Γ2) a (v : val Γ1 a)
  : f1 ᵣ⊛ᵥ (f2 ⊛ᵥ v) = (f1 ᵣ⊛ f2) ⊛ᵥ v .
  now apply (val_ind_mut _ _ _ ren_sub_prf).
Qed.
Lemma e_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val_m]> Γ2) a (π : ev_ctx Γ1 a)
  : f1 ᵣ⊛ₑ (f2 ⊛ₑ π) = (f1 ᵣ⊛ f2) ⊛ₑ π .
  now apply (ctx_ind_mut _ _ _ ren_sub_prf).
Qed.
Lemma m_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val_m]> Γ2) a (v : val_m Γ1 a)
  : f1 ᵣ⊛ₘ (f2 ⊛ₘ v) = (f1 ᵣ⊛ f2) ⊛ₘ v .
  destruct a; [ now apply v_ren_sub | now apply e_ren_sub ].
Qed.
Lemma s_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val_m]> Γ2) (s : state Γ1)
  : f1 ᵣ⊛ₛ (f2 ⊛ₛ s) = (f1 ᵣ⊛ f2) ⊛ₛ s .
  destruct s; cbn; now rewrite t_ren_sub, e_ren_sub.
Qed.
(*|
Lemma 8: substitution-renaming "associativity".
|*)
Definition t_sub_ren_P Γ1 a (t : term Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 ⊆ Γ2),
  f1 ⊛ₜ (f2 ᵣ⊛ₜ t) = (f1 ⊛ᵣ f2) ⊛ₜ t .
Definition v_sub_ren_P Γ1 a (v : val Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 ⊆ Γ2),
  f1 ⊛ᵥ (f2 ᵣ⊛ᵥ v) = (f1 ⊛ᵣ f2) ⊛ᵥ v .
Definition e_sub_ren_P Γ1 a (π : ev_ctx Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 ⊆ Γ2),
  f1 ⊛ₑ (f2 ᵣ⊛ₑ π) = (f1 ⊛ᵣ f2) ⊛ₑ π .
Lemma sub_ren_prf : syn_ind_args t_sub_ren_P v_sub_ren_P e_sub_ren_P.
  econstructor.
  all: unfold t_sub_ren_P, v_sub_ren_P, e_sub_ren_P.
  all: intros; cbn; f_equal.
  all: try rewrite a_shift2_s_ren; auto.
Qed.

Lemma t_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 ⊆ Γ2) a (t : term Γ1 a)
  : f1 ⊛ₜ (f2 ᵣ⊛ₜ t) = (f1 ⊛ᵣ f2) ⊛ₜ t .
  now apply (term_ind_mut _ _ _ sub_ren_prf).
Qed.
Lemma v_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 ⊆ Γ2) a (v : val Γ1 a)
  : f1 ⊛ᵥ (f2 ᵣ⊛ᵥ v) = (f1 ⊛ᵣ f2) ⊛ᵥ v .
  now apply (val_ind_mut _ _ _ sub_ren_prf).
Qed.
Lemma e_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 ⊆ Γ2) a (π : ev_ctx Γ1 a)
  : f1 ⊛ₑ (f2 ᵣ⊛ₑ π) = (f1 ⊛ᵣ f2) ⊛ₑ π .
  now apply (ctx_ind_mut _ _ _ sub_ren_prf).
Qed.
Lemma m_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 ⊆ Γ2) a (v : val_m Γ1 a)
  : f1 ⊛ₘ (f2 ᵣ⊛ₘ v) = (f1 ⊛ᵣ f2) ⊛ₘ v .
  destruct a; [ now apply v_sub_ren | now apply e_sub_ren ].
Qed.
Lemma s_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 ⊆ Γ2) (s : state Γ1)
  : f1 ⊛ₛ (f2 ᵣ⊛ₛ s) = (f1 ⊛ᵣ f2) ⊛ₛ s .
  destruct s; cbn; now rewrite t_sub_ren, e_sub_ren.
Qed.
(*|
Lemma 9: left identity law of substitution.
|*)
Definition t_sub_id_l_P Γ a (t : term Γ a) : Prop := a_id ⊛ₜ t = t .
Definition v_sub_id_l_P Γ a (v : val Γ a) : Prop := a_id ⊛ᵥ v = v .
Definition e_sub_id_l_P Γ a (π : ev_ctx Γ a) : Prop := a_id ⊛ₑ π = π .
Lemma sub_id_l_prf : syn_ind_args t_sub_id_l_P v_sub_id_l_P e_sub_id_l_P.
  econstructor.
  all: unfold t_sub_id_l_P, v_sub_id_l_P, e_sub_id_l_P.
  all: intros; cbn; f_equal; auto.
  all: try rewrite a_shift2_id; auto.
Qed.

Lemma t_sub_id_l {Γ} a (t : term Γ a) : a_id ⊛ₜ t = t .
  now apply (term_ind_mut _ _ _ sub_id_l_prf).
Qed.
Lemma v_sub_id_l {Γ} a (v : val Γ a) : a_id ⊛ᵥ v = v .
  now apply (val_ind_mut _ _ _ sub_id_l_prf).
Qed.
Lemma e_sub_id_l {Γ} a (π : ev_ctx Γ a) : a_id ⊛ₑ π = π .
  now apply (ctx_ind_mut _ _ _ sub_id_l_prf).
Qed.
Lemma m_sub_id_l {Γ} a (v : val_m Γ a) : a_id ⊛ₘ v = v.
  destruct a; [ now apply v_sub_id_l | now apply e_sub_id_l ].
Qed.
Lemma s_sub_id_l {Γ} (s : state Γ) : a_id ⊛ₛ s = s.
  destruct s; cbn; now rewrite t_sub_id_l, e_sub_id_l.
Qed.
Lemma a_comp_id_l {Γ1 Γ2} (a : Γ1 =[val_m]> Γ2) : a_id ⊛ a ≡ₐ a .
  intros ? ?; now apply m_sub_id_l.
Qed.
(*|
Lemma 9: right identity law of substitution. As for renaming, this one is
mostly by definition.
|*)
Lemma m_sub_id_r {Γ1 Γ2} (f : Γ1 =[val_m]> Γ2) {a} (i : Γ1 ∋ a) : f ⊛ₘ a_id a i = f a i.
  now destruct a.
Qed.
Lemma a_comp_id_r {Γ1 Γ2} (f : Γ1 =[val_m]> Γ2) : f ⊛ a_id ≡ₐ f .
  intros a ?; now apply m_sub_id_r.
Qed.
(*|
Lemma 10: shifting assigments respects composition.
|*)
Lemma a_shift2_comp {Γ1 Γ2 Γ3 a b} (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 =[val_m]> Γ2)
  : @a_shift2 _ _ a b (f1 ⊛ f2) ≡ₐ a_shift2 f1 ⊛ a_shift2 f2 .
  unfold a_shift2, m_shift2, a_comp; intros ? h.
  do 2 (dependent elimination h; [ symmetry; exact (a_comp_id_r _ _ _) | cbn ]).
  unfold s_map; now rewrite m_ren_sub, m_sub_ren.
Qed.
(*|
Lemma 11: substitution-substitution associativity, ie composition law.
|*)
Definition t_sub_sub_P Γ1 a (t : term Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 =[val_m]> Γ2),
    f1 ⊛ₜ (f2 ⊛ₜ t) = (f1 ⊛ f2) ⊛ₜ t.
Definition v_sub_sub_P Γ1 a (v : val Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 =[val_m]> Γ2),
    f1 ⊛ᵥ (f2 ⊛ᵥ v) = (f1 ⊛ f2) ⊛ᵥ v.
Definition e_sub_sub_P Γ1 a (π : ev_ctx Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 =[val_m]> Γ2),
    f1 ⊛ₑ (f2 ⊛ₑ π) = (f1 ⊛ f2) ⊛ₑ π.
Lemma sub_sub_prf : syn_ind_args t_sub_sub_P v_sub_sub_P e_sub_sub_P.
  econstructor.
  all: unfold t_sub_sub_P, v_sub_sub_P, e_sub_sub_P.
  all: intros; cbn; f_equal.
  all: try rewrite a_shift2_comp; auto.
Qed.

Lemma t_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 =[val_m]> Γ2) a (t : term Γ1 a)
  : f1 ⊛ₜ (f2 ⊛ₜ t) = (f1 ⊛ f2) ⊛ₜ t.
  now apply (term_ind_mut _ _ _ sub_sub_prf).
Qed.
Lemma v_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 =[val_m]> Γ2) a (v : val Γ1 a)
  : f1 ⊛ᵥ (f2 ⊛ᵥ v) = (f1 ⊛ f2) ⊛ᵥ v.
  now apply (val_ind_mut _ _ _ sub_sub_prf).
Qed.
Lemma e_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 =[val_m]> Γ2) a (π : ev_ctx Γ1 a)
  : f1 ⊛ₑ (f2 ⊛ₑ π) = (f1 ⊛ f2) ⊛ₑ π.
  now apply (ctx_ind_mut _ _ _ sub_sub_prf).
Qed.
Lemma m_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 =[val_m]> Γ2) a (v : val_m Γ1 a)
  : f1 ⊛ₘ (f2 ⊛ₘ v) = (f1 ⊛ f2) ⊛ₘ v.
  destruct a; [ now apply v_sub_sub | now apply e_sub_sub ].
Qed.
Lemma s_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 =[val_m]> Γ2) (s : state Γ1)
  : f1 ⊛ₛ (f2 ⊛ₛ s) = (f1 ⊛ f2) ⊛ₛ s.
  destruct s; cbn; now rewrite t_sub_sub, e_sub_sub.
Qed.
Lemma a_comp_assoc {Γ1 Γ2 Γ3 Γ4} (u : Γ3 =[val_m]> Γ4) (v : Γ2 =[val_m]> Γ3) (w : Γ1 =[val_m]> Γ2)
           : u ⊛ (v ⊛ w) ≡ₐ (u ⊛ v) ⊛ w .
  intros ? ?; unfold a_comp; now apply m_sub_sub.
Qed.
Lemma a_sub2_sub {Γ Δ a b} (f : Γ =[val_m]> Δ) (v1 : val_m Γ a) (v2 : val_m Γ b)
  : assign2 (f ⊛ₘ v1) (f ⊛ₘ v2) ⊛ a_shift2 f ≡ₐ f ⊛ (assign2 v1 v2).
  
  intros ? h; unfold a_comp.
  do 2 (dependent elimination h; [ cbn; now rewrite m_sub_id_r | ]).
  cbn; unfold s_map, m_shift2; rewrite m_sub_ren, m_sub_id_r.
  now apply m_sub_id_l.
Qed.
Lemma t_sub2_sub {Γ Δ x y z} (f : Γ =[val_m]> Δ) (t : term (Γ ▶ x ▶ y) z) u v
  : t_subst (a_shift2 f) _ t /[ m_subst f _ u , m_subst f _ v ] = t_subst f _ (t /[ u , v ]) .
  unfold t_subst2; now rewrite 2 t_sub_sub, a_sub2_sub.
Qed.

(*
#[global] Instance p_app_eq {Γ x} (v : val_m Γ x) (m : pat (t_neg x)) : Proper (ass_eq _ _ ==> eq) (p_app v m) .
  intros ? ? H.
  destruct x; dependent elimination m; cbn in *; now repeat rewrite H.
Qed.
*)

From OGS.OGS Require Spec.

Definition stlc_spec : Spec.interaction_spec :=
  {| Spec.typ := ty ;
     Spec.msg := obs ;
     Spec.dom := @obs_dom |}
.

Program Definition stlc_val : @Spec.lang_monoid stlc_spec :=
  {| Spec.val := val_m ;
     Spec.v_var := @a_id ;
     Spec.v_sub := @m_subst
  |}.

Program Definition stlc_conf : @Spec.lang_module stlc_spec stlc_val :=
  {| Spec.conf := state ;
     Spec.c_sub := @s_subst ;
  |}.

Program Definition stlc_val_laws : @Spec.lang_monoid_laws stlc_spec stlc_val :=
  {| Spec.v_sub_proper := @m_sub_eq ;
     Spec.v_sub_var := @a_comp_id_r ;
     Spec.v_var_sub := @a_comp_id_l ;
     Spec.v_sub_sub := @a_comp_assoc ;
  |} .

Program Definition stlc_conf_laws : @Spec.lang_module_laws stlc_spec stlc_val stlc_conf :=
  {| Spec.c_sub_proper := @s_sub_eq ;
     Spec.c_var_sub := @s_sub_id_l ;
     Spec.c_sub_sub := @s_sub_sub ;
  |} .

Definition stlc_var_laws : @Spec.var_assumptions stlc_spec stlc_val .
  econstructor; intros.
  - destruct x; now dependent induction H.
  - destruct x; induction v; try (apply inr; intros [ i H ]; now inversion H).
    all: apply inl; econstructor; auto.
  - destruct X as [ i H ].
    destruct x; induction v; try now inversion H.
    all: refine (h ,' eq_refl).
Defined.

Program Definition stlc_machine : @Spec.machine stlc_spec stlc_val stlc_conf :=
  {| Spec.eval := @eval ;
     Spec.app := @obs_app ; |}.

From Coinduction Require Import coinduction lattice rel tactics.
From OGS.ITree Require Import Eq.
From OGS.OGS Require Import Spec.

Lemma stlc_machine_law : @Spec.machine_laws stlc_spec stlc_val stlc_conf stlc_machine .
  econstructor; intros; unfold stlc_spec, stlc_val in *; cbn.
  - intros ? ? H1; dependent elimination m; cbn; repeat (f_equal; auto).
  - destruct x; dependent elimination m; cbn; f_equal.
  - revert c e; unfold comp_eq, it_eq; coinduction R CIH; intros c e.
    destruct c. cbn in e0.
    dependent elimination t.
    * dependent elimination e0.
      + simpl c_sub.
        unfold stlc_new.eval at 2.
        cbn - [ stlc_new.eval ].
        change (it_eqF _ ?a ?b T1_0 (observe ?x) (_observe ?y)) with (it_eq_bt _ a R T1_0 x y).
        refine (gfp_bt (it_eq_map _ _) R T1_0 _ _ _); reflexivity.
      + cbn; econstructor.
        exact (CIH (Cut t0 (K2 v e0)) e).
      + dependent elimination v.
        ++ simpl s_subst.
           unfold stlc_new.eval at 2.
           cbn - [ stlc_new.eval ].
           change (it_eqF _ ?a _ T1_0 (observe ?x) (_observe ?y)) with (it_eq_bt _ a R T1_0 x y).
           refine (gfp_bt (it_eq_map _ _) R T1_0 _ _ _); reflexivity.
        ++ cbn; econstructor.
           change (LamRec _) with (v_subst e _ (LamRec t0)) at 1.
           change (v_subst e _ ?a) with (m_subst e (+ _) a).
           rewrite t_sub2_sub.
           exact (CIH (Cut (t0 /[ LamRec t0 , v0 ]) e1) e).
    * cbn; econstructor.
      exact (CIH (Cut t1 (K1 t0 e0)) e).
  - destruct u as [ a [ i [ p γ ] ]].
    unfold nf_ty', nf_var', nf_val', a_id; cbn in *.
    destruct a; dependent elimination p; cbn in *.
    all: unfold comp_eq; apply it_eq_unstep; cbn; econstructor.
    all: do 3 (unshelve econstructor; auto; cbn).
    all: intros ? h; do 3 (dependent elimination h; auto).
  - intros [ x p ].
    destruct x; dependent elimination p; econstructor.
    * intros [ z p ] H.
      destruct z; dependent elimination p; dependent elimination H.
      + dependent elimination v; try now destruct (p (_ ,' eq_refl)).
        apply it_eq_step in i0; now inversion i0.
      + dependent elimination v; try now destruct (p (_ ,' eq_refl)).
        apply it_eq_step in i0; now inversion i0.
    * intros [ z p ] H.
      destruct z; dependent elimination p; dependent elimination H.
      + cbn in *.
        pose (vv :=e (+ a) Ctx.top); change (e (+ a) Ctx.top) with vv in i0; remember vv; clear vv Heqv0 e.
        dependent elimination v; try now destruct (p (_ ,' eq_refl)).
        apply it_eq_step in i0; now inversion i0.
        dependent elimination v0; apply it_eq_step in i0; cbn in i0; dependent elimination i0.
        unfold msg_of_nf' in r_rel; cbn in r_rel.
        inversion_sigma r_rel; dependent elimination r_rel1; clear .
        econstructor; intros [ z p ] H.
        destruct z; dependent elimination p; dependent elimination H.
        ++ dependent elimination v; try now destruct (p (_ ,' eq_refl)).
           apply it_eq_step in i0; now inversion i0.
        ++ dependent elimination v; try now destruct (p (_ ,' eq_refl)).
           apply it_eq_step in i0; now inversion i0.
      + cbn in *.
        pose (vv :=e (+ a) Ctx.top); change (e (+ a) Ctx.top) with vv in i0; remember vv; clear vv Heqv0 e.
        dependent elimination v; try now destruct (p (_ ,' eq_refl)).
        apply it_eq_step in i0; now inversion i0.
        dependent elimination v0; apply it_eq_step in i0; cbn in i0; dependent elimination i0.
        unfold msg_of_nf' in r_rel; cbn in r_rel.
        inversion_sigma r_rel; inversion r_rel1.
Qed.

Definition sem_act Δ Γ := @ogs_act stlc_spec Δ (∅ ▶ Γ) .

Definition interp_act_s Δ {Γ} (c : state Γ) : sem_act Δ Γ :=
  @Spec.m_strat stlc_spec stlc_val stlc_conf stlc_machine Δ (∅ ▶ Γ)
    (@Spec.inj_init_act stlc_spec stlc_val stlc_conf Δ Γ c) .
Notation "⟦ t ⟧ₛ" := (interp_act_s _ t) .

Definition ogs_weq_act Δ {Γ} : relation (sem_act Δ Γ) := fun u v => u ≈ v .
Notation "u ≈[ogs Δ ]≈ v" := (ogs_weq_act Δ u v) (at level 40).

Definition eval2msg {Γ : t_ctx} : state Γ -> delay (@msg' stlc_spec Γ) :=
  @eval_to_msg stlc_spec stlc_val stlc_conf stlc_machine Γ .

Definition subst_eq Δ {Γ} : relation (state Γ) :=
  fun u v => forall σ : Γ =[val_m]> Δ, eval2msg (σ ⊛ₛ u) ≈ eval2msg (σ ⊛ₛ v) .
Notation "x ≈[sub Δ ]≈ y" := (subst_eq Δ x y) (at level 10).

Theorem stlc_subst_correct Δ {Γ} (x y : state Γ) : ⟦ x ⟧ₛ ≈[ogs Δ ]≈ ⟦ y ⟧ₛ -> x ≈[sub Δ ]≈ y .
  exact (@ogs_correction stlc_spec stlc_val stlc_val_laws stlc_conf stlc_conf_laws stlc_var_laws
           stlc_machine stlc_machine_law Γ Δ x y).
Qed.

Definition c_of_t {Γ a} (t : term Γ a) : state (Γ ▶ ¬ a) := Cut (t_shift _ t) (K0 Ctx.top) .
Notation "⟦ t ⟧ₜ" := (⟦ c_of_t t ⟧ₛ) .

Definition a_of_sk {Γ Δ a} (σ : Γ =[val_m]> Δ) (π : ev_ctx Δ a)
  : (Γ ▶ ¬ a) =[val_m]> Δ := σ ▶ₐ (π : val_m _ (¬ _)) .

Definition ciu_eq Δ {Γ a} : relation (term Γ a) :=
  fun u v => forall (σ : Γ =[val_m]> Δ) (π : ev_ctx Δ a),
      eval2msg (Cut (σ ⊛ₜ u) π) ≈ eval2msg (Cut (σ ⊛ₜ v) π) .
Notation "x ≈[ciu Δ ]≈ y" := (ciu_eq Δ x y) (at level 10).

Lemma sub_csk_p {Γ Δ a} (t : term Γ a) (σ : Γ =[val_m]> Δ) (π : ev_ctx Δ a)
  : Cut (σ ⊛ₜ t) π = a_of_sk σ π ⊛ₛ c_of_t t .
  cbn; unfold t_shift; now rewrite t_sub_ren.
Qed.

Theorem stlc_ciu_correct Δ {Γ a} (x y : term Γ a) : ⟦ x ⟧ₜ ≈[ogs Δ ]≈ ⟦ y ⟧ₜ -> x ≈[ciu Δ ]≈ y .
  intros H σ k; rewrite 2 sub_csk_p.
  now apply stlc_subst_correct.
Qed.
(*|
.. [AACMM21] Guillaume Allais et al, "A type- and scope-safe universe of
   syntaxes with binding: their semantics and proofs", 2021.
.. [FS22] Marcelo Fiore & Dmitrij Szamozvancev, "Formal Metatheory of
   Second-Order Abstract Syntax", 2022.
.. [L05] Soren Lassen, "Eager Normal Form Bisimulation", 2005.

|*)
