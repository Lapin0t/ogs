(*|
============================
Simply-typed lambda-calculus
============================


.. coq:: none
|*)
Set Primitive Projections.

From Coq Require Import Logic.
From Coq Require Import Program.Equality.
Import EqNotations.
Require Import Psatz.

From ExtLib.Data Require Import List.

From OGS Require Import Utils.
From OGS.ITree Require Import Cat Event Dual ITree Rec Angelic Eq.
From OGS.STLC Require Import Ctx.

From Equations Require Import Equations.
Set Equations Transparent.

(*
From OGS Require Import OGSD.
From OGS Require Import EqD.
*)

(*|
Syntax
------

First we will define the well-typed syntax of our language.

Context and types
^^^^^^^^^^^^^^^^^

Let's define the types of our language. We will have unit, product,
disjoint union (ie sum) and functions, equipped with the usual notations.
|*)

Inductive ty : Type :=
| Unit : ty
| Prod : ty -> ty -> ty
| Arr : ty -> ty -> ty
| Sum : ty -> ty -> ty
.

(*| .. coq:: none |*)
Derive NoConfusion for ty.
Declare Scope ty_scope.
Delimit Scope ty_scope with ty.
Bind Scope ty_scope with ty.

(*||*)
Notation "A → B" := (Arr A B) (at level 40) : ty_scope .
Notation "A × B" := (Prod A B) (at level 40) : ty_scope.
Notation "A + B" := (Sum A B) : ty_scope.

(*|
Our contexts (stacks of types) will be called ``t_ctx``. They are defined generically
in ``Ctx.v``.
|*)
Definition t_ctx : Type := Ctx.ctx ty.
Bind Scope ctx_scope with t_ctx.

(*|
Negative and positive types
^^^^^^^^^^^^^^^^^^^^^^^^^^^

Our next couple of definitions will focus on segregating types between "positive"
and "negative" types. These terms are heavily overloaded in language theory with
subtle differences between concepts of polarization:

- polarized linear logic, focusing & proof nets
- values (+) vs computation (-) in call-by-push-value (CBPV) and other
  effect calculi
- inductive data-types (+) vs coinductive record-types (-) in agda and
  coq (with primitive projections)

Our language is quite concrete as such we won't try to relate our
notion of polarity too precisely with these notions: our only negative
type is function type (irrespective of the domain and codomain) while
unit, product and sum are positive. What is important for us is that
values of negative types are *opaque* in the sense that a term can
only destruct it (eg apply a function).

We'll define an ``is_neg`` predicate, negative types and contexts
containing only negative types.
|*)
Variant is_neg : ty -> Prop := | NArr {a b} : is_neg (a → b) .
Definition neg_ty : Type := { t : ty | is_neg t }.
Definition neg_ctx : Type := Ctx.ctx neg_ty.

(*| .. coq:: none |*)
Definition of_n_ty (t : neg_ty) : ty := proj1_sig t.
Coercion of_n_ty : neg_ty >-> ty.

Bind Scope ctx_scope with neg_ctx.
Bind Scope ctx_scope with ctx.
Definition of_n_ctx : neg_ctx -> t_ctx := map of_n_ty.
Coercion of_n_ctx : neg_ctx >-> t_ctx.

Equations of_n_var {Γ x} (i : Γ ∋ x) : (of_n_ctx Γ) ∋ of_n_ty x :=
  of_n_var top     := top ;
  of_n_var (pop i) := pop (of_n_var i) .

(*|
Our first non-trivial lemma: if a variable in negative context has
type ``x`` then ``x`` is negative.
|*)
Equations neg_var {Γ : neg_ctx} {x : ty} : (Γ : t_ctx) ∋ x -> is_neg x :=
  @neg_var ∅       _ (!) ;
  @neg_var (_ ▶ t) _ (top)   := proj2_sig t ;
  @neg_var (_ ▶ _) _ (pop i) := neg_var i .

Equations neg_upgrade {Γ : neg_ctx} {x : ty} (i : (Γ : t_ctx) ∋ x) :
  Γ ∋ exist _ x (neg_var i) :=
  @neg_upgrade (_ ▶ (exist _ _ _)) _ (top)   := top ;
  @neg_upgrade (_ ▶ _)             _ (pop i) := pop (neg_upgrade i) .

(*|
Syntax of terms
^^^^^^^^^^^^^^^

This is the usual well-typed representation of terms: any coq term
``t : term Γ x`` denotes a well-typed and well-scoped term of type ``x``
in context ``Γ``.

As in most other simple type systems, our typing rules match
one-to-one with our syntactic rules. As we're not really interested
(yet?) in writing a typechecker (nor a parser), we don't bother
defining untyped terms and the usual predicate for a typing judgement
as this would just duplicate code.

Additionally, functions on intrinsically typed terms like
substitution, renaming or evaluation carry with them the proof that
they preserve typing: no subject reduction to prove! Our functions
will really be proofs with computational content, which may make them
slightly more complicated, but which can help by restricting what can
be done (no more blind de-bruijn indices manipulation).
|*)
Inductive term : t_ctx -> ty -> Type :=
| Var {Γ a} : Γ ∋ a -> term Γ a
| Lam {Γ a b} : term (Γ ▶ a) b -> term Γ (a → b)
| Rec {Γ a b} : term (Γ ▶ (a → b)%ty ▶ a) b -> term Γ (a → b)
| App {Γ a b} : term Γ (a → b) -> term Γ a -> term Γ b
| Pair {Γ a b} : term Γ a -> term Γ b -> term Γ (a × b)
| PMatch {Γ a b x} : term Γ (a × b) -> term (Γ ▶ a ▶ b) x -> term Γ x
| Inl {Γ a b} : term Γ a -> term Γ (a + b)
| Inr {Γ a b} : term Γ b -> term Γ (a + b)
| SMatch {Γ a b x} : term Γ (a + b) -> term (Γ ▶ a) x -> term (Γ ▶ b) x -> term Γ x
.

(*|
Simultaneous renaming. This is functoriality of term (as presheaves on contexts).
First using an auxiliary that does fused shifting for efficiency.
|*)
Equations t_rename_aux {Γ Δ} (ts : t_ctx) (f : Γ ⊆ Δ) [t]
          : term (Γ +▶ ts) t -> term (Δ +▶ ts) t :=
  t_rename_aux ts f (Var i)        := Var (r_shift_n ts f _ i) ;
  t_rename_aux ts f (Lam u)        := Lam (t_rename_aux (ts ▶ _) f u) ;
  t_rename_aux ts f (Rec u)        := Rec (t_rename_aux (ts ▶ _ ▶ _) f u) ;
  t_rename_aux ts f (App u v)      := App (t_rename_aux ts f u)
                                          (t_rename_aux ts f v) ;
  t_rename_aux ts f (Pair u v)     := Pair (t_rename_aux ts f u)
                                           (t_rename_aux ts f v) ;
  t_rename_aux ts f (PMatch u v)   := PMatch (t_rename_aux ts f u)
                                             (t_rename_aux (ts ▶ _ ▶ _) f v) ;
  t_rename_aux ts f (Inl u)        := Inl (t_rename_aux ts f u) ;
  t_rename_aux ts f (Inr u)        := Inr (t_rename_aux ts f u) ;
  t_rename_aux ts f (SMatch u v w) := SMatch (t_rename_aux ts f u)
                                             (t_rename_aux (ts ▶ _) f v)
                                             (t_rename_aux (ts ▶ _) f w) .

Definition t_rename {Γ Δ} (f : Γ ⊆ Δ) [t] := @t_rename_aux Γ Δ ∅ f t.

Definition t_shift {Γ} [y x] : term Γ x -> term (Γ ▶ y) x :=
  @t_rename _ _ (fun _ => pop) _.

Equations s_shift_n {Γ Δ} (ts : t_ctx) (f : Γ =[ term ]> Δ)
          : (Γ +▶ ts) =[ term ]> (Δ +▶ ts) :=
  s_shift_n ts f _ i with concat_split _ _ i :=
    { | inl j := t_rename (r_concat_l _ _) (f _ j) ;
      | inr j := Var (r_concat_r _ _ _ j) } .

(*|
Simultaneous substitution. This is a skew multiplication, analoguous to the
join of monads, generalized to a skew monoidal structure on presheaves.
|*)
Equations t_subst_aux {Γ Δ} (ts : t_ctx) (f : Γ =[ term ]> Δ) [t]
          : term (Γ +▶ ts) t -> term (Δ +▶ ts) t :=
  t_subst_aux ts f (Var i)       := s_shift_n ts f _ i ;
  t_subst_aux ts f (Lam u)       := Lam (t_subst_aux (ts ▶ _) f u) ;
  t_subst_aux ts f (Rec u)       := Rec (t_subst_aux (ts ▶ _ ▶ _) f u) ;
  t_subst_aux ts f (App u v)     := App (t_subst_aux ts f u) (t_subst_aux ts f v) ;
  t_subst_aux ts f (Pair u v)    := Pair (t_subst_aux ts f u) (t_subst_aux ts f v) ;
  t_subst_aux ts f (PMatch u v)  := PMatch (t_subst_aux ts f u)
                                           (t_subst_aux (ts ▶ _ ▶ _) f v) ;
  t_subst_aux ts f (Inl u)       := Inl (t_subst_aux ts f u) ;
  t_subst_aux ts f (Inr u)       := Inr (t_subst_aux ts f u) ;
  t_subst_aux ts f (SMatch u v w) := SMatch (t_subst_aux ts f u)
                                            (t_subst_aux (ts ▶ _) f v)
                                            (t_subst_aux (ts ▶ _) f w).

Definition t_subst {Γ Δ} (f : Γ =[ term ]> Δ) [t] := @t_subst_aux Γ Δ ∅ f t.

(*|
Substituting the top variable only.
|*)
Definition t_subst1 {Γ a b} (u : term (Γ ▶ a) b) (v : term Γ a) : term Γ b :=
  t_subst (has_case v (@Var _)) u .

Notation "u /ₛ v" := (t_subst1 u v) (at level 50, left associativity).

(*|
CBV evaluation
--------------

Call-by-value reduction fully reduces the arguments to a function call
before substituting them into the function's body. It is eager in the
sense that this may or may not have been needed depending what the
function does with its arguments, yet it did it preemptively. The term
"eager normal form" (ENF) has been introduced by Soren Lassen
when adapting Böhm trees from call-by-name to call-by-value: Lassen
trees caracterize ENF-bisimulation whereas Böhm trees caracterize
strong-NF-bisimulation.

TODO check terms and facts

Eager values
^^^^^^^^^^^^

Eager values are lambda-terms that do not contain any eager-redex. One can note
the general pattern: ``val := pos-intro(val) | neg-intro(term)``.
|*)
Inductive e_val (Γ : t_ctx) : ty -> Type :=
| VVar {x} : Γ ∋ x -> e_val Γ x
| VLam {a b} : term (Γ ▶ a) b -> e_val Γ (a → b)
| VRec {a b} : term (Γ ▶ (a → b)%ty ▶ a) b -> e_val Γ (a → b)
| VPair {a b} : e_val Γ a -> e_val Γ b -> e_val Γ (a × b)
| VInl {a b} : e_val Γ a -> e_val Γ (a + b)
| VInr {a b} : e_val Γ b -> e_val Γ (a + b)
.
(*|
.. coq:: none
|*)
Arguments VVar {Γ x}.
Arguments VLam {Γ a b}.
Arguments VRec {Γ a b}.
Arguments VPair {Γ a b}.
Arguments VInl {Γ a b}.
Arguments VInr {Γ a b}.
Derive Signature for e_val.

(*|
Eager values are trivially a subset of terms.
|*)
Equations t_of_val {Γ x} : e_val Γ x -> term Γ x :=
  t_of_val (VVar i) := Var i ;
  t_of_val (VLam u) := Lam u ;
  t_of_val (VRec u) := Rec u ;
  t_of_val (VPair u v) := Pair (t_of_val u) (t_of_val v) ;
  t_of_val (VInl u) := Inl (t_of_val u) ;
  t_of_val (VInr u) := Inr (t_of_val u) .
Coercion t_of_val : e_val >-> term.

(*|
In an ideal world, values being a subset of terms, we could lift the
renaming action from terms to values. Our definition aren't expressive enough yet
so here's the due.
|*)
Equations v_rename {Γ Δ} (f : forall t, Γ ∋ t -> Δ ∋ t) {t}
          : e_val Γ t -> e_val Δ t :=
  v_rename f (VVar i)    := VVar (f _ i) ;
  v_rename f (VLam u)    := VLam (t_rename (r_shift f) u) ;
  v_rename f (VRec u)    := VRec (t_rename (r_shift2 f) u) ;
  v_rename f (VPair u v) := VPair (v_rename f u) (v_rename f v) ;
  v_rename f (VInl u)    := VInl (v_rename f u) ;
  v_rename f (VInr u)    := VInr (v_rename f u) .
  
(*|

Eager contexts
^^^^^^^^^^^^^^

Term-contexts — not to be confused with typing contexts — are terms
with a single hole, ie extended with a (linear) meta-variable. As
explained by Conor McBride, these one-hole contexts are linked to the
derivative of the signature of terms hence could be generated
automatically from it.

Our contexts are (eager) *evaluation* contexts, that is they caracterize all the
places at which it is possible to do an eager reduction. As such, we can observe
that our contexts don't allow to put the hole below any binder (lambda, rec-lambda,
continuations of match constructs).

Our contexts grow outwards, that is the operator closest to the hole
will be the head-constructor of the context. They are intrinsically-typed as follows:
an element of ``e_ctx Γ x y`` is a term of type ``x`` in context ``Γ`` with a hole
of type ``y`` (and context ``Γ`` too, since it can't cross binders).

This is exactely the type of the call-stack of the CBV evaluator.
|*)
Inductive e_ctx (Γ : t_ctx) (t : ty) : ty -> Type :=
| EHole : e_ctx Γ t t
| EApp_l {a b} : e_ctx Γ t b -> term Γ a -> e_ctx Γ t (a → b)
| EApp_r {a b} : e_ctx Γ t b -> e_val Γ (a → b) -> e_ctx Γ t a
| EPair_l {a b} : e_ctx Γ t (a × b) -> term Γ b -> e_ctx Γ t a
| EPair_r {a b} : e_ctx Γ t (a × b) -> e_val Γ a -> e_ctx Γ t b
| EPMatch {a b x} : e_ctx Γ t x -> term (Γ ▶ a ▶ b) x -> e_ctx Γ t (a × b)
| EInl {a b} : e_ctx Γ t (a + b) -> e_ctx Γ t a
| EInr {a b} : e_ctx Γ t (a + b) -> e_ctx Γ t b
| ESMatch {a b x} : e_ctx Γ t x -> term (Γ ▶ a) x -> term (Γ ▶ b) x -> e_ctx Γ t (a + b)
.
(*|
.. coq:: none
|*)
Arguments EHole {Γ t}.
Arguments EApp_l {Γ t a b}.
Arguments EApp_r {Γ t a b}.
Arguments EPair_l {Γ t a b}.
Arguments EPair_r {Γ t a b}.
Arguments EPMatch {Γ t a b x}.
Arguments EInl {Γ t a b}.
Arguments EInr {Γ t a b}.
Arguments ESMatch {Γ t a b x}.

(*|
Still administrative work..
|*)
Equations e_rename {Γ Δ x y} (f : forall t, Γ ∋ t -> Δ ∋ t)
          : e_ctx Γ y x -> e_ctx Δ y x :=
  e_rename f EHole         := EHole ;
  e_rename f (EApp_r E u)  := EApp_r (e_rename f E) (v_rename f u) ;
  e_rename f (EApp_l E u)  := EApp_l (e_rename f E) (t_rename f u) ;
  e_rename f (EPair_r E u) := EPair_r (e_rename f E) (v_rename f u) ;
  e_rename f (EPair_l E u) := EPair_l (e_rename f E) (t_rename f u) ;
  e_rename f (EPMatch E u) := EPMatch (e_rename f E)
                                      (t_rename (r_shift2 f) u) ;
  e_rename f (EInl E)      := EInl (e_rename f E) ;
  e_rename f (EInr E)      := EInr (e_rename f E) ;
  e_rename f (ESMatch E u v) := ESMatch (e_rename f E)
                                        (t_rename (r_shift f) u)
                                        (t_rename (r_shift f) v) .

(*|
Eager redex decomposition
^^^^^^^^^^^^^^^^^^^^^^^^^

Having case constructs for sum and product types, we have 3 kinds of
beta-redexes. ``e_elim Γ x y`` represents eliminators taking a
``term Γ x`` to a ``term Γ y``.
|*)
Variant e_elim (Γ : t_ctx) : ty -> ty -> Type :=
| RApp {a b} : e_val Γ a -> e_elim Γ (a → b) b
| RPMatch {a b x} : term (Γ ▶ a ▶ b) x -> e_elim Γ (a × b) x
| RSMatch {a b x} : term (Γ ▶ a) x -> term (Γ ▶ b) x -> e_elim Γ (a + b) x
.
(*|
.. coq:: none
|*)
Derive Signature for e_elim.
Arguments RApp {Γ a b}.
Arguments RPMatch {Γ a b x}.
Arguments RSMatch {Γ a b x}.

(*|
Finally "eager term". The most important lemma for defining eager evaluation will
explain how eager terms are in bijection with terms. In plain english, eager terms
are terms where the next eager-redex to evaluate is explicited. In particular,
either there is no such redex and the term is a value, or it can be decomposed as
``E[v r]`` with ``E`` an evaluation context, ``v`` a value and ``r`` an eliminator.
|*)
Variant e_term (Γ : t_ctx) (x : ty) : Type :=
| EVal : e_val Γ x -> e_term Γ x
| ERed {a b} : e_ctx Γ x b -> e_val Γ a -> e_elim Γ a b -> e_term Γ x
.
(*|
.. coq:: none
|*)
Arguments EVal {Γ x}.
Arguments ERed {Γ x a b}.

Module focus_aux.
(*|
Finding the redex
^^^^^^^^^^^^^^^^^

Given an ongoing computation, that is a term in an evaluation context ``E[t]``,
we want to find the next redex in CBV evaluation order.

We do it efficiently with only tail-calls by leveraging our type of
evaluation contexts. The recursion pattern of these tail calls is non-trivial
so we need some helpers to get coq (and coq-equations) to accept our definition.
We do that extrinsically by providing a strictly decreasing measure on arguments
across calls. 

.. coq:: none
|*)
Equations term_size {Γ x} : term Γ x -> nat :=
  term_size (Var _) := S O ;
  term_size (Lam _) := S O ;
  term_size (Rec _) := S O ;
  term_size (App a b) := S (S (term_size a + term_size b)) ;
  term_size (Pair a b) := S (S (S (term_size a + term_size b))) ;
  term_size (PMatch a b) := S (term_size a) ;
  term_size (Inl a) := S (S (term_size a)) ;
  term_size (Inr a) := S (S (term_size a)) ;
  term_size (SMatch a b c) := S (term_size a) .

Equations ctx_size {Γ y x} : e_ctx Γ y x -> nat :=
  ctx_size EHole := O ;
  ctx_size (EApp_l E u) := S (ctx_size E + term_size u) ;
  ctx_size (EApp_r E u) := O ;
  ctx_size (EPair_l E u) := S (S (ctx_size E + term_size u)) ;
  ctx_size (EPair_r E u) := S (ctx_size E) ;
  ctx_size (EPMatch E u) := O ;
  ctx_size (EInl E) := S (ctx_size E) ;
  ctx_size (EInr E) := S (ctx_size E) ;
  ctx_size (ESMatch E u v) := O .

Equations aux_size {Γ x} : term Γ x + e_val Γ x -> nat :=
  aux_size (inl t) := term_size t ;
  aux_size (inr v) := O .

(*|
The following definition should actually be two mutually recursive functions::

     e_focus : e_ctx Γ y x → term Γ x → e_term Γ y 
     e_focus_backtrack : e_ctx Γ y x → e_val Γ x → e_term Γ y

But coq-equations does not seem to allow ``by wf ...`` hints in mutual blocks
so we had to hack it into a single function using a sum.

The idea is that ``e_focus`` will descend into the left-most
unexplored branches, recording its path by growing the evaluation
context. When hitting a value we have to backtrack on the evaluation
context, either finding a suitable redex or descending in another
branch.
|*)
Equations? focus_aux {Γ x y} (E : e_ctx Γ y x) (t : term Γ x + e_val Γ x)
          : e_term Γ y by wf (ctx_size E + aux_size t)%nat lt :=
  focus_aux E (inl (Var i))      := focus_aux E (inr (VVar i)) ;
  focus_aux E (inl (Lam a))      := focus_aux E (inr (VLam a)) ;
  focus_aux E (inl (Rec a))      := focus_aux E (inr (VRec a)) ;
  focus_aux E (inl (App a b))    := focus_aux (EApp_l E b) (inl a) ;
  focus_aux E (inl (Pair a b))   := focus_aux (EPair_l E b) (inl a) ;
  focus_aux E (inl (PMatch a b)) := focus_aux (EPMatch E b) (inl a) ;
  focus_aux E (inl (Inl a))      := focus_aux (EInl E) (inl a) ;
  focus_aux E (inl (Inr a))      := focus_aux (EInr E) (inl a) ;
  focus_aux E (inl (SMatch a b c)) := focus_aux (ESMatch E b c) (inl a) ;

  focus_aux EHole         (inr v) := EVal v ;
  focus_aux (EApp_l E u)  (inr v) := focus_aux (EApp_r E v) (inl u) ;
  focus_aux (EApp_r E u)  (inr v) := ERed E u (RApp v) ;
  focus_aux (EPair_l E u) (inr v) := focus_aux (EPair_r E v) (inl u) ;
  focus_aux (EPair_r E u) (inr v) := focus_aux E (inr (VPair u v)) ;
  focus_aux (EPMatch E b) (inr v) := ERed E v (RPMatch b) ;
  focus_aux (EInl E)      (inr v) := focus_aux E (inr (VInl v)) ;
  focus_aux (EInr E)      (inr v) := focus_aux E (inr (VInr v)) ;
  focus_aux (ESMatch E a b) (inr v) := ERed E v (RSMatch a b) .
all: lia.
Defined.
End focus_aux.
 
(*|
From now on, a lot of functions which would usually be presented as taking a term
as input, will take an ongoing evaluation instead, that is a term ``a`` decomposed
as ``E[b]``. We call such a package a "focused term".
|*)
Variant eval_arg (Γ : t_ctx) (x : ty) : Type :=
| EArg {y} : e_ctx Γ x y -> term Γ y -> eval_arg Γ x.
(*|
.. coq:: none
|*)
Arguments EArg {Γ x y}.

(*||*)
Definition earg_start {Γ x} (u : term Γ x) : eval_arg Γ x := EArg EHole u.

(*|
Efficiently find the first redex in ``E[t]``
|*)
Equations e_focus {Γ x} : eval_arg Γ x -> e_term Γ x :=
  e_focus (EArg E t) := focus_aux.focus_aux E (inl t).

(*|
Eager normal forms
^^^^^^^^^^^^^^^^^^

Repeatedly applying the redex-finding function and then reducing it, we will either
end-up with a value or, as we evaluate open terms, get stuck on a redex whose premise
is a variable. That's exactly what eager-normal-forms are.
|*)
Variant e_nf (Γ : t_ctx) (x : ty) : Type :=
| NVal : e_val Γ x -> e_nf Γ x
| NRed {a b} : e_ctx Γ x b -> Γ ∋ a -> e_elim Γ a b -> e_nf Γ x
.
(*|
.. coq:: none
|*)
Arguments NVal {Γ x}.
Arguments NRed {Γ x a b}.

(*|
The evaluator
^^^^^^^^^^^^^
This next function is the core of our evaluator implementing a single
reduction step, outputing either a term-in-context to continue
evaluation on, or a normal form if the evaluation is done.
|*)
Equations eval_step {Γ x} (t : e_term Γ x) : eval_arg Γ x + e_nf Γ x :=
  eval_step (EVal v)                   := inr (NVal v) ;
  eval_step (ERed E (VVar i) r)        := inr (NRed E i r) ;
  eval_step (ERed E (VRec u) (RApp v)) :=
    inl (EArg E (u /ₛ t_shift (t_of_val v) /ₛ Rec u)) ;
  eval_step (ERed E (VLam u) (RApp v)) :=
    inl (EArg E (u /ₛ t_of_val v)) ;
  eval_step (ERed E (VPair u0 u1) (RPMatch a)) :=
    inl (EArg E (a /ₛ t_shift (t_of_val u1) /ₛ t_of_val u0)) ;
  eval_step (ERed E (VInl u) (RSMatch a b)) :=
    inl (EArg E (a /ₛ t_of_val u)) ;
  eval_step (ERed E (VInr u) (RSMatch a b)) :=
    inl (EArg E (b /ₛ t_of_val u)) .

(*|
And now the evaluator is complete: our iterₐ combinator encoding tail-recursion
ties the knot, repeatedly finding the next redex and reducing it.
|*)
Definition eval_enf {Γ x} : eval_arg Γ x -> computation (e_nf Γ x) :=
  iterₐ (NonDep.ret ∘ eval_step ∘ e_focus).

(*|
For encoding reasons, our dependent-itree machinerie works on indexed
sets ``I → Type`` yet all our types (terms, values, variables, etc) are all of the
form ``t_ctx → ty → Type``. Here we define some uncurried versions. Additionnaly
we constrain contexts to contain only negative types as we would like to work with
*focused* terms that do not contain spurious stuck redexes.
|*)
Definition frame : Type := neg_ctx * ty.
Definition eval_arg' : frame -> Type := uncurry (eval_arg ∘ of_n_ctx).
Definition term' : frame -> Type := uncurry (term ∘ of_n_ctx).
Definition e_nf' : frame -> Type := uncurry (e_nf ∘ of_n_ctx).
Definition earg_start' {i} (u : term' i) : eval_arg' i := EArg EHole u.
Definition e_ctx' : ty -> frame -> Type := fun t e => e_ctx (fst e) (snd e) t.
Definition earg' {t e} : e_ctx' t e -> term (fst e) t -> eval_arg' e := EArg.

Equations lift_frame : neg_ctx -> frame -> frame :=
  lift_frame Γ e := ((Γ +▶ fst e)%ctx , snd e).

(*|
Lassen trees
------------

Normal forms for some notion of reduction induce an equivalence on terms defined
by equality of normal forms. But for eager normal forms, evaluation may get stuck
quite early and this induced equivalence won't be very interesting. What we would
like is to somehow continue executing stuck terms. Enter Lassen trees.

Eager normal forms that are stuck, ie ``E[x v]`` may be seen as an
interaction between an unknown context containing the free variable
``x`` and the term at hand, controlling both ``E`` and ``v``. In this
view, ``x`` is a question, ``v`` is its argument, and ``E`` is the
continuation taking as argument the hypothetic answer. TODO ref on
dialogical view of reduction/evaluation.

Lassen, adapting Böhm trees to CBV settings, proposed to construct a
potentially infinite (coinductive) tree where nodes are eager normal
forms. Hence there are two kinds of nodes:

- Value nodes of some type ``a``, which have one child for each observation
  that can be made on ``a`` (more on that below).
- Stuck redex nodes, which have the same children as a value node,
  applied to the redex argument, and additionally have another child continuing
  the evaluation on ``E[y]`` for ``y`` fresh, specifying how evaluation *would*
  continue if the stuck redex had been reduced to an abstract ``y``.

Lassen trees thus caracterize the full CBV *strategy* on a term, that
is, how it would react in any context. To be more formal, we will want
to prove that bisimulation of lassen trees implies contextual
equivalence of the terms, or, that lassen trees provide a
fully-abstract model of STLC.

Abstract values and observations
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

There are a couple things to precise before going forward: In the
stuck node, why do we continue to evaluate on ``E[y]`` with fresh
``y`` instead of continuing on ``E[v]`` for any acceptable value
``v``? One thing to understand is that these universally quantified
items (fresh variable or value) will appear in the traces of our tree and hence
will be compared for equality in a bisimulation. Thus it is clear that
we do not want values of function types (lambdas) in our traces:
comparing function by syntactic equality is not the observational equality we want.
On the other hand, values of other types (spoiler: all positive types)
are perfectly fine appearing in traces.since their allowed observations are exactly
defined by their syntactic value.

To resolve this we introduce a notion of *abstract value*, which hides
components that have negative types. Note that there is no variable: an abstract
value can (and must) be a *fresh* variable on negative types and a constructor on
positive types.
|*)
Inductive a_val : ty -> Type :=
| AArr {a b} : a_val (a → b)
| APair {a b} : a_val a -> a_val b -> a_val (a × b)
| AInl {a b} : a_val a -> a_val (a + b)
| AInr {a b} : a_val b -> a_val (a + b)
.
(*|
.. coq:: none
|*)
Derive NoConfusion for a_val.
Arguments AArr {a b}.
Arguments APair {a b}.
Arguments AInl {a b}.
Arguments AInr {a b}.

(*|
When continuing evaluation after a redex, we will universally quantify
on an abstract value ``a`` and continue on ``E[t_of_a(a)]`` where ``t_of_a``
turns an abstract value into a term, extending the context with a fresh variable
for everything that has been hiden.
|*)
Equations a_cext {x} : a_val x -> neg_ctx :=
  a_cext (@AArr a b)   := nil ▶ (exist _ (a → b)%ty NArr) ;
  a_cext (APair u v)   := a_cext u +▶ a_cext v ;
  a_cext (AInl u)      := a_cext u ;
  a_cext (AInr u)      := a_cext u .

(*|
.. coq:: none
|*)
Ltac r_fixup :=
  unfold of_n_ctx in *;
  repeat rewrite map_app in *.

Definition r_concat_l' {Γ Δ : neg_ctx} : forall t, of_n_ctx Γ ∋ t -> of_n_ctx (Γ +▶ Δ) ∋ t.
  r_fixup; eapply r_concat_l.
Defined.

Definition r_concat_r' {Γ Δ : neg_ctx} : forall t, of_n_ctx Δ ∋ t -> of_n_ctx (Γ +▶ Δ) ∋ t.
  r_fixup; eapply r_concat_r.
Defined.

(*||*)
Equations t_of_a {x} (u : a_val x) : term (a_cext u) x :=
  t_of_a (AArr)      := Var top ;
  t_of_a (APair u v) := Pair (t_rename r_concat_l' (t_of_a u))
                             (t_rename r_concat_r' (t_of_a v));
  t_of_a (AInl u)    := Inl (t_of_a u) ;
  t_of_a (AInr u)    := Inr (t_of_a u) .

(*|
We will also need to define the set of queries (or observations) that can be made
on a given negative type.
|*)
Equations t_obs : neg_ty -> Type :=
  t_obs (exist _ (a → b)%ty _) := a_val a .

(*|
And how the typing context and goal type change at a given observation.
|*)
Equations t_obs_args (x : neg_ty) : t_obs x -> neg_ctx :=
  t_obs_args (exist _ (a → b)%ty _)   o := a_cext o .

Equations t_obs_goal (x : neg_ty) : t_obs x -> ty :=
  t_obs_goal (exist _ (a → b)%ty _)   o := b .

Definition t_obs_nxt (x : neg_ty) (o : t_obs x) : frame :=
  (t_obs_args x o , t_obs_goal x o).

(*|
.. coq:: none
|*)
Arguments t_obs_args {x} o.
Arguments t_obs_goal {x} o.
Arguments t_obs_nxt {x} o.

(*|
|*)
Equations t_obs_apply {Γ : neg_ctx} {x : neg_ty} (o : t_obs x)
          : term Γ x -> term ((Γ +▶ t_obs_args o) : neg_ctx) (t_obs_goal o) :=
  @t_obs_apply Γ (exist _ (a → b)%ty _)   o t :=
    App (t_rename r_concat_l' t)
        (t_rename r_concat_r' (t_of_a o)).

(*|
Now we explain how to turn a value into an abstract value. It is crucial that the
context is negative and thus every positive value must be a constructor.
|*)
Equations a_of_val {Γ : neg_ctx} x (v : e_val Γ x) : a_val x :=
  a_of_val (_ → _) v           := AArr ;
  a_of_val (_ × _) (VPair u v) := APair (a_of_val _ u) (a_of_val _ v) ;
  a_of_val (_ + _) (VInl u)    := AInl (a_of_val _ u) ;
  a_of_val (_ + _) (VInr u)    := AInr (a_of_val _ u) ;

  a_of_val (Unit)  (VVar i) with neg_var i := { | (!) } ;
  a_of_val (_ × _) (VVar i) with neg_var i := { | (!) } ;
  a_of_val (_ + _) (VVar i) with neg_var i := { | (!) } .
(*|
.. coq:: none
|*)
Arguments a_of_val {Γ x}.

(*|
If we turn a concrete value into an abstract value, for every new variable that we
introduced (``a_cext``) we can get it's original value.
|*)
Equations cext_get {Γ : neg_ctx} x (v : e_val Γ x) {y : neg_ty}
         : a_cext (a_of_val v) ∋ y -> e_val Γ y :=
  cext_get (_ → _) v           top := v ;

  cext_get (_ × _) (VPair u v) j with concat_split _ _ j :=
    { | inl k := cext_get _ u k ;
      | inr k := cext_get _ v k } ;
  cext_get (_ + _) (VInl u) j := cext_get _ u j ;
  cext_get (_ + _) (VInr v) j := cext_get _ v j ;

  cext_get Unit    (VVar i) _ with neg_var i := { | (!) } ;
  cext_get (_ × _) (VVar i) _ with neg_var i := { | (!) } ;
  cext_get (_ + _) (VVar i) _ with neg_var i := { | (!) } .
(*|
.. coq:: none
|*)
Arguments cext_get {Γ} x v {y} i.

(*|
We end with 3 functions that will enable to treat ``e_elim`` and ``t_obs`` as
opaque in the OGS development. They respectively construct an observation and
explain how it is eliminated.
|*)
Equations o_of_elim {Γ : neg_ctx} x {y} (i : (Γ : t_ctx) ∋ x)
  : e_elim Γ x y -> t_obs (exist _ x (neg_var i)) :=
  o_of_elim _ i e with neg_var i := {
      o_of_elim (_ → _) i (RApp v) _ := _
  } .
Obligation 1. exact (a_of_val v). Defined.
Arguments o_of_elim {Γ x y} i e.

Definition o_of_elim_eq {Γ : neg_ctx} {x y} (i : (Γ : t_ctx) ∋ x)
          (e : e_elim Γ x y) : t_obs_goal (o_of_elim i e) = y.
  cbv [o_of_elim]; pose (u := neg_var i); fold u.
  destruct x; try dependent elimination u.
  dependent elimination e.
  reflexivity.
Defined.

Definition o_args_get {Γ : neg_ctx} {x y z} (i : (Γ : t_ctx) ∋ x)
          (e : e_elim Γ x y) (j : t_obs_args (o_of_elim i e) ∋ z) : e_val Γ z.
  cbv [o_of_elim] in j; pose (u := neg_var i); fold u in j.
  destruct x; try dependent elimination u.
  dependent elimination e.
  exact (cext_get _ e j).
Defined.
