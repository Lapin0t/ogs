(*|
============================
Simply-typed lambda-calculus
============================


.. coq:: none
|*)
Set Primitive Projections.

From Coq Require Import Logic.
From Coq.Logic Require Import StrictProp.
From Coq Require Import Program.Equality.
Import EqNotations.
Require Import Psatz.

From ExtLib.Data Require Import List.

From OGS Require Import Utils.
From OGS.ITree Require Import Cat Event Dual ITree Rec Angelic Eq.
From OGS.STLC Require Import Ctx.

From Equations Require Import Equations.
Set Equations Transparent.

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

Equations is_neg : ty -> SProp :=
  is_neg (a → b)%ty := sUnit ;
  is_neg _          := sEmpty .

Definition neg_ty : Type := subset is_neg.
Definition neg_coe : neg_ty -> ty := sub_elt.
Coercion neg_coe : neg_ty >-> ty.

Definition neg_ctx : Type := subset (fun Γ : t_ctx => forall k, Γ ∋ k -> is_neg k).
Definition neg_c_coe : neg_ctx -> t_ctx := sub_elt.
Coercion neg_c_coe : neg_ctx >-> t_ctx.

Bind Scope ctx_scope with neg_ctx.
Bind Scope ctx_scope with ctx.

Definition app_neg (Γ : neg_ctx) (x : neg_ty) : neg_ctx.
  refine ({| sub_elt := (Γ.(sub_elt) ▶ x.(sub_elt))%ctx ;
             sub_prf := fun k i => _ |}).
  remember (sub_elt Γ ▶ sub_elt x)%ctx.
  destruct i; injection Heql; intros Ha Hb.
  rewrite Hb; exact (sub_prf x).
  rewrite Ha in i; exact (sub_prf Γ x0 i).
Defined.

Definition concat_neg (Γ Δ : neg_ctx) : neg_ctx.
  refine ({| sub_elt := (Γ.(sub_elt) +▶ Δ.(sub_elt))%ctx ;
             sub_prf := fun k i => _ |}).
  destruct (concat_split _ _ i).
  exact (Γ.(sub_prf) k h).
  exact (Δ.(sub_prf) k h).
  Defined.

Definition nil' : neg_ctx.
  refine ({| sub_elt := ∅%ctx ; sub_prf := fun k i => _ |}).
  remember ∅%ctx; destruct i; discriminate Heql.
  Defined.

Definition arr_neg (a b : ty) : neg_ty :=
  {| sub_elt := (a → b)%ty ; sub_prf := stt |}.

Notation "Γ +▶' Δ" := (concat_neg Γ Δ) (at level 40).
Notation "Γ ▶' x" := (app_neg Γ x) (at level 40).
Notation "∅'" := nil'.
Notation "a →' b" := (arr_neg a b) (at level 40).

Bind Scope ctx_scope with neg_ctx.
Bind Scope ctx_scope with ctx.

Definition neg_var {Γ : neg_ctx} {x} : (Γ : t_ctx) ∋ x -> is_neg x := Γ.(sub_prf) x.

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

Equations v_shift_n {Γ Δ} (ts : t_ctx) (f : Γ =[ e_val ]> Δ)
          : (Γ +▶ ts) =[ e_val ]> (Δ +▶ ts) :=
  v_shift_n ts f _ i with concat_split _ _ i :=
    { | inl j := v_rename (r_concat_l _ _) (f _ j) ;
      | inr j := VVar (r_concat_r _ _ _ j) } .

Definition s_t_of_val {Γ Δ} : Γ =[ e_val ]> Δ -> Γ =[ term ]> Δ :=
  fun f _ i => t_of_val (f _ i).
  

Equations v_subst_aux {Γ Δ} (ts : t_ctx) (f : Γ =[ e_val ]> Δ) [t]
          : e_val (Γ +▶ ts) t -> e_val (Δ +▶ ts) t :=
  v_subst_aux ts f (VVar i) := v_shift_n ts f _ i ;
  v_subst_aux ts f (VLam u) := VLam (t_subst_aux (ts ▶ _) (s_t_of_val f) u) ;
  v_subst_aux ts f (VRec u) := VRec (t_subst_aux (ts ▶ _ ▶ _) (s_t_of_val f) u) ;
  v_subst_aux ts f (VPair u v) := VPair (v_subst_aux ts f u) (v_subst_aux ts f v) ;
  v_subst_aux ts f (VInl u) := VInl (v_subst_aux ts f u) ;
  v_subst_aux ts f (VInr u) := VInr (v_subst_aux ts f u) .
  
Definition v_subst {Γ Δ} (f : Γ =[ e_val ]> Δ) [t] := @v_subst_aux Γ Δ ∅ f t.

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

Equations e_comp {Γ x y z} : e_ctx Γ z y -> e_ctx Γ y x -> e_ctx Γ z x :=
  e_comp E EHole           := E ;
  e_comp E (EApp_r F u)    := EApp_r (e_comp E F) u ;
  e_comp E (EApp_l F u)    := EApp_l (e_comp E F) u ;
  e_comp E (EPair_r F u)   := EPair_r (e_comp E F) u ;
  e_comp E (EPair_l F u)   := EPair_l (e_comp E F) u ;
  e_comp E (EPMatch F u)   := EPMatch (e_comp E F) u ;
  e_comp E (EInl F)        := EInl (e_comp E F) ;
  e_comp E (EInr F)        := EInr (e_comp E F) ;
  e_comp E (ESMatch F u v) := ESMatch (e_comp E F) u v .
  
Equations e_subst {Γ Δ} (f : Γ =[ e_val ]> Δ) [y t]
  : e_ctx Γ y t -> e_ctx Δ y t :=
  e_subst f EHole           := EHole ;
  e_subst f (EApp_r E u)    := EApp_r (e_subst f E) (v_subst f u) ;
  e_subst f (EApp_l E u)    := EApp_l (e_subst f E) (t_subst (s_t_of_val f) u) ;
  e_subst f (EPair_r E u)   := EPair_r (e_subst f E) (v_subst f u) ;
  e_subst f (EPair_l E u)   := EPair_l (e_subst f E) (t_subst (s_t_of_val f) u) ;
  e_subst f (EPMatch E u)   :=
    EPMatch (e_subst f E) (t_subst_aux (∅ ▶ _ ▶ _) (s_t_of_val f) u) ;
  e_subst f (EInl E)        := EInl (e_subst f E) ;
  e_subst f (EInr E)        := EInr (e_subst f E) ;
  e_subst f (ESMatch E u v) :=
    ESMatch (e_subst f E)
            (t_subst_aux (∅ ▶ _) (s_t_of_val f) u)
            (t_subst_aux (∅ ▶ _) (s_t_of_val f) v).

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

Variant e_zip (A : t_ctx -> ty -> Type) (Γ : t_ctx) (x : ty) :=
| EZ {y} (E : e_ctx Γ x y) : A Γ y -> e_zip A Γ x
.
Arguments EZ {A Γ x y} E a.

Definition ez_init {A : t_ctx -> ty -> Type} {Γ x} (a : A Γ x) : e_zip A Γ x :=
  EZ EHole a.

Definition zterm := e_zip term.

Definition focus_arg (Γ : t_ctx) (x : ty) : Type :=
  e_zip term Γ x + e_zip e_val Γ x.

(*|
This function terminates, but it's elimination order is not trivial
(it's not simply structural) and we won't use it outside of itree context so
we just wrap it into an ``itree ∅ₑ`` to get general recursion and make coq happy.
|*)
Equations focus_aux {Γ x} : focus_arg Γ x -> (focus_arg Γ x + e_term Γ x) :=
  focus_aux (inl (EZ E (Var i)))        := inl (inr (EZ E (VVar i))) ;
  focus_aux (inl (EZ E (Lam m)))        := inl (inr (EZ E (VLam m))) ;
  focus_aux (inl (EZ E (Rec m)))        := inl (inr (EZ E (VRec m))) ;
  focus_aux (inl (EZ E (App m n)))      := inl (inl (EZ (EApp_l E n) m)) ;
  focus_aux (inl (EZ E (Pair m n)))     := inl (inl (EZ (EPair_l E n) m)) ;
  focus_aux (inl (EZ E (PMatch m n)))   := inl (inl (EZ (EPMatch E n) m)) ;
  focus_aux (inl (EZ E (Inl m)))        := inl (inl (EZ (EInl E) m)) ;
  focus_aux (inl (EZ E (Inr m)))        := inl (inl (EZ (EInr E) m)) ;
  focus_aux (inl (EZ E (SMatch m n p))) := inl (inl (EZ (ESMatch E n p) m)) ;

  focus_aux (inr (EZ EHole           v)) := inr (EVal v) ;
  focus_aux (inr (EZ (EApp_l E m)    v)) := inl (inl (EZ (EApp_r E v) m)) ;
  focus_aux (inr (EZ (EApp_r E w)    v)) := inr (ERed E w (RApp v)) ;
  focus_aux (inr (EZ (EPair_l E m)   v)) := inl (inl (EZ (EPair_r E v) m)) ;
  focus_aux (inr (EZ (EPair_r E w)   v)) := inl (inr (EZ E (VPair w v))) ;
  focus_aux (inr (EZ (EPMatch E m)   v)) := inr (ERed E v (RPMatch m)) ;
  focus_aux (inr (EZ (EInl E)        v)) := inl (inr (EZ E (VInl v))) ;
  focus_aux (inr (EZ (EInr E)        v)) := inl (inr (EZ E (VInr v))) ;
  focus_aux (inr (EZ (ESMatch E m n) v)) := inr (ERed E v (RSMatch m n)) .

Definition focus {Γ x} : zterm Γ x -> computation (e_term Γ x) :=
  iterₐ (retₐ ∘ focus_aux) ∘ inl.

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
Equations eval_step {Γ x} (t : e_term Γ x) : zterm Γ x + e_nf Γ x :=
  eval_step (EVal v)                   := inr (NVal v) ;
  eval_step (ERed E (VVar i) r)        := inr (NRed E i r) ;
  eval_step (ERed E (VRec u) (RApp v)) :=
    inl (EZ E (u /ₛ t_shift (t_of_val v) /ₛ Rec u)) ;
  eval_step (ERed E (VLam u) (RApp v)) :=
    inl (EZ E (u /ₛ t_of_val v)) ;
  eval_step (ERed E (VPair u0 u1) (RPMatch a)) :=
    inl (EZ E (a /ₛ t_shift (t_of_val u1) /ₛ t_of_val u0)) ;
  eval_step (ERed E (VInl u) (RSMatch a b)) :=
    inl (EZ E (a /ₛ t_of_val u)) ;
  eval_step (ERed E (VInr u) (RSMatch a b)) :=
    inl (EZ E (b /ₛ t_of_val u)) .

(*|
And now the evaluator is complete: our iterₐ combinator encoding tail-recursion
ties the knot, repeatedly finding the next redex and reducing it.
|*)
Definition eval_enf {Γ x} : zterm Γ x -> computation (e_nf Γ x) :=
  iterₐ (focus !$> eval_step).

(*|
For encoding reasons, our dependent-itree machinerie works on indexed
sets ``I → Type`` yet all our types (terms, values, variables, etc) are all of the
form ``t_ctx → ty → Type``. Here we define some uncurried versions. Additionnaly
we constrain contexts to contain only negative types as we would like to work with
*focused* terms that do not contain spurious stuck redexes.
|*)
Definition frame : Type := neg_ctx * ty.
Definition zterm' : frame -> Type := uncurry (zterm ∘ neg_c_coe).
Definition term' : frame -> Type := uncurry (term ∘ neg_c_coe).
Definition e_nf' : frame -> Type := uncurry (e_nf ∘ neg_c_coe).
Definition ez_init' {i} (u : term' i) : zterm' i := EZ EHole u.
Definition e_ctx' : ty -> frame -> Type := fun t e => e_ctx (fst e) (snd e) t.
Definition earg' {t e} : e_ctx' t e -> term (fst e) t -> zterm' e := EZ.

Equations lift_frame : neg_ctx -> frame -> frame :=
  lift_frame Γ e := ((Γ +▶' fst e)%ctx , snd e).

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
  a_cext (@AArr a b)   := ∅' ▶' (a →' b) ;
  a_cext (APair u v)   := a_cext u +▶' a_cext v ;
  a_cext (AInl u)      := a_cext u ;
  a_cext (AInr u)      := a_cext u .

Equations t_of_a {x} (u : a_val x) : term (a_cext u) x :=
  t_of_a (AArr)      := Var top ;
  t_of_a (APair u v) := Pair (t_rename (r_concat_l _ _) (t_of_a u))
                             (t_rename (r_concat_r _ _) (t_of_a v));
  t_of_a (AInl u)    := Inl (t_of_a u) ;
  t_of_a (AInr u)    := Inr (t_of_a u) .

(*|
We will also need to define the set of queries (or observations) that can be made
on a given negative type.
|*)
Equations t_obs_aux (t : ty) : is_neg t -> Type :=
  t_obs_aux (a → b)%ty _ := a_val a .

Equations t_obs : neg_ty -> Type :=
  t_obs n := t_obs_aux n.(sub_elt) n.(sub_prf).

(*|
And how the typing context and goal type change at a given observation.
|*)
Equations t_obs_args_aux (t : ty) (p : is_neg t) : t_obs_aux t p -> neg_ctx :=
  t_obs_args_aux (a → b)%ty _ o := a_cext o .

Equations t_obs_goal_aux (t : ty) (p : is_neg t) : t_obs_aux t p -> ty :=
  t_obs_goal_aux (a → b)%ty _ o := b .

Definition t_obs_args (t : neg_ty) : t_obs t -> neg_ctx :=
  t_obs_args_aux t.(sub_elt) t.(sub_prf) . 

Definition t_obs_goal (t : neg_ty) : t_obs t -> ty :=
  t_obs_goal_aux t.(sub_elt) t.(sub_prf) . 

Definition t_obs_nxt (t : neg_ty) (o : t_obs t) : frame :=
  (t_obs_args t o , t_obs_goal t o).

(*|
.. coq:: none
|*)
Arguments t_obs_args {t} o.
Arguments t_obs_goal {t} o.
Arguments t_obs_nxt {t} o.

(*|
|*)
Equations t_obs_apply_aux {Γ : neg_ctx} (x : ty) (p : is_neg x) (o : t_obs_aux x p)
          : term Γ x -> term ((Γ +▶' t_obs_args_aux x p o)) (t_obs_goal_aux x p o) :=
  t_obs_apply_aux (a → b)%ty _ o t :=
    App (t_rename (r_concat_l _ _) t)
        (t_rename (r_concat_r _ _) (t_of_a o)).

Definition t_obs_apply {Γ : neg_ctx} {x : neg_ty} (o : t_obs x)
  : term Γ x -> term ((Γ +▶' t_obs_args o)) (t_obs_goal o) :=
  t_obs_apply_aux x.(sub_elt) x.(sub_prf) o.

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
Definition cext_get {Γ : neg_ctx} (x : ty) (v : e_val Γ x) {y : neg_ty}
         : (a_cext (a_of_val v) : t_ctx) ∋ y -> e_val Γ y.
  induction x.
  - dependent elimination v.
    + destruct (neg_var h).
  - dependent elimination v.
    + destruct (neg_var h).
    + intro i. destruct (concat_split _ _ i).
      * exact (IHx1 e h).
      * exact (IHx2 e0 h).
  - intro i.
    cbv [a_of_val] in i. cbn in i.
    remember (∅ ▶ (x1 → x2)%ty)%ctx.
    destruct i; injection Heql; intros Ha Hb.
    rewrite Hb; exact v.
    rewrite Ha in i; dependent elimination i.
  - dependent elimination v.
    + destruct (neg_var h).
    + exact (IHx1 e1).
    + exact (IHx2 e2).
Defined.
      
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
  : e_elim Γ x y -> t_obs (Build_subset _ _ x (neg_var i)) :=
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
          (e : e_elim Γ x y) (j : (t_obs_args (o_of_elim i e) : t_ctx) ∋ z) : e_val Γ z.
  cbv [o_of_elim o_of_elim_clause_1] in j. pose (u := neg_var i); fold u in j.
  destruct x; try dependent elimination u.
  dependent elimination e.
  cbn in j; cbv [o_of_elim_obligations_obligation_1] in j.
  exact (cext_get _ e (j : _ ∋ neg_coe {| sub_elt := z ; sub_prf := neg_var j |})).
Defined.
