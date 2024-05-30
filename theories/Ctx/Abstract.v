(*|
Abstract contexts structures
============================

Our whole development utilizes well-scoped and well-typed terms. In this style, the most
common binder representation is by using lists as contexts and well-typed DeBruijn indices
as variables. This is nice and good, but sometimes we would rather have had another,
isomorphic, representation. Indeed in an intensional type theory like Coq, sometimes
crossing an isomorphism is pretty painful.

As such, we here define what it means for an alternate definition of contexts to
"behave like lists and DeBruijn indices".

This is a very natural extension to the theory of substitution by Marcelo Fiore and
Dimitri Szamozvancev, and in fact a variant of the "Nameless, Painless" approach by
Nicolas Pouillard.

Theory
------

Categorically, it very simple. Contexts are represented by a set ``C``, a distinguished
element ``∅`` and a binary operation ``- +▶ -``. Additionally it has a map representing
variable ``𝐯 : C → 𝐀`` where ``𝐀`` is a sufficiently well-behaved category, typically a
presheaf category. We then ask that

- ``𝐯 ∅ ≈ ⊥``, where ``⊥`` is the initial object in ``𝐀`` and
- ``𝐯 (Γ +▶ Δ) ≈ 𝐯 Γ + 𝐯 Δ`` where `+` is the coproduct in ``𝐀``.

Our category of contexts is basically the image of ``𝐯``, which has the structure of a
commutative monoid. Then, given a family ``X : C → 𝐀``, it is easy to define
assignments as::

  Γ =[X]> Δ ≔ 𝐀[ 𝐯 Γ , X Δ ]

And renamings as::

  Γ ⊆ Δ ≔ Γ =[ 𝐯 ]> Δ
        ≔ 𝐀[ 𝐯 Γ , 𝐯 Δ ]

Assuming ``𝐀`` is (co-)powered over ``Set``, the substitution tensor product and substitution
internal hom in ``C → 𝐀`` are given by:: 

  ( X ⊗ Y ) Γ ≔ ∫^Δ  X Δ × (Δ =[ Y ]> Γ)
  ⟦ X , Y ⟧ Γ ≔ ∫_Δ  (Γ =[ X ]> Δ) → Y Δ

More generally, given a category ``𝐁`` (co-)powered over ``Set`` we can define the the
following functors, generalizing the substitution tensor and hom to heretogeneous
settings::

  ( - ⊗ - ) : (C → 𝐁) → (C → 𝐀) → (C → 𝐁)
  ( X ⊗ Y ) Γ ≔ ∫^Δ  X Δ × (Δ =[ Y ]> Γ)

  ⟦ - , - ⟧ : (C → 𝐀) → (C → 𝐁) → (C → 𝐁)
  ⟦ X , Y ⟧ Γ ≔ ∫_Δ  (Γ =[ X ]> Δ) → Y Δ

Concretely
----------  

We here apply the above theory to the case where ``𝐀`` is the family category ``T → Set``
for some set ``T``. Taking ``T`` to the set of types of some object language, families
``C → 𝐀``, ie ``C → T → Set``, model nicely well-scoped and well-typed families. To
capture non-typed syntactic categories, indexed only by a scope, we develop the special
case where ``𝐁`` is just ``Set``.

We then instanciate this abstract structure with the usual lists and DeBruijn indices,
but also with two useful instances: the direct sum, where the notion of variables ``𝐯``
is the pointwise coproduct and the subset, where the notion of variables is preserved.

In further work we wish to tacle this in more generality, notable treating the case for
the idiomatic presentation of well-scoped untyped syntax where ``𝐀`` is ``Set``, ``C``
is ``ℕ`` and ``𝐯`` is ``Fin``. Currently, we do treat untyped syntax, but using the
non-idiomatic "unityped" presentation.

.. coq:: none
|*)
From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.

#[global] Declare Scope ctx_scope.
#[global] Delimit Scope ctx_scope with ctx.
#[local] Open Scope ctx_scope.

Reserved Notation "∅".
Reserved Notation "Γ +▶ Δ" (at level 50, left associativity).
Reserved Notation "Γ ∋ x" (at level 60).
Reserved Notation "[ x ]".
(*|
The first part of the context structure: the distinguished empty context, the binary
concatenation and the family of variables.
|*)
Class context (T C : Type) := {
  c_emp : C ;
  c_cat : C -> C -> C ;
  c_var : C -> T -> Type ;
}.
#[global] Notation "∅" := c_emp : ctx_scope.
#[global] Notation "Γ +▶ Δ" := (c_cat Γ Δ) : ctx_scope.
#[global] Notation "Γ ∋ t" := (c_var Γ%ctx t).
(*|
Next we need to formalize the isomorphisms stating that variables map the empty context
to the initial family and the concatenation to the coproduct family. To do this we will
not write the usual forward map and backward map that compose to the identity, but we
will rather formalize injections with inhabited fibers. The reason for this equivalent
presentation is that it will ease dependent pattern matching by providing the isomorphisms
as "views" (see "The view from the left" by Conor McBride).

First lets define the two injection maps.
|*)
Class context_cat_wkn (T C : Type) {CC : context T C} := {
  r_cat_l {Γ Δ} [t] : Γ ∋ t -> Γ +▶ Δ ∋ t ;
  r_cat_r {Γ Δ} [t] : Δ ∋ t -> Γ +▶ Δ ∋ t ;
}.
(*|
Then, assuming such a structure, we define two inductive families characterizing the
fibers.
|*)
Section with_param.
  Context `{C : context_cat_wkn X T}.

  Variant c_emp_view t : ∅ ∋ t -> Type := .
(*| .. coq:: none |*)
  Derive NoConfusion NoConfusionHom for c_emp_view.
(*||*)
  Variant c_cat_view Γ Δ t : Γ +▶ Δ ∋ t -> Type :=
  | Vcat_l (i : Γ ∋ t) : c_cat_view Γ Δ t (r_cat_l i)
  | Vcat_r (j : Δ ∋ t) : c_cat_view Γ Δ t (r_cat_r j)
  .
(*| .. coq:: none |*)
  #[global] Arguments Vcat_l {Γ Δ t} i.
  #[global] Arguments Vcat_r {Γ Δ t} j.
  Derive NoConfusion for c_cat_view.
(*||*)
End with_param.
(*|
Finally we give the rest of the laws: functions witnessing the inhabitedness of the fibers
and the injectivity of the two injection maps. This last statement is split into 3 as we
have separated the embedding for coproducts into two separate maps.
|*)
Class context_laws T C {CC : context T C} := {
  c_var_cat :: context_cat_wkn T C ;
  c_view_emp {t} i : c_emp_view t i ;
  c_view_cat {Γ Δ t} i : c_cat_view Γ Δ t i ;
  r_cat_l_inj {Γ Δ t} : injective (@r_cat_l _ _ _ _ Γ Δ t) ;
  r_cat_r_inj {Γ Δ t} : injective (@r_cat_r _ _ _ _ Γ Δ t) ;
  r_cat_disj {Γ Δ t} (i : Γ ∋ t) (j : Δ ∋ t) : ¬ (r_cat_l i = r_cat_r j) ;
} .
