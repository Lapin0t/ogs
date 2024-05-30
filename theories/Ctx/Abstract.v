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

Categorically, it very simple. Contexts are represented by a set `C`, a distinguished
element `∅` and a binary operation `- +▶ -`. Additionally it has a map representing
variable `𝓋 : C → 𝒜` where `𝒜` is a sufficiently well-behaved category, typically a
presheaf category. We then ask that

- `𝓋 ∅ ≈ ⊥`, where `⊥` is the initial object in `𝒜` and
- `𝓋 (Γ +▶ Δ) ≈ 𝓋 Γ + 𝓋 Δ` where `+` is the coproduct in `𝒜`.

Our category of contexts is basically the image of `𝓋`, which has the structure of a
commutative monoid. Then, given a family `𝒳 : C → 𝒜`, it is easy to define
assignments as::

  Γ =[𝒳]> Δ ≔ 𝒜[ 𝓋 Γ , 𝒳 Δ ]

And renamings as::

  Γ ⊆ Δ ≔ Γ =[ 𝓋 ]> Δ
        ≔ 𝒜[ 𝓋 Γ , 𝓋 Δ ]

Assuming `𝒜` is (co-)powered over `Set`, the substitution tensor product and substitution
internal hom in `C → 𝒜` are given by:: 

  ( 𝒳 ⊗ 𝒴 ) Γ ≔ ∫^Δ  𝒳 Δ × (Δ =[ 𝒴 ]> Γ)
  ⟦ 𝒳 , 𝒴 ⟧ Γ ≔ ∫_Δ  (Γ =[ 𝒳 ]> Δ) → 𝒴 Δ

More generally, given a category `ℬ` (co-)powered over `Set` we can define the the
following functors, generalizing the substitution tensor and hom to heretogeneous
settings::

  ( - ⊗ - ) : (C → ℬ) → (C → 𝒜) → (C → ℬ)
  ( 𝒳 ⊗ 𝒴 ) Γ ≔ ∫^Δ  𝒳 Δ × (Δ =[ 𝒴 ]> Γ)

  ⟦ - , - ⟧ : (C → 𝒜) → (C → ℬ) → (C → ℬ)
  ⟦ 𝒳 , 𝒴 ⟧ Γ ≔ ∫_Δ  (Γ =[ 𝒳 ]> Δ) → 𝒴 Δ

Concretely
----------  

We here apply the above theory to the case where `𝓐` is the family category `T → Set` for
some set `T`. Taking `T` to the set of types of some object language, families `C → 𝒜`, ie
`C → T → Set`, model nicely well-scoped and well-typed families. To capture non-typed
syntactic categories, indexed only by a scope, we develop the special case where `ℬ` is
just `Set`.

We then instanciate this abstract structure with the usual lists and DeBruijn indices,
but also with two useful instances: the direct sum, where the notion of variables `𝓋` is
the pointwise coproduct and the subset, where the notion of variables is preserved.

In further work we wish to tacle this in more generality, notable treating the case for
the idiomatic presentation of well-scoped untyped syntax where `𝒜` is `Set`, `C` is `ℕ`
and `𝓋` is `Fin`. Currently, we do treat untyped syntax, but using the non-idiomatic
"unityped" presentation.

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
