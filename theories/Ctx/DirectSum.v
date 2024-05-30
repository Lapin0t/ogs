(*|
Direct sum of context structure
===============================

A random calculus you may find in the wild will most likely not fit into the rigid
well-scoped and well-typed format with concrete contexts and DeBruijn indices. Sometimes
this is because the designers have found useful to formalize this calculus with *two*
contexts, storing two kinds of variables for different use. The usual trick is to change
the set of types to a coproduct and store everything in one big context, eg using
``ctx (S + T)`` instead of ``ctx S × ctx T``. This does work, but it might make some things
more cumbersome.

Using our abstraction over context structures, we can readily express the case of two
separate contexts: the direct sum.

.. coq:: none
|*)
From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.
From OGS.Ctx Require Import Abstract Family.

Reserved Notation "C ⊕ D" (at level 40).
#[local] Open Scope ctx_scope.

(*|
Let's assume we have two contexts structures.
|*)
Section with_param.
  Context {T1 C1 : Type} {CC1 : context T1 C1} {CL1 : context_laws T1 C1}.
  Context {T2 C2 : Type} {CC2 : context T2 C2} {CL2 : context_laws T2 C2}.
(*|
A pair of contexts is just that.
|*)
  Definition dsum := C1 × C2.
(*|
Empty context and concatenation are without suprise.
|*)
  Definition c_emp2 : dsum := (∅ , ∅) .

  Definition c_cat2 (Γ12 : dsum) (Δ12 : dsum) : dsum
    := (fst Γ12 +▶ fst Δ12 , snd Γ12 +▶ snd Δ12).
(*|
Now the interesting part: variables! The new set of types is either a type from the
first context or from the second: ``T₁ + T₂``. We then compute the set of variables
by case splitting on this coproduct: either a variable from the left or from the right.
|*)
  Equations c_var2 : dsum -> T1 + T2 -> Type :=
   c_var2 Γ12 (inl t1) := fst Γ12 ∋ t1 ;
   c_var2 Γ12 (inr t2) := snd Γ12 ∋ t2 .
(*|
This instanciates the relevant part.
|*)
  #[global] Instance direct_sum_context : context (T1 + T2) dsum :=
    {| c_emp := c_emp2 ; c_cat := c_cat2 ; c_var := c_var2 |}.
(*|
And the laws are straightforward.
|*)
  #[global] Instance direct_sum_cat_wkn : context_cat_wkn (T1 + T2) dsum .
  Proof.
    split.
    - intros ?? [ t1 | t2 ] i; cbn; now apply r_cat_l.
    - intros ?? [ t1 | t2 ] i; cbn; now apply r_cat_r.
  Defined.

  #[global] Instance direct_sum_laws : context_laws (T1 + T2) dsum .
  Proof.
    esplit; cbn.
    - intros [] i; cbn in i; now destruct (c_view_emp i).
    - intros ?? [] i; cbn in i; destruct (c_view_cat i).
      now refine (Vcat_l _).
      now refine (Vcat_r _).
      now refine (Vcat_l _).
      now refine (Vcat_r _).
    - intros ?? []; cbn; intros ?? H; now apply (r_cat_l_inj _ _ H).
    - intros ?? []; cbn; intros ?? H; now apply (r_cat_r_inj _ _ H).
    - intros ?? []; cbn; intros ?? H; now apply (r_cat_disj _ _ H).
  Qed.
End with_param.
(*|
Let's have a notation for this.
|*)
#[global] Arguments dsum C1 C2 : clear implicits.
#[global] Notation "C ⊕ D" := (dsum C D).
