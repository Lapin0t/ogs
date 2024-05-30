(*|
Sub-context structure
=====================

As motivated in `Ctx/DirectSum.v <DirectSum.html>`_, we sometimes have exotic calculi
which need specific kinds of contexts. Another such case is when there is a particular
subset of types, represented by a predicate, and we wish to talk about contexts containing
only these kind of types. Once again, we *could* do this using concrete lists, by taking
the set of types to be elements of the predicate ``P : T → SProp``: ``ctx (sigS P)``. The
problem is once again that DeBruijn indices on this structure is not the right notion of
variables. The set of contexts of some subset of the types is a subset of the set of contexts
over that type! In other words, we should rather take ``sigS (ctx T) (allS P)``. As such the
notion of variable should be the same.

.. coq:: none
|*)
From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.
From OGS.Ctx Require Import Abstract Family.

#[local] Open Scope ctx_scope.

Reserved Notation "∅ₛ".
Reserved Notation "Γ ▶ₛ x" (at level 40).
Reserved Notation "Γ +▶ₛ Δ" (at level 40).
(*|
We assume given a notion of context and a strict predicate on types.
|*)
Section with_param.
  Context {T C} {CC : context T C} {CL : context_laws T C} {P : T -> SProp}.
(*|
We define the strict predicate on context stating that all elements verify ``P``.
|*)
  Definition allS (Γ : C) : SProp := forall x, Γ ∋ x -> P x.
  Definition ctxS : Type := sigS allS.
  Definition coe_ctxS : ctxS -> C := sub_elt.
(*|
A variable in the refined context is just a variable in the underlying context.
|*)
  Definition varS (Γ : ctxS) (x : T) := Γ.(sub_elt) ∋ x.
(*|
Nil and concatenation respect ``allS``.
|*)
  Program Definition nilS : ctxS := {| sub_elt := ∅ |}.
  Next Obligation. intros ? i; destruct (c_view_emp i). Qed.

  Program Definition catS (Γ Δ : ctxS) : ctxS :=
    {| sub_elt := Γ.(sub_elt) +▶ Δ.(sub_elt) |}.
  Next Obligation.
    intros ? i; destruct (c_view_cat i).
    now apply Γ.(sub_prf).
    now apply Δ.(sub_prf).
  Qed.
(*|
We now construct the instance.
|*)
  #[global] Instance subset_context : context T ctxS :=
    {| c_emp := nilS ;
       c_cat := catS ;
       c_var := varS |}.

  #[global] Instance subset_context_cat_wkn : context_cat_wkn T ctxS :=
    {| r_cat_l Γ Δ t i := @r_cat_l T C _ _ Γ.(sub_elt) Δ.(sub_elt) t i ;
       r_cat_r Γ Δ t i := @r_cat_r T C _ _ Γ.(sub_elt) Δ.(sub_elt) t i |} .

  #[global] Instance subset_context_laws : context_laws T ctxS.
  Proof.
    unshelve esplit; cbn.
    - intros ? i; destruct (c_view_emp i).
    - intros ??? i; destruct (c_view_cat i).
      refine (Vcat_l _).
      refine (Vcat_r _).
    - intros ????? H; exact (r_cat_l_inj _ _ H).
    - intros ????? H; exact (r_cat_r_inj _ _ H).
    - intros ????? H; exact (r_cat_disj _ _ H).
  Qed.
(*|
A couple helpers for manipulating the new variables.
|*)
  Definition s_prf {Γ : ctxS} {x} (i : Γ.(sub_elt) ∋ x) : P x := Γ.(sub_prf) x i .

  Definition s_elt_upg {Γ : ctxS} {x} (i : Γ.(sub_elt) ∋ x) : sigS P :=
    {| sub_prf := Γ.(sub_prf) x i |}.

  Definition s_var_upg {Γ : ctxS} {x : T} (i : Γ.(sub_elt) ∋ x)
    : Γ ∋ (s_elt_upg i).(sub_elt) := i.
End with_param.
(*|
.. coq:: none
|*)
#[global] Arguments ctxS T C {CC} P.
#[global] Arguments allS {T C CC} P Γ.

#[global] Notation "∅ₛ" := (nilS) : ctx_scope.
#[global] Notation "Γ +▶ₛ Δ" := (catS Γ Δ) : ctx_scope.

(*|
In the case of sub-contexts over concrete contexts we provide a wrapper for the
"append" operation.
|*)
From OGS.Ctx Require Import Ctx Covering.
Section with_param.
  Context {T} {P : T -> SProp}.

  Program Definition conS (Γ : ctxS T (ctx T) P) (x : sigS P) : ctxS T (ctx T) P :=
    {| sub_elt := Γ.(sub_elt) ▶ₓ x.(sub_elt) |}.
  Next Obligation.
    intros ? i; cbn in i.
    remember (Γ.(sub_elt) ▶ₓ x.(sub_elt)) as c; apply noConfusion_inv in Heqc.
    destruct i.
    - pose proof (H := f_equal (pr2 (B := fun _ => _)) Heqc); cbn in H.
      rewrite H; now apply x.(sub_prf).
    - pose proof (H := f_equal (pr1 (B := fun _ => _)) Heqc); cbn in H.
      rewrite H in i; now apply Γ.(sub_prf).
  Qed.
End with_param.

#[global] Notation "Γ ▶ₛ x" := (conS Γ x) : ctx_scope.
