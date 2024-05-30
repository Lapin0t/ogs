(*|
Covering for free contexts
==========================

In `Ctx/Ctx.v <Ctx.html>`_ we have instanciated the relevant part of the abstract interface
for concrete contexts. Here we tackle the rest of the structure. Basically, we need to
provide case-splitting for deciding if a variable ``i : (Γ +▶ Δ) ∋ x`` is in ``Γ`` or in
``Δ``. We could do this directly but we prove a slight generalization, going through the
definition of coverings, a ternary relationship on concrete contexts witnessing that a
context is *covered* by the two others (respecting order).

.. coq:: none
|*)
From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.
From OGS.Ctx Require Import All Ctx.

Reserved Notation "a ⊎ b ≡ c" (at level 30).
Reserved Notation "a ▶ₐ v" (at level 30).
Reserved Notation "[ u , H , v ]" (at level 9).

#[local] Open Scope ctx_scope.

Section with_param.
  Context {X : Type} {F : Fam₁ X (ctx X)}.
(*|
A covering
----------

This inductive family provides proofs that some context ``zs`` is obtained by "zipping"
together two other contexts ``xs`` and ``ys``.
|*)
  Inductive cover : ctx X -> ctx X -> ctx X -> Type :=
  | CNil : ∅ₓ ⊎ ∅ₓ  ≡ ∅ₓ
  | CLeft  {x xs ys zs} : xs ⊎ ys ≡ zs -> (xs ▶ₓ x) ⊎ ys ≡ (zs ▶ₓ x)
  | CRight {x xs ys zs} : xs ⊎ ys ≡ zs -> xs ⊎ (ys ▶ₓ x) ≡ (zs ▶ₓ x)
  where "a ⊎ b ≡ c" := (cover a b c).
(*|
.. coq:: none
|*)
  Derive Signature NoConfusion NoConfusionHom for cover.
(*|
Basic useful coverings.
|*)
  Equations cover_nil_r xs : xs ⊎ ∅ₓ ≡ xs :=
    cover_nil_r ∅ₓ        := CNil ;
    cover_nil_r (xs ▶ₓ _) := CLeft (cover_nil_r xs) .
  #[global] Arguments cover_nil_r {xs}.

  Equations cover_nil_l xs : ∅ₓ ⊎ xs ≡ xs :=
    cover_nil_l ∅ₓ        := CNil ;
    cover_nil_l (xs ▶ₓ _) := CRight (cover_nil_l xs) .
  #[global] Arguments cover_nil_l {xs}.
(*|
This is the crucial one: the concatenation is covered by its two components.
|*)
  Equations cover_cat {xs} ys : xs ⊎ ys ≡ (xs +▶ ys) :=
    cover_cat ∅ₓ        := cover_nil_r ;
    cover_cat (ys ▶ₓ _) := CRight (cover_cat ys) .
  #[global] Arguments cover_cat {xs ys}.
(*|
A covering gives us two injective renamings, left embedding and right embedding.
|*)
  Equations r_cover_l {xs ys zs} : xs ⊎ ys ≡ zs -> xs ⊆ zs :=
    r_cover_l (CLeft c)  _ top     := top ;
    r_cover_l (CLeft c)  _ (pop i) := pop (r_cover_l c _ i) ;
    r_cover_l (CRight c) _ i       := pop (r_cover_l c _ i) .

  Equations r_cover_r {xs ys zs} : xs ⊎ ys ≡ zs -> ys ⊆ zs :=
    r_cover_r (CLeft c)  _ i       := pop (r_cover_r c _ i) ;
    r_cover_r (CRight c) _ top     := top ;
    r_cover_r (CRight c) _ (pop i) := pop (r_cover_r c _ i) .
(*|
Injectivity.
|*)
  Lemma r_cover_l_inj {xs ys zs} (p : xs ⊎ ys ≡ zs) [x] (i j : xs ∋ x)
    (H : r_cover_l p _ i = r_cover_l p _ j) : i = j .
  Proof.
    induction p.
    - dependent elimination i.
    - dependent elimination i; dependent elimination j; try now inversion H.
      apply noConfusion_inv in H.
      f_equal; now apply IHp.
    - apply noConfusion_inv in H.
      now apply IHp.
  Qed.

  Lemma r_cover_r_inj {xs ys zs} (p : xs ⊎ ys ≡ zs) [y] (i j : ys ∋ y)
    (H : r_cover_r p _ i = r_cover_r p _ j) : i = j .
  Proof.
    induction p.
    - dependent elimination i.
    - apply noConfusion_inv in H; now apply IHp.
    - dependent elimination i; dependent elimination j; try now inversion H.
      apply noConfusion_inv in H.
      f_equal; now apply IHp.
  Qed.
(*|
The two embeddings have disjoint images.
|*)
  Lemma r_cover_disj {xs ys zs} (p : xs ⊎ ys ≡ zs) [a] (i : xs ∋ a) (j : ys ∋ a)
    (H : r_cover_l p _ i = r_cover_r p _ j) : T0.
  Proof.
    induction p.
    - inversion i.
    - dependent elimination i.
      + inversion H.
      + apply noConfusion_inv in H; cbn in H.
        exact (IHp v j H).
    - dependent elimination j.
      + inversion H.
      + apply noConfusion_inv in H; cbn in H.
        exact (IHp i v H).
  Qed.
(*|
Now we can start proving that the copairing of the two embeddings has non-empty fibers,
ie, we can case split.
|*)
  Variant cover_view {xs ys zs} (p : xs ⊎ ys ≡ zs) [z] : zs ∋ z -> Type :=
  | Vcov_l  (i : xs ∋ z) : cover_view p (r_cover_l p _ i)
  | Vcov_r (j : ys ∋ z) : cover_view p (r_cover_r p _ j)
  .
  #[global] Arguments Vcov_l {xs ys zs p z}.
  #[global] Arguments Vcov_r {xs ys zs p z}.
(*|
Indeed!
|*)
  Lemma view_cover {xs ys zs} (p : xs ⊎ ys ≡ zs) [z] (i : zs ∋ z) : cover_view p i.
  Proof.
    revert xs ys p; induction zs; intros xs ys p; dependent elimination i.
    + dependent elimination p; [ exact (Vcov_l top) | exact (Vcov_r top) ].
    + dependent elimination p.
      * destruct (IHzs v _ _ c); [ exact (Vcov_l (pop i)) | exact (Vcov_r j) ].
      * destruct (IHzs v _ _ c0); [ exact (Vcov_l i) | exact (Vcov_r (pop j)) ].
  Qed.
(*|
Finishing the instanciation of the abstract interface for ``ctx X``.
|*)
  #[global] Instance free_context_cat_wkn : context_cat_wkn X (ctx X) :=
    {| r_cat_l _ _ := r_cover_l cover_cat ;
       r_cat_r _ _ := r_cover_r cover_cat |}.

  #[global] Program Instance free_context_laws : context_laws X (ctx X).
  Next Obligation. dependent elimination i. Qed.
  Next Obligation.
    destruct (view_cover cover_cat i).
    now refine (Vcat_l _).
    now refine (Vcat_r _).
  Qed.
  Next Obligation. intros ?? H; now apply r_cover_l_inj in H. Qed.
  Next Obligation. intros ?? H; now apply r_cover_r_inj in H. Qed.
  Next Obligation. now apply r_cover_disj in H. Qed.
(*|
Additional utilities.
|*)
  Definition a_cover {Γ1 Γ2 Γ3 Δ} (p : Γ1 ⊎ Γ2 ≡ Γ3) (u : Γ1 =[F]> Δ) (v : Γ2 =[F]> Δ)
    : Γ3 =[F]> Δ
    := fun _ i => match view_cover p i with
               | Vcov_l i  => u _ i
               | Vcov_r j => v _ j
               end .
  #[global] Arguments a_cover _ _ _ _ _ _ _ _ /.

  #[global] Instance a_cover_proper {Γ1 Γ2 Γ3 Δ H}
    : Proper (asgn_eq _ _ ==> asgn_eq _ _ ==> asgn_eq _ _) (@a_cover Γ1 Γ2 Γ3 Δ H).
  Proof.
    intros ? ? H1 ? ? H2 ? i; unfold a_cover.
    destruct (view_cover H i); [ now apply H1 | now apply H2 ].
  Qed.
End with_param.

#[global] Notation "a ⊎ b ≡ c" := (cover a b c).
#[global] Notation "a ▶ₐ v" := (a_append a v) : asgn_scope.
#[global] Notation "[ u , H , v ]" := (a_cover H u v) : asgn_scope.
