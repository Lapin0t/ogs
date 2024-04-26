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
Covering:
---------
Predicate for splitting a context into a disjoint union
|*)
  Inductive cover : ctx X -> ctx X -> ctx X -> Type :=
  | CNil : ∅ ⊎ ∅  ≡ ∅
  | CLeft  {x xs ys zs} : xs ⊎ ys ≡ zs -> (xs ▶ x) ⊎ ys ≡ (zs ▶ x)
  | CRight {x xs ys zs} : xs ⊎ ys ≡ zs -> xs ⊎ (ys ▶ x) ≡ (zs ▶ x)
  where "a ⊎ b ≡ c" := (cover a b c).
(*|
.. coq:: none
|*)
  Derive Signature NoConfusion NoConfusionHom for cover.
(*|
.. coq::
|*)
  Equations cover_nil_r xs : xs ⊎ ∅ ≡ xs :=
    cover_nil_r ∅        := CNil ;
    cover_nil_r (xs ▶ _) := CLeft (cover_nil_r xs) .
  #[global] Arguments cover_nil_r {xs}.

  Equations cover_nil_l xs : ∅ ⊎ xs ≡ xs :=
    cover_nil_l ∅        := CNil ;
    cover_nil_l (xs ▶ _) := CRight (cover_nil_l xs) .
  #[global] Arguments cover_nil_l {xs}.

  Equations cover_cat {xs} ys : xs ⊎ ys ≡ (xs +▶ ys) :=
    cover_cat ∅        := cover_nil_r ;
    cover_cat (ys ▶ _) := CRight (cover_cat ys) .
  #[global] Arguments cover_cat {xs ys}.

  Equations r_cover_l {xs ys zs} : xs ⊎ ys ≡ zs -> xs ⊆ zs :=
    r_cover_l (CLeft c)  _ top     := top ;
    r_cover_l (CLeft c)  _ (pop i) := pop (r_cover_l c _ i) ;
    r_cover_l (CRight c) _ i       := pop (r_cover_l c _ i) .

  Equations r_cover_r {xs ys zs} : xs ⊎ ys ≡ zs -> ys ⊆ zs :=
    r_cover_r (CLeft c)  _ i       := pop (r_cover_r c _ i) ;
    r_cover_r (CRight c) _ top     := top ;
    r_cover_r (CRight c) _ (pop i) := pop (r_cover_r c _ i) .

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

  Variant cover_view {xs ys zs} (p : xs ⊎ ys ≡ zs) [z] : zs ∋ z -> Type :=
  | Vcov_l  (i : xs ∋ z) : cover_view p (r_cover_l p _ i)
  | Vcov_r (j : ys ∋ z) : cover_view p (r_cover_r p _ j)
  .
  #[global] Arguments Vcov_l {xs ys zs p z}.
  #[global] Arguments Vcov_r {xs ys zs p z}.

  Lemma view_cover {xs ys zs} (p : xs ⊎ ys ≡ zs) [z] (i : zs ∋ z) : cover_view p i.
  Proof.
    revert xs ys p; induction zs; intros xs ys p; dependent elimination i.
    + dependent elimination p; [ exact (Vcov_l top) | exact (Vcov_r top) ].
    + dependent elimination p.
      * destruct (IHzs v _ _ c); [ exact (Vcov_l (pop i)) | exact (Vcov_r j) ].
      * destruct (IHzs v _ _ c0); [ exact (Vcov_l i) | exact (Vcov_r (pop j)) ].
  Qed.
(*|
Finishing the instanciation of the abstract interface for `ctx X`.
|*)
  #[global] Instance free_context_cat_wkn : context_cat_wkn X (ctx X) :=
    {| r_cat_l _ _ := r_cover_l cover_cat ;
       r_cat_r _ _ := r_cover_r cover_cat |}.

  #[global] Instance free_context_laws : context_laws X (ctx X).
  Proof.
    esplit.
    - intros ? i; dependent elimination i.
    - intros ??? i; destruct (view_cover cover_cat i).
      now refine (Vcat_l _).
      now refine (Vcat_r _).
    - intros ????? H; now apply r_cover_l_inj in H.
    - intros ????? H; now apply r_cover_r_inj in H.
    - intros ????? H; now apply r_cover_disj in H.
  Qed.
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

(* WIP is this needed?
Lemma r_cover_l_nil {Γ} : r_cover_l cover_nil_r ≡ₐ @r_id X _ _ Γ .
Proof.
  intros ? i; induction Γ; dependent elimination i; eauto.
  cbn; f_equal; apply IHΓ.
Qed.

Lemma a_cover_proj_l {Γ1 Γ2 Γ3 Δ} (H : Γ1 ⊎ Γ2 ≡ Γ3) (u : Γ1 =[F]> Δ) (v : Γ2 =[F]> Δ)
  : r_cover_l H ᵣ⊛ [ u , H , v ] ≡ₐ u.
Proof.
  intros ? i; cbn.
  remember (r_cover_l H a i) as j.
  destruct (view_cover H j).
  - now f_equal; apply (r_cover_l_inj H).
  - now apply ex_falso, (r_cover_disj H i j).
Qed.

Lemma a_cover_proj_r {Γ1 Γ2 Γ3 Δ} (H : Γ1 ⊎ Γ2 ≡ Γ3) (u : Γ1 =[F]> Δ) (v : Γ2 =[F]> Δ)
  : r_cover_r H ᵣ⊛ [ u , H , v ] ≡ₐ v.
Proof.
  intros ? j; cbn.
  remember (r_cover_r H a j) as i.
  destruct (view_cover H i).
  - now apply ex_falso, (r_cover_disj H i j).
  - now f_equal; apply (r_cover_r_inj H).
Qed.

Lemma a_cover_uniq {Γ1 Γ2 Γ3 Δ} (H : Γ1 ⊎ Γ2 ≡ Γ3)
  (u : Γ1 =[F]> Δ) (v : Γ2 =[F]> Δ) (w : Γ3 =[F]> Δ)
  (H1 : u ≡ₐ r_cover_l H ᵣ⊛ w)
  (H2 : v ≡ₐ r_cover_r H ᵣ⊛ w)
  : [ u , H , v ] ≡ₐ w .
Proof.
  intros ? i; unfold a_cover.
  destruct (view_cover H i); [ exact (H1 a i) | exact (H2 a j) ].
Qed.

Lemma view_cat_simpl_l {Γ1 Γ2 x} (i : x ∈ Γ1)
      : view_cat (r_cat_l_ccr (Δ:=Γ2) _ i) = CLeftV i .
Proof.
  pose (uu := view_cat (r_cat_l_ccr (Δ:=Γ2) x i)).
  fold uu; dependent induction uu.
  - apply r_cover_l_inj in x1; rewrite x1 in x.
    dependent destruction x; now simpl_depind.
  - symmetry in x1; apply r_cover_disj in x1; destruct x1.
Qed.

Lemma view_cat_simpl_r {Γ1 Γ2} {x : X} (i : x ∈ Γ2)
      : view_cat (r_cat_r_ccr (Γ:=Γ1) _ i) = CRightV i .
Proof.
  pose (uu := view_cat (r_cat_r_ccr (Γ:=Γ1) x i)); fold uu.
  dependent induction uu.
  - apply r_cover_disj in x1; destruct x1.
  - apply r_cover_r_inj in x1; rewrite x1 in x.
    dependent destruction x; now simpl_depind.
Qed.

Lemma a_eq_cover_id {Γ1 Γ2 Γ3 : ctx X} (H : Γ1 ⊎ Γ2 ≡ Γ3)
  : [ r_cover_l H , H , r_cover_r H ] ≡ₐ r_id .
Proof. now apply a_cover_uniq. Qed.

Lemma a_eq_cover_map {F G : Fam₁ X} {Γ1 Γ2 Γ3 Δ1 Δ2} (f : forall x, F x Δ1 -> G x Δ2)
  (H : Γ1 ⊎ Γ2 ≡ Γ3) (u : Γ1 =[F]> Δ1) (v : Γ2 =[F]> Δ1)
  : a_map [ u , H , v ] f ≡ₐ [ a_map u f , H , a_map v f ].
Proof.
  symmetry; apply a_cover_uniq; intros ? i; cbn; f_equal; symmetry.
  now apply a_cover_proj_l.
  now apply a_cover_proj_r.
Qed.

Equations cover_swap {Γ1 Γ2 Γ3} : Γ1 ⊎ Γ2 ≡ Γ3 -> Γ2 ⊎ Γ1 ≡ Γ3 :=
  cover_swap CNil       := CNil ;
  cover_swap (CLeft p)  := CRight (cover_swap p) ;
  cover_swap (CRight p) := CLeft (cover_swap p) .

Lemma cover_swap_swap {Γ1 Γ2 Γ3} (p : Γ1 ⊎ Γ2 ≡ Γ3) : cover_swap (cover_swap p) = p.
  dependent induction p; cbn; f_equal; eauto.
Qed.

Equations cat_cover {xs0 xs1 ys0 ys1 zs0 zs1}
  : xs0 ⊎ ys0 ≡ zs0
    -> xs1 ⊎ ys1 ≡ zs1
    -> (xs0 +▶ xs1) ⊎ (ys0 +▶ ys1) ≡ (zs0 +▶ zs1) :=
  cat_cover a (CNil)     := a ;
  cat_cover a (CLeft b)  := CLeft (cat_cover a b) ;
  cat_cover a (CRight b) := CRight (cat_cover a b) .

Equations ext_cover_l {xs ys zs} (Γ : ctx X)
  : xs ⊎ ys ≡ zs
    -> (xs +▶ Γ) ⊎ ys ≡ (zs +▶ Γ) :=
  ext_cover_l ∅        c := c ;
  ext_cover_l (Γ ▶ _) c := CLeft (ext_cover_l Γ c) .

Equations ext_cover_r {xs ys zs} (Γ : ctx X)
  : xs ⊎ ys ≡ zs
    -> xs ⊎ (ys +▶ Γ) ≡ (zs +▶ Γ) :=
  ext_cover_r ∅        c := c ;
  ext_cover_r (Γ ▶ _) c := CRight (ext_cover_r Γ c) .
*)
