(*|
Contexts
=========

.. coq:: none
|*)

From Coq Require Import Program.Equality.
From Equations Require Import Equations.
Set Equations Transparent.

Import EqNotations.

From Coinduction Require Import lattice.

From OGS Require Import Utils.
From OGS Require Import Utils.Prelude.

(*|
Contexts are simply lists, with the purely aesthetic choice of representing cons as coming from the right.
.. coq::
|*)
Inductive ctx (X : Type) : Type :=
| cnil : ctx X
| ccon : ctx X -> X -> ctx X
.
(*|
.. coq:: none
|*)

Arguments cnil {X}.
Arguments ccon {X} Γ x.
Derive NoConfusion for ctx.

#[global] Declare Scope ctx_scope.
#[global] Delimit Scope ctx_scope with ctx.
#[global] Bind Scope ctx_scope with ctx.
(*|
.. coq::
|*)
#[global] Notation "∅" := (cnil) : ctx_scope.
#[global] Notation "Γ ▶ x" := (ccon Γ%ctx x) (at level 40, left associativity) : ctx_scope.

(*|
Concatenation of contexts, by induction on the second argument
|*)
Equations ccat {X} : ctx X -> ctx X -> ctx X :=
  ccat Γ ∅       := Γ ;
  ccat Γ (Δ ▶ x) := (ccat Γ Δ) ▶ x .

#[global] Notation "Γ +▶ Δ" := (ccat Γ%ctx Δ%ctx) (at level 50, left associativity) : ctx_scope.

Lemma ccat_empty_l {X} {Γ : ctx X} : (∅ +▶ Γ)%ctx = Γ.
  induction Γ; eauto.
  cbn; now f_equal.
Qed.

Lemma ccat_empty_r {X} {Γ : ctx X} : (Γ +▶ ∅)%ctx = Γ.
  reflexivity.
Qed.

Section lemma.
Context {X : Type}.

(*|
Join over contexts
|*)
Equations join : ctx (ctx X) -> ctx X :=
  join (∅)     := ∅ ;
  join (Γ ▶ xs) := join Γ +▶ xs .

(*|
Two mutually recursive functions, defined at once via a boolean argument.
Given a context of contexts, we join them, but by keeping only half the contexts:
the ones in odd positions (join_odd) respectively in even positions (join_even)
|*)
Equations join_even_odd_aux : bool -> ctx (ctx X) -> ctx X :=
  join_even_odd_aux b (∅) := ∅ ;
  join_even_odd_aux true  (Γ ▶ xs) := join_even_odd_aux false Γ +▶ xs ;
  join_even_odd_aux false (Γ ▶ xs) := join_even_odd_aux true Γ .

Notation join_even := (join_even_odd_aux true) .
Notation join_odd := (join_even_odd_aux false) .

(*
Equations join_cat Γs Δs : join (Γs +▶ Δs)%ctx = ((join Γs) +▶ (join Δs))%ctx :=
  join_cat Γs ∅%ctx        := eq_refl ;
  join_cat Γs (Δs ▶ Δ)%ctx :=
    rew app_assoc Δ (join Δs) (join Γs)
     in f_equal (app Δ) (join_cat Γs Δs).
Arguments join_cat {Γs Δs}.
*)

(*|
We wish to manipulate intrinsically typed terms. We hence need a tightly typed notion of position in the context: rather than a loose index, [has Γ x] is a proof of membership of [x] to [Γ].
|*)
Inductive has : ctx X -> X -> Type :=
| top {Γ x} : has (Γ ▶ x) x
| pop {Γ x y} : has Γ x -> has (Γ ▶ y) x.
Notation "Γ ∋ x" := (has Γ%ctx x) (at level 30).
Derive Signature for has.

(*|
Assignment
------------
We distinguish assignments, mapping variables in a context to terms, from substitutions, applying an assignment to a term.
Assignments are again intrinsically typed, mapping variables of a context Γ to open terms with variables in Δ.
|*)
Definition assignment (F : ctx X -> X -> Type) (Γ Δ : ctx X) := forall x, Γ ∋ x -> F Δ x.
Notation "Γ =[ F ]> Δ" := (assignment F Γ%ctx Δ%ctx) (at level 30).

Definition ass_eq {F : ctx X -> X -> Type} Γ Δ : relation (Γ =[F]> Δ) :=
  dpointwise_relation (fun x => pointwise_relation _ eq)%signature.

Notation "u ≡ₐ v" := (ass_eq _ _ u v) (at level 50).

#[global] Instance ass_equivalence {F Γ Δ} : Equivalence (@ass_eq F Γ Δ).
econstructor.
- intros u ? i; reflexivity.
- intros u h ? i ?; symmetry; now apply (H i a).
- intros u v w h1 h2 ? i. transitivity (v a i); [ now apply h1 | now apply h2 ].
Qed.

(*|
Renaming
---------
Context inclusion is defined as an assignment of variables in Γ to variables in Δ.
This inclusion can be thought of as the assignment whose associated substitution is a renaming of assignments.
|*)
Notation "Γ ⊆ Δ" := (assignment has Γ%ctx Δ%ctx) (at level 30).

Definition s_ren {F Γ1 Γ2 Γ3} (a : Γ2 =[F]> Γ3) (b : Γ1 ⊆ Γ2) : Γ1 =[F]> Γ3 :=
  fun _ i => a _ (b _ i).
Infix "⊛ᵣ" := s_ren (at level 14).

#[global] Instance s_ren_proper {F Γ1 Γ2 Γ3} : Proper (ass_eq _ _ ==> ass_eq _ _ ==> ass_eq _ _) (@s_ren F Γ1 Γ2 Γ3) .
Proof.
  intros ? ? H1 ? ? H2 ? i.
  unfold s_ren; now rewrite H2, H1.
Qed.

(*|
The identity inclusion, whose renaming is the identity.
|*)
Definition r_id {Γ} : Γ ⊆ Γ := fun _ i => i .

Lemma s_ren_id {F Γ1 Γ2} (a : Γ1 =[F]> Γ2) : a ⊛ᵣ r_id ≡ₐ a .
  intros ? i; reflexivity.
Qed.

(*|
Composition of context inclusion induces a composed renaming.
|*)
Definition r_comp {Γ1 Γ2 Γ3} (a : Γ2 ⊆ Γ3) (b : Γ1 ⊆ Γ2) : Γ1 ⊆ Γ3 :=
  a ⊛ᵣ b.

Lemma s_ren_comp {F Γ1 Γ2 Γ3 Γ4} (u : Γ3 =[F]> Γ4) (v : Γ2 ⊆ Γ3) (w : Γ1 ⊆ Γ2)
      : u ⊛ᵣ (r_comp v w) ≡ₐ (u ⊛ᵣ v) ⊛ᵣ w.
Proof. reflexivity. Qed.

(* helper for defining various shiftings *)
Equations has_case {Γ Δ : ctx X} {F : ctx X -> X -> Type} {a}
  : F Δ a -> (forall x, Γ ∋ x -> F Δ x) -> forall x, (Γ ▶ a) ∋ x -> F Δ x :=
  has_case z s _ top     := z ;
  has_case z s _ (pop i) := s _ i .

Definition r_shift {Γ Δ : ctx X} {a} (f : Γ ⊆ Δ) : (Γ ▶ a) ⊆ (Δ ▶ a)
  := has_case top (fun _ i => pop (f _ i)).

Definition r_shift2 {Γ Δ : ctx X} {a b} (f : Γ ⊆ Δ) : (Γ ▶ a ▶ b) ⊆ (Δ ▶ a ▶ b)
  := r_shift (r_shift f).

Equations r_shift_n {Γ Δ : ctx X} (xs : ctx X) (f : Γ ⊆ Δ) : (Γ +▶ xs) ⊆ (Δ +▶ xs) :=
  r_shift_n ∅        f _ i       := f _ i ;
  r_shift_n (xs ▶ _) f _ top     := top ;
  r_shift_n (xs ▶ _) f _ (pop i) := pop (r_shift_n xs f _ i) .

Inductive cover : ctx X -> ctx X -> ctx X -> Type :=
| CNil :                                 cover ∅        ∅        ∅
| CLeft {x xs ys zs} : cover xs ys zs ->  cover (xs ▶ x) ys       (zs ▶ x)
| CRight {x xs ys zs} : cover xs ys zs -> cover xs       (ys ▶ x) (zs ▶ x)
.
Notation "a ⊎ b ≡ c" := (cover a b c) (at level 30).
Derive NoConfusion for cover.

Equations cover_swap {Γ1 Γ2 Γ3} : Γ1 ⊎ Γ2 ≡ Γ3 -> Γ2 ⊎ Γ1 ≡ Γ3 :=
  cover_swap CNil := CNil ;
  cover_swap (CLeft p) := CRight (cover_swap p) ;
  cover_swap (CRight p) := CLeft (cover_swap p) .

Lemma cover_swap_swap {Γ1 Γ2 Γ3} (p : Γ1 ⊎ Γ2 ≡ Γ3) : cover_swap (cover_swap p) = p.
  dependent induction p; cbn; f_equal; eauto.
Qed.

Equations cover_nil_r xs : xs ⊎ ∅ ≡ xs :=
  cover_nil_r ∅        := CNil ;
  cover_nil_r (xs ▶ x) := CLeft (cover_nil_r xs) .
#[global] Arguments cover_nil_r {xs}.

Equations cover_nil_l xs : ∅ ⊎ xs ≡ xs :=
  cover_nil_l ∅        := CNil ;
  cover_nil_l (xs ▶ x) := CRight (cover_nil_l xs) .
#[global] Arguments cover_nil_l {xs}.

Equations cover_cat {xs} ys : xs ⊎ ys ≡ (xs +▶ ys) :=
  cover_cat ∅        := cover_nil_r ;
  cover_cat (ys ▶ y) := CRight (cover_cat ys) .
#[global] Arguments cover_cat {xs ys}.

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
  ext_cover_l ∅       c := c ;
  ext_cover_l (Γ ▶ _) c := CLeft (ext_cover_l Γ c) .

Equations ext_cover_r {xs ys zs} (Γ : ctx X)
          : xs ⊎ ys ≡ zs
          -> xs ⊎ (ys +▶ Γ) ≡ (zs +▶ Γ) :=
  ext_cover_r ∅ c := c ;
  ext_cover_r (Γ ▶ _) c := CRight (ext_cover_r Γ c) .

Equations r_cover_l {xs ys zs} : xs ⊎ ys ≡ zs -> xs ⊆ zs :=
  r_cover_l (CLeft c)  _ top     := top ;
  r_cover_l (CLeft c)  _ (pop i) := pop (r_cover_l c _ i) ;
  r_cover_l (CRight c) _ i       := pop (r_cover_l c _ i) .

Equations r_cover_r {xs ys zs} : xs ⊎ ys ≡ zs -> ys ⊆ zs :=
  r_cover_r (CLeft c)  _ i       := pop (r_cover_r c _ i) ;
  r_cover_r (CRight c) _ top     := top ;
  r_cover_r (CRight c) _ (pop i) := pop (r_cover_r c _ i) .

Equations cover_split {xs ys zs} : xs ⊎ ys ≡ zs -> has zs ⇒ᵢ (has xs +ᵢ has ys) :=
  cover_split (CLeft c)  _ top     := inl top ;
  cover_split (CRight c) _ top     := inr top ;
  cover_split (CLeft c)  _ (pop i) with cover_split c _ i :=
      { | inl j := inl (pop j) ;
        | inr j := inr j } ;
  cover_split (CRight c) _ (pop i) with cover_split c _ i :=
      { | inl j := inl j ;
        | inr j := inr (pop j) } .

Lemma cover_split_inv_r {xs ys zs} (p : xs ⊎ ys ≡ zs) [x] (i : zs ∋ x) (j : xs ∋ x)
          : cover_split p _ i = inl j
            -> i = r_cover_l p _ j.
  revert xs ys zs p x i j; induction p; intros ? i j H.
  all: dependent destruction i; cbn in H; try now inversion H.
  all: destruct (cover_split p _ i) eqn:Hs; inversion_clear H in Hs.
  all: cbn; f_equal; now apply IHp.
Qed.

Lemma cover_split_inv_l {xs ys zs} (p : xs ⊎ ys ≡ zs) [x] (i : zs ∋ x) (j : ys ∋ x)
          : cover_split p _ i = inr j
            -> i = r_cover_r p _ j.
  revert xs ys zs p x i j; induction p; intros ? i j H.
  all: dependent destruction i; cbn in H; try now inversion H.
  all: destruct (cover_split p _ i) eqn:Hs; inversion_clear H in Hs.
  all: cbn; f_equal; now apply IHp.
Qed.

Equations s_empty {F Γ} : ∅ =[F]> Γ :=
  s_empty x (!).

Definition cover_split3_left (Γ1 Γ2 Γ3 Γ123 : ctx X) : Type :=
  { Γ12 & Γ1 ⊎ Γ2 ≡ Γ12 * Γ12 ⊎ Γ3 ≡ Γ123 }%type.

Definition cover_split3_right (Γ1 Γ2 Γ3 Γ123 : ctx X) : Type :=
  { Γ23 & Γ1 ⊎ Γ23 ≡ Γ123 * Γ2 ⊎ Γ3 ≡ Γ23 }%type.

Equations cover_assoc1 {Γ1 Γ2 Γ12 Γ3 Γ123} (H1 : Γ1 ⊎ Γ2 ≡ Γ12) (H2 : Γ12 ⊎ Γ3 ≡ Γ123)
  : cover_split3_right Γ1 Γ2 Γ3 Γ123 :=
  cover_assoc1 u          CNil :=
    (_ ,' (u , cover_nil_r)) ;
  cover_assoc1 (CLeft u)  (CLeft v) :=
    (_ ,' (CLeft (fst (projT2 (cover_assoc1 u v))) ,
           snd (projT2 (cover_assoc1 u v)))) ;
  cover_assoc1 (CRight u) (CLeft v) :=
    (_ ,' (CRight (fst (projT2 (cover_assoc1 u v))) ,
           CLeft  (snd (projT2 (cover_assoc1 u v))))) ;
  cover_assoc1 u          (CRight v) :=
    (_ ,' (CRight (fst (projT2 (cover_assoc1 u v))) ,
           CRight (snd (projT2 (cover_assoc1 u v))))) .

Definition cover_assoc1' {Γ1 Γ2 Γ3 Γ123}
  : cover_split3_left Γ1 Γ2 Γ3 Γ123
    -> cover_split3_right Γ1 Γ2 Γ3 Γ123 :=
  fun u => cover_assoc1 (fst (projT2 u)) (snd (projT2 u)) .

Notation cover_assoc1_ctx H1 H2 := (projT1 (cover_assoc1 H1 H2)).
Notation cover_assoc1_left H1 H2 := (fst (projT2 (cover_assoc1 H1 H2))).
Notation cover_assoc1_right H1 H2 := (snd (projT2 (cover_assoc1 H1 H2))).

Equations cover_assoc2 {Γ1 Γ2 Γ3 Γ23 Γ123} (H1 : Γ1 ⊎ Γ23 ≡ Γ123) (H2 : Γ2 ⊎ Γ3 ≡ Γ23)
  : cover_split3_left Γ1 Γ2 Γ3 Γ123 :=
  cover_assoc2 CNil v := (_ ,' (cover_nil_l , v)) ;
  cover_assoc2 (CLeft u)  v :=
    (_ ,' (CLeft (fst (projT2 (cover_assoc2 u v))) ,
           CLeft (snd (projT2 (cover_assoc2 u v))))) ;
  cover_assoc2 (CRight u) (CLeft v) :=
    (_ ,' (CRight (fst (projT2 (cover_assoc2 u v))) ,
           CLeft  (snd (projT2 (cover_assoc2 u v))))) ;
  cover_assoc2 (CRight u) (CRight v) :=
    (_ ,' (fst (projT2 (cover_assoc2 u v)) ,
           CRight (snd (projT2 (cover_assoc2 u v))))) .

Definition cover_assoc2' {Γ1 Γ2 Γ3 Γ123}
  : cover_split3_right Γ1 Γ2 Γ3 Γ123
    -> cover_split3_left Γ1 Γ2 Γ3 Γ123 :=
  fun u => cover_assoc2 (fst (projT2 u)) (snd (projT2 u)) .

Notation cover_assoc2_ctx H1 H2 := (projT1 (cover_assoc2 H1 H2)).
Notation cover_assoc2_left H1 H2 := (fst (projT2 (cover_assoc2 H1 H2))).
Notation cover_assoc2_right H1 H2 := (snd (projT2 (cover_assoc2 H1 H2))).

(*
Lemma cover_assoc12 {Γ1 Γ2 Γ3 Γ123} (u : cover_split3_left Γ1 Γ2 Γ3 Γ123)
      : cover_assoc2' (cover_assoc1' u) = u .
  destruct u as [? [H1 H2]]; cbn.
  funelim (cover_assoc1 H1 H2); cbn.
  - dependent elimination u. eauto.
  - clear H0; unfold cover_assoc2' in H.
    assert (H2 := projT2_eq H).
    remember (projT1_eq H) as H1 eqn:H3 in *; clear H3 H; cbn in *.
    apply eq_existT_uncurried.
    unshelve econstructor.
    apply (f_equal (fun x => x ▶ _)%ctx); exact H1.
    etransitivity.
    symmetry; apply (@rew_pair _ (fun Γ12 => (_ ⊎ _ ≡ Γ12)) (fun Γ12 => Γ12 ⊎ _ ≡ _)).
    apply pair_equal_spec; split.
    Search "rew".


    Search "rew".
    rewrite <- rew_pair.
    dependent destruction H1.
    Search (_ = (_ , _)).
    Search ((_ , _) = (_ , _)).
    Check (projT1_eq H).
    Search (projT1 ?a = ?b).
    Check (projT1_eq H).

    Check (EqdepFacts.eq_sigT_fst H).
Search ((_ ,' _) = (_ ,' _)).
    Search

    apply EqdepFacts.eq_sigT_iff_eq_dep.
    Print EqdepFacts.eq_dep.

Lemma cover_assoc_ctx12 {Γ1 Γ2 Γ3 Γ123} (H1 : Γ1 ⊎ Γ2 ≡ Γ12) (H2 : Γ12 ⊎ Γ3 ≡ Γ123)
  cover_assoc2_ctx (cover_assoc1_lft H1 H2) (cover_assoc1_rgt H1 H2)
  = Γ12 .

Lemma cover_assoc12 {Γ1 Γ2 Γ12 Γ3 Γ123} (H1 : Γ1 ⊎ Γ2 ≡ Γ12) (H2 : Γ12 ⊎ Γ3 ≡ Γ123)
  : cover_assoc2_lft (cover_assoc1_lft H1 H2) (cover_assoc1_rgt H1 H2)
    = H1 .
*)


Lemma cover_assoc2_eq1 {Γ1 Γ2 Γ3 Γ23 Γ123} (H1 : Γ1 ⊎ Γ23 ≡ Γ123) (H2 : Γ2 ⊎ Γ3 ≡ Γ23)
      : r_cover_l H1 ≡ₐ r_cover_l (cover_assoc2_right H1 H2) ⊛ᵣ r_cover_l (cover_assoc2_left H1 H2).
  funelim (cover_assoc2 H1 H2); simp cover_assoc.
  dependent destruction v; intros ? i; dependent destruction i.
  all: intros ? i.
  dependent destruction i; eauto.
  all: cbn; f_equal; apply H.
  Qed.

Lemma cover_assoc2_eq2 {Γ1 Γ2 Γ3 Γ23 Γ123} (H1 : Γ1 ⊎ Γ23 ≡ Γ123) (H2 : Γ2 ⊎ Γ3 ≡ Γ23)
      : r_cover_r H1 ⊛ᵣ r_cover_l H2 ≡ₐ r_cover_l (cover_assoc2_right H1 H2) ⊛ᵣ r_cover_r (cover_assoc2_left H1 H2).
  funelim (cover_assoc2 H1 H2); simp cover_assoc.
  dependent destruction v; intros ? i; dependent destruction i.
  all: intros ? i.
  2: dependent destruction i; eauto.
  all: cbn; f_equal; apply H.
  Qed.

Lemma cover_assoc2_eq3 {Γ1 Γ2 Γ3 Γ23 Γ123} (H1 : Γ1 ⊎ Γ23 ≡ Γ123) (H2 : Γ2 ⊎ Γ3 ≡ Γ23)
      : r_cover_r H1 ⊛ᵣ r_cover_r H2 ≡ₐ r_cover_r (cover_assoc2_right H1 H2).
  funelim (cover_assoc2 H1 H2); simp cover_assoc.
  dependent destruction v; intros ? i; dependent destruction i.
  all: intros ? i.
  3: dependent destruction i; eauto.
  all: cbn; f_equal; apply H.
  Qed.

Lemma cover_assoc1_eq1 {Γ1 Γ2 Γ12 Γ3 Γ123} (H1 : Γ1 ⊎ Γ2 ≡ Γ12) (H2 : Γ12 ⊎ Γ3 ≡ Γ123) :
    r_cover_l H2 ⊛ᵣ r_cover_l H1 ≡ₐ r_cover_l (cover_assoc1_left H1 H2).
Proof.
  funelim (cover_assoc1 H1 H2); simp cover_assoc.
  dependent destruction u; intros ? i; dependent destruction i.
  all: intros ? i.
  dependent destruction i; eauto.
  all: cbn; f_equal; apply H.
  Qed.

Lemma cover_assoc1_eq2 {Γ1 Γ2 Γ12 Γ3 Γ123} (H1 : Γ1 ⊎ Γ2 ≡ Γ12) (H2 : Γ12 ⊎ Γ3 ≡ Γ123) :
    r_cover_l H2 ⊛ᵣ r_cover_r H1
    ≡ₐ
    r_cover_r (cover_assoc1_left H1 H2) ⊛ᵣ r_cover_l (cover_assoc1_right H1 H2) .
Proof.
  funelim (cover_assoc1 H1 H2); simp cover_assoc.
  dependent destruction u; intros ? i; dependent destruction i.
  all: intros ? i.
  2: dependent destruction i; eauto.
  all: cbn; f_equal; apply H.
Qed.

Lemma cover_assoc1_eq3 {Γ1 Γ2 Γ12 Γ3 Γ123} (H1 : Γ1 ⊎ Γ2 ≡ Γ12) (H2 : Γ12 ⊎ Γ3 ≡ Γ123) :
    r_cover_r H2 ≡ₐ
    r_cover_r (cover_assoc1_left H1 H2) ⊛ᵣ r_cover_r (cover_assoc1_right H1 H2) .
Proof.
  funelim (cover_assoc1 H1 H2); simp cover_assoc.
  dependent destruction u; intros ? i; dependent destruction i.
  all: intros ? i.
  3: dependent destruction i; eauto.
  all: cbn; f_equal; apply H.
Qed.

Equations s_cover {F Γ1 Γ2 Γ3 Δ} : Γ1 ⊎ Γ2 ≡ Γ3 -> Γ1 =[F]> Δ -> Γ2 =[F]> Δ -> Γ3 =[F]> Δ :=
  s_cover h u v _ i with cover_split h _ i := {
    | inl j := u _ j ;
    | inr j := v _ j
  } .
Notation "[ u , H , v ]" := (s_cover H u v) (at level 9).

#[global] Instance s_cover_proper {F Γ1 Γ2 Γ3 Δ} (H : Γ1 ⊎ Γ2 ≡ Γ3) : Proper (ass_eq _ _ ==> ass_eq _ _ ==> ass_eq _ _) (s_cover (F:=F) (Δ:=Δ) H).
intros ? ? H1 ? ? H2 ? i.
unfold s_cover, s_cover_clause_1.
destruct (cover_split H _ i); [ now apply H1 | now apply H2 ].
Qed.


Definition s_cat {F Γ1 Γ2 Δ} : Γ1 =[F]> Δ -> Γ2 =[F]> Δ -> (Γ1 +▶ Γ2) =[F]> Δ :=
  s_cover cover_cat .
Notation "[ u , v ]" := (s_cat u v) (at level 9).

Definition r_concat_l {Γ Δ : ctx X} : Γ ⊆ (Γ +▶ Δ) :=
  r_cover_l cover_cat .

Definition r_cover_l_nil {Γ} : r_cover_l cover_nil_r ≡ₐ @r_id Γ .
  intros ? i.
  induction Γ.
  - dependent elimination i.
  - dependent elimination i.
    reflexivity.
    unfold r_id; cbn; f_equal.
    apply (IHΓ h).
Qed.

Definition r_concat_r {Γ Δ : ctx X} : Δ ⊆ (Γ +▶ Δ) :=
  r_cover_r cover_cat .

Definition s_map {F G Γ Δ1 Δ2} (f : F Δ1 ⇒ᵢ G Δ2) (u : Γ =[F]> Δ1) : Γ =[G]> Δ2 :=
  fun _ i => f _ (u _ i) .

Definition r_concat3_1 {Γ Δ ϒ : ctx X} : (Γ +▶ Δ) ⊆ (Γ +▶ (Δ +▶ ϒ)) :=
  [ r_concat_l , r_concat_r ⊛ᵣ r_concat_l ].

Definition r_concat3_2 {Γ Δ ϒ : ctx X} : (Γ +▶ ϒ) ⊆ (Γ +▶ (Δ +▶ ϒ)) :=
  [ r_concat_l , r_concat_r ⊛ᵣ r_concat_r ].

Lemma s_eq_cover_empty_r {F Γ1 Δ} (u : Γ1 =[F]> Δ) : [ u , s_empty ] ≡ₐ u.
Proof.
  intros ? i.
  unfold s_cat, cover_cat, cover_nil_r, s_cover, s_cover_clause_1.
  dependent induction Γ1.
  - dependent elimination i.
  - dependent elimination i.
    + reflexivity.
    + cbn; unfold cover_split_clause_3.
      transitivity (match cover_split
                            ((fix cover_nil_r (xs : ctx X) : xs ⊎ ∅ ≡ xs :=
                                match xs as c return (c ⊎ ∅ ≡ c) with
                                | ∅%ctx => CNil
                                | (c ▶ x)%ctx => CLeft (cover_nil_r c)
                                end) Γ0) _ h
                    with
                    | inl h0 => u x1 (pop h0)
                    | inr h0 => s_empty x1 h0
                    end).
      destruct (cover_split ((fix cover_nil_r (xs : ctx X) : xs ⊎ ∅ ≡ xs :=
                                match xs as c return (c ⊎ ∅ ≡ c) with
                                | ∅%ctx => CNil
                                | (c ▶ x)%ctx => CLeft (cover_nil_r c)
                                end) Γ0) _ h);
        eauto.
      apply (IHΓ1 _ (fun _ i => u _ (pop i))).
  Qed.

Lemma s_eq_cover_l {F Γ1 Γ2 Γ3 Δ} (H : Γ1 ⊎ Γ2 ≡ Γ3) (u : Γ1 =[F]> Δ) (v : Γ2 =[F]> Δ)
      : [ u , H , v ] ⊛ᵣ r_cover_l H ≡ₐ u.
Proof.
  intros ? i. dependent induction H.
  - dependent elimination i.
  - dependent elimination i.
    + reflexivity.
    + unfold s_ren, s_cover, s_cover_clause_1; cbn; unfold cover_split_clause_3.
      transitivity (match cover_split H _ (r_cover_l H _ h) with
                    | inl h0 => u _ (pop h0)
                    | inr h0 => v _ h0
                    end).
      destruct (cover_split H _ (r_cover_l H _ h)); eauto.
      now apply (IHcover (fun _ i => u _ (pop i)) v).
  - unfold s_ren, s_cover, s_cover_clause_1; cbn; unfold cover_split_clause_4.
    transitivity (match cover_split H _ (r_cover_l H _ i) with
                  | inl h0 => u _ h0
                  | inr h0 => v _ (pop h0)
                  end).
    destruct (cover_split H _ (r_cover_l H _ i)); eauto.
    now apply (IHcover u (fun _ i => v _ (pop i))).
Qed.

Lemma s_eq_cat_l {F Γ1 Γ2 Δ} (u : Γ1 =[F]> Δ) (v : Γ2 =[F]> Δ)
      : [ u , v ] ⊛ᵣ r_concat_l ≡ₐ u.
  apply s_eq_cover_l.
Qed.

Lemma s_eq_cover_r {F Γ1 Γ2 Γ3 Δ} (H : Γ1 ⊎ Γ2 ≡ Γ3) (u : Γ1 =[F]> Δ) (v : Γ2 =[F]> Δ)
      : [ u , H , v ] ⊛ᵣ r_cover_r H ≡ₐ v.
Proof.
  dependent induction H; intros ? i.
  - dependent elimination i.
  - unfold s_ren, s_cover, s_cover_clause_1, r_comp.
    rewrite r_cover_r_equation_2, cover_split_equation_3.
      unfold cover_split_clause_3.
      transitivity (match cover_split H _ (r_cover_r H _ i) with
                    | inl h0 => u _ (pop h0)
                    | inr h0 => v _ h0
                    end).
      destruct (cover_split H _ (r_cover_r H a i)); eauto.
      now apply (IHcover (fun _ i => u _ (pop i)) v).
  - dependent elimination i.
    reflexivity.
    unfold s_ren, s_cover, s_cover_clause_1, r_comp.
    rewrite r_cover_r_equation_4, cover_split_equation_5.
    unfold cover_split_clause_4.
    transitivity (match cover_split H _ (r_cover_r H _ h) with
                  | inl h0 => u _ h0
                  | inr h0 => v _ (pop h0)
                  end).
    destruct (cover_split H _ (r_cover_r H x1 h)); eauto.
    now apply (IHcover u (fun _ i => v _ (pop i))).
Qed.

Lemma s_eq_cat_r {F Γ1 Γ2 Δ} (u : Γ1 =[F]> Δ) (v : Γ2 =[F]> Δ)
      : [ u , v ] ⊛ᵣ r_concat_r ≡ₐ v.
  apply s_eq_cover_r.
Qed.

Lemma s_eq_cover_uniq {F Γ1 Γ2 Γ3 Δ} (H : Γ1 ⊎ Γ2 ≡ Γ3)
       (u : Γ1 =[F]> Δ) (v : Γ2 =[F]> Δ) (w : Γ3 =[F]> Δ)
       (H1 : u ≡ₐ w ⊛ᵣ r_cover_l H)
       (H2 : v ≡ₐ w ⊛ᵣ r_cover_r H)
       : [ u , H , v ] ≡ₐ w .
  intros ? i.
  unfold s_cover, s_cover_clause_1.
  destruct (cover_split H _ i) eqn:Hs.
  rewrite (cover_split_inv_r H _ _ Hs); apply H1.
  rewrite (cover_split_inv_l H _ _ Hs); apply H2.
Qed.

(*
Lemma s_eq_cover_empty_l {F Γ1 Δ} (u : Γ1 =[F]> Δ)
          : [ s_empty , u ] ≡ₛ (rew <- [fun x => x =[F]> _] ccat_empty_l in u).
*)

(*
Lemma s_cat_assoc {F Γ1 Γ2 Γ3 Δ}
  (u1 : Γ1 =[F]> Δ) (u2 : Γ2 =[F]> Δ) (u3 : Γ3 =[F]> Δ)
  : [ [ u1 , u2 ] , u3 ]
      ≡ₛ [ u1 , [ u2 , u3 ] ] ⊛ᵣ ([ [ r_concat_l , r_concat_r ⊛ᵣ r_concat_l ] , r_concat_r ⊛ᵣ r_concat_r ]) .
Proof.
  apply s_eq_cover_uniq.
  - apply s_eq_cover_uniq.
    * intros ? i.
      unfold s_ren.
*)

Lemma s_cover_assoc1 {F Γ1 Γ2 Γ12 Γ3 Γ123 Δ}
  (H1 : Γ1 ⊎ Γ2 ≡ Γ12) (H2 : Γ12 ⊎ Γ3 ≡ Γ123)
  (u1 : Γ1 =[F]> Δ) (u2 : Γ2 =[F]> Δ) (u3 : Γ3 =[F]> Δ)
  : [ [ u1 , H1 , u2 ] , H2 , u3 ]
    ≡ₐ [ u1 , cover_assoc1_left H1 H2 , [ u2 , cover_assoc1_right H1 H2 , u3 ] ].
Proof.
  apply s_eq_cover_uniq.
  + apply s_eq_cover_uniq; rewrite <- s_ren_comp.
    * now rewrite cover_assoc1_eq1, s_eq_cover_l.
    * now rewrite cover_assoc1_eq2, s_ren_comp, s_eq_cover_r, s_eq_cover_l.
  + now rewrite (cover_assoc1_eq3 H1), s_ren_comp, 2 s_eq_cover_r.
Qed.

Lemma s_cover_assoc2 {F Γ1 Γ2 Γ3 Γ23 Γ123 Δ}
  (H1 : Γ1 ⊎ Γ23 ≡ Γ123) (H2 : Γ2 ⊎ Γ3 ≡ Γ23)
  (u1 : Γ1 =[F]> Δ) (u2 : Γ2 =[F]> Δ) (u3 : Γ3 =[F]> Δ)
  : [ u1 , H1 , [ u2 , H2 , u3 ] ]
    ≡ₐ [ [ u1 , cover_assoc2_left H1 H2 , u2 ] , cover_assoc2_right H1 H2 , u3 ].
Proof.
  apply s_eq_cover_uniq.
  + now rewrite (cover_assoc2_eq1 H1 H2), s_ren_comp, 2 s_eq_cover_l.
  + apply s_eq_cover_uniq; rewrite <- s_ren_comp.
    - now rewrite cover_assoc2_eq2 , s_ren_comp, s_eq_cover_l, s_eq_cover_r.
    - now rewrite cover_assoc2_eq3 , s_eq_cover_r.
Qed.

(*
Lemma s_cat_assoc {F Γ1 Γ2 Γ3 Δ}
  (u1 : Γ1 =[F]> Δ) (u2 : Γ2 =[F]> Δ) (u3 : Γ3 =[F]> Δ)
  : [ [ u1 , u2 ] , u3 ]
      ≡ₛ [ u1 , cover_assoc1_ cover_cat cover_cat , [ u2 , cover_assoc2 cover_cat cover_cat , u3 ] ].
Proof. apply s_cover_assoc. Qed.
*)

End lemma.

#[global] Notation join_even := (join_even_odd_aux true) .
#[global] Notation join_odd := (join_even_odd_aux false) .
#[global] Notation "Γ ∋ x" := (has Γ%ctx x) (at level 30) : type_scope.
#[global] Notation "a ⊎ b ≡ c" := (cover a%ctx b%ctx c%ctx) (at level 30) : type_scope.
#[global] Notation "Γ ⊆ Δ" := (assignment has Γ%ctx Δ%ctx) (at level 30) : type_scope.
#[global] Notation "Γ =[ F ]> Δ" := (assignment F Γ%ctx Δ%ctx) (at level 30) : type_scope.
#[global] Notation "a ∘⊆ b" := (r_comp a%ctx b%ctx) (at level 30).
#[global] Notation "[ u , v ]" := (s_cat u v) (at level 14).
#[global] Notation "u ≡ₐ v" := (ass_eq _ _ u v) (at level 50).

#[global] Infix "⊛ᵣ" := s_ren (at level 14).
