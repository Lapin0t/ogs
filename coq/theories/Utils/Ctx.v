(*|
Contexts
=========

---

nil : ctx
++ : ctx -> ctx -> ctx

nil-cat : nil ++ Γ = Γ
cat-nil : Γ ++ nil = Γ

⊆ : ctx -> ctx -> Type

nil-lt : nil ⊆ Γ
nil-gt :

cat⊆ :

---

=> : ctx -> ctx -> Type

s-nil : nil => Γ
s-cat : Γ1 => Δ -> Γ2 => Δ -> (Γ1 ++ Γ2) => Δ

s-nil-eq : (u : nil => Γ) -> u ~~ s-nil
s-cat-eq : (a : Γ1 => Δ) (b : Γ2 => Δ) (u : (Γ1 ++ Γ2) => Δ)


.. coq:: none
|*)

From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.

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

Equations c_length {X} (Γ : ctx X) : nat :=
  c_length ∅%ctx := O ;
  c_length (Γ ▶ _)%ctx := Datatypes.S (c_length Γ) .

Equations ccat {X} : ctx X -> ctx X -> ctx X :=
  ccat Γ ∅        := Γ ;
  ccat Γ (Δ ▶ x) := (ccat Γ Δ) ▶ x .
#[global] Notation "Γ +▶ Δ" := (ccat Γ%ctx Δ%ctx) (at level 50, left associativity) : ctx_scope.

Lemma ccat_empty_l {X} {Γ : ctx X} : (∅ +▶ Γ)%ctx = Γ.
  induction Γ; [ reflexivity | ].
  cbn; f_equal; apply IHΓ.
Qed.

Lemma ccat_empty_r {X} {Γ : ctx X} : (Γ +▶ ∅)%ctx = Γ.
  reflexivity.
Qed.

Equations c_map {X Y} : (X -> Y) -> ctx X -> ctx Y :=
  c_map f ∅        := ∅ ;
  c_map f (Γ ▶ x) := c_map f Γ ▶ f x .

Section lemma.
Context {X : Type}.

Equations join : ctx (ctx X) -> ctx X :=
  join (∅)       := ∅ ;
  join (Γ ▶ xs) := join Γ +▶ xs .

(*|
Two mutually recursive functions, defined at once via a boolean argument.
Given a context of contexts, we join them, but by keeping only half the contexts:
the ones in odd positions (join_odd) respectively in even positions (join_even)
|*)
Equations join_even_odd_aux : bool -> ctx (ctx X) -> ctx X :=
  join_even_odd_aux b     (∅)       := ∅ ;
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
Derive Signature NoConfusion for has.

(*|
Assignment
------------
We distinguish assignments, mapping variables in a context to terms, from substitutions, applying an assignment
to a term. Assignments are again intrinsically typed, mapping variables of a context Γ to open terms with
variables in Δ.
|*)
Definition assignment (F : ctx X -> X -> Type) (Γ Δ : ctx X) := has Γ ⇒ᵢ F Δ.
Notation "Γ =[ F ]> Δ" := (assignment F Γ%ctx Δ%ctx) (at level 30).

Definition ass_eq {F : ctx X -> X -> Type} Γ Δ : relation (Γ =[F]> Δ) :=
  dpointwise_relation (fun x => pointwise_relation _ eq)%signature.

Notation "u ≡ₐ v" := (ass_eq _ _ u v) (at level 50).

#[global] Instance ass_equivalence {F Γ Δ} : Equivalence (@ass_eq F Γ Δ).
  econstructor.
  - now intros u ? i.
  - intros u h ? ? i; symmetry; now apply (H _ i).
  - intros u v w h1 h2 ? i; transitivity (v _ i); [ now apply h1 | now apply h2 ].
Qed.

(*|
Renaming
---------
Context inclusion is defined as an assignment of variables in Γ to variables in Δ. This inclusion can be thought
of as the assignment whose associated substitution is a renaming of assignments.
|*)
Notation "Γ ⊆ Δ" := (assignment has Γ%ctx Δ%ctx) (at level 30).

Definition s_map {F G Γ Δ1 Δ2} (f : F Δ1 ⇒ᵢ G Δ2) (u : Γ =[F]> Δ1) : Γ =[G]> Δ2 :=
  fun _ i => f _ (u _ i) .

Definition s_ren {F Γ1 Γ2 Γ3} (a : Γ2 =[F]> Γ3) (b : Γ1 ⊆ Γ2) : Γ1 =[F]> Γ3 :=
  s_map a b .
Infix "⊛ᵣ" := s_ren (at level 14).

#[global] Instance s_ren_proper {F Γ1 Γ2 Γ3}
          : Proper (ass_eq _ _ ==> ass_eq _ _ ==> ass_eq _ _)
                   (@s_ren F Γ1 Γ2 Γ3) .
  intros ? ? H1 ? ? H2 ? i; unfold s_ren, s_map; now rewrite H1, H2.
Qed.

Equations s_empty {F Γ} : ∅ =[F]> Γ :=
  s_empty x (!).

(*|
The identity inclusion, whose renaming is the identity.
|*)
Definition r_id {Γ} : Γ ⊆ Γ := fun _ i => i .

Lemma s_ren_id {F Γ1 Γ2} (a : Γ1 =[F]> Γ2) : a ⊛ᵣ r_id ≡ₐ a .
  reflexivity.
Qed.

Definition s_pop {Γ x} : Γ ⊆ (Γ ▶ x) := fun _ i => pop i.

(*|
Composition of context inclusion induces a composed renaming.
|*)
Lemma s_ren_comp {F Γ1 Γ2 Γ3 Γ4} (u : Γ3 =[F]> Γ4) (v : Γ2 ⊆ Γ3) (w : Γ1 ⊆ Γ2)
      : u ⊛ᵣ (v ⊛ᵣ w) ≡ₐ (u ⊛ᵣ v) ⊛ᵣ w.
  reflexivity.
Qed.

(* helper for defining various shiftings *)
Equations s_append {Γ Δ : ctx X} {F : ctx X -> X -> Type} {a}
  : Γ =[F]> Δ -> F Δ a -> (Γ ▶ a) =[F]> Δ :=
  s_append s z _ top     := z ;
  s_append s z _ (pop i) := s _ i .

#[global] Instance s_append_eq {Γ Δ : ctx X} {F : ctx X -> X -> Type} {a}
          : Proper (ass_eq _ _ ==> eq ==> ass_eq _ _) (@s_append Γ Δ F a).
  intros f g H1 x y H2 u i; dependent elimination i; [ exact H2 | apply H1 ].
Qed.

Definition r_shift {Γ Δ : ctx X} {a} (f : Γ ⊆ Δ) : (Γ ▶ a) ⊆ (Δ ▶ a)
  := s_append (s_ren s_pop f) top.

Lemma r_shift_comp {Γ1 Γ2 Γ3 : ctx X} {a} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2)
  : r_shift (a:=a) (f1 ⊛ᵣ f2) ≡ₐ r_shift (a:=a) f1 ⊛ᵣ r_shift (a:=a) f2 .
  intros x i; dependent elimination i; reflexivity.
Qed.

Lemma r_shift_id {Γ : ctx X} {a} : @r_shift Γ Γ a r_id ≡ₐ r_id .
  intros x i; dependent elimination i; reflexivity.
Qed.

#[global] Instance r_shift_eq {Γ Δ : ctx X} {a} : Proper (ass_eq _ _ ==> ass_eq _ _) (@r_shift Γ Δ a).
  intros f1 f2 H x i; unfold r_shift.
  dependent elimination i; [ reflexivity | ].
  unfold s_ren, s_map, s_pop; cbn; f_equal; apply H.
Qed.

Definition r_shift2 {Γ Δ : ctx X} {a b} (f : Γ ⊆ Δ) : (Γ ▶ a ▶ b) ⊆ (Δ ▶ a ▶ b)
  := r_shift (r_shift f).

Equations r_shift_n {Γ Δ : ctx X} (xs : ctx X) (f : Γ ⊆ Δ) : (Γ +▶ xs) ⊆ (Δ +▶ xs) :=
  r_shift_n ∅         f := f ;
  r_shift_n (xs ▶ _) f := r_shift (r_shift_n xs f) .

Inductive cover : ctx X -> ctx X -> ctx X -> Type :=
| CNil :                                  cover ∅         ∅         ∅
| CLeft  {x xs ys zs} : cover xs ys zs -> cover (xs ▶ x) ys        (zs ▶ x)
| CRight {x xs ys zs} : cover xs ys zs -> cover xs        (ys ▶ x) (zs ▶ x)
.
Notation "a ⊎ b ≡ c" := (cover a b c) (at level 30).
Derive Signature NoConfusion for cover.

Equations cover_swap {Γ1 Γ2 Γ3} : Γ1 ⊎ Γ2 ≡ Γ3 -> Γ2 ⊎ Γ1 ≡ Γ3 :=
  cover_swap CNil       := CNil ;
  cover_swap (CLeft p)  := CRight (cover_swap p) ;
  cover_swap (CRight p) := CLeft (cover_swap p) .

Lemma cover_swap_swap {Γ1 Γ2 Γ3} (p : Γ1 ⊎ Γ2 ≡ Γ3) : cover_swap (cover_swap p) = p.
  dependent induction p; cbn; f_equal; eauto.
Qed.

Equations cover_nil_r xs : xs ⊎ ∅ ≡ xs :=
  cover_nil_r ∅         := CNil ;
  cover_nil_r (xs ▶ _) := CLeft (cover_nil_r xs) .
#[global] Arguments cover_nil_r {xs}.

Equations cover_nil_l xs : ∅ ⊎ xs ≡ xs :=
  cover_nil_l ∅         := CNil ;
  cover_nil_l (xs ▶ _) := CRight (cover_nil_l xs) .
#[global] Arguments cover_nil_l {xs}.

Equations cover_cat {xs} ys : xs ⊎ ys ≡ (xs +▶ ys) :=
  cover_cat ∅         := cover_nil_r ;
  cover_cat (ys ▶ _) := CRight (cover_cat ys) .
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
  ext_cover_l ∅        c := c ;
  ext_cover_l (Γ ▶ _) c := CLeft (ext_cover_l Γ c) .

Equations ext_cover_r {xs ys zs} (Γ : ctx X)
          : xs ⊎ ys ≡ zs
          -> xs ⊎ (ys +▶ Γ) ≡ (zs +▶ Γ) :=
  ext_cover_r ∅        c := c ;
  ext_cover_r (Γ ▶ _) c := CRight (ext_cover_r Γ c) .

Equations r_cover_l {xs ys zs} : xs ⊎ ys ≡ zs -> xs ⊆ zs :=
  r_cover_l (CNil)     := s_empty ;
  r_cover_l (CLeft c)  := r_shift (r_cover_l c) ;
  r_cover_l (CRight c) := s_ren s_pop (r_cover_l c) .

Lemma r_cover_l_inj {xs ys zs} (p : xs ⊎ ys ≡ zs) [x] (i j : xs ∋ x)
                    (H : r_cover_l p _ i = r_cover_l p _ j) : i = j .
  induction p.
  - dependent elimination i.
  - dependent elimination i; dependent elimination j; try now inversion H.
    dependent induction H.
    f_equal; now apply IHp.
  - dependent induction H.
    now apply IHp.
Qed.

Equations r_cover_r {xs ys zs} : xs ⊎ ys ≡ zs -> ys ⊆ zs :=
  r_cover_r (CNil)     := s_empty ;
  r_cover_r (CLeft c)  := s_ren s_pop (r_cover_r c) ;
  r_cover_r (CRight c) := r_shift (r_cover_r c) .

Lemma r_cover_r_inj {xs ys zs} (p : xs ⊎ ys ≡ zs) [x] (i j : ys ∋ x)
                    (H : r_cover_r p _ i = r_cover_r p _ j) : i = j .
  induction p.
  - dependent elimination i.
  - dependent induction H.
    now apply IHp.
  - dependent elimination i; dependent elimination j; try now inversion H.
    dependent induction H.
    f_equal; now apply IHp.
Qed.

Lemma r_cover_disj {xs ys zs} (p : xs ⊎ ys ≡ zs) [x] (i : xs ∋ x) (j : ys ∋ x)
  (H : r_cover_l p _ i = r_cover_r p _ j) : T0.
  induction p.
  - inversion i.
  - dependent elimination i.
    + inversion H.
    + cbn in H; unfold s_ren, s_map, s_pop in H.
      remember (r_cover_l p x2 h); dependent elimination H.
      now apply (IHp h j).
  - dependent elimination j.
    + inversion H.
    + cbn in H; unfold s_ren, s_map, s_pop in H.
      remember (r_cover_l p x2 i); dependent elimination H.
      now apply (IHp i h).
Qed.

Variant cover_view {xs ys zs} (p : xs ⊎ ys ≡ zs) [x] : zs ∋ x -> Type :=
| CLeftV  (i : xs ∋ x) : cover_view p (r_cover_l p _ i)
| CRightV (j : ys ∋ x) : cover_view p (r_cover_r p _ j)
.
#[global] Arguments CLeftV {xs ys zs p x}.
#[global] Arguments CRightV {xs ys zs p x}.

Definition cover_split {xs ys zs} (p : xs ⊎ ys ≡ zs) [x] (i : zs ∋ x) : cover_view p i.
  revert xs ys p; induction zs; intros xs ys p; dependent elimination i.
  + dependent elimination p; [ refine (CLeftV top) | refine (CRightV top) ].
  + dependent elimination p as [ CLeft p | CRight p ].
    * destruct (IHzs h _ _ p); [ refine (CLeftV (pop i)) | refine (CRightV j) ].
    * destruct (IHzs h _ _ p); [ refine (CLeftV i) | refine (CRightV (pop j)) ].
Defined.

Definition cat_split {xs ys} [x] (i : (xs +▶ ys) ∋ x) : cover_view cover_cat i :=
  cover_split cover_cat i.

Definition s_cover {F Γ1 Γ2 Γ3 Δ} : Γ1 ⊎ Γ2 ≡ Γ3 -> Γ1 =[F]> Δ -> Γ2 =[F]> Δ -> Γ3 =[F]> Δ :=
  fun p u v _ i => match cover_split p i with
                 | CLeftV i  => u _ i
                 | CRightV j => v _ j
                 end .
Notation "[ u , H , v ]" := (s_cover H u v) (at level 9).

#[global] Instance s_cover_proper {F Γ1 Γ2 Γ3 Δ} (H : Γ1 ⊎ Γ2 ≡ Γ3)
          : Proper (ass_eq _ _ ==> ass_eq _ _ ==> ass_eq _ _) (s_cover (F:=F) (Δ:=Δ) H).
  intros ? ? H1 ? ? H2 ? i; unfold s_cover.
  destruct (cover_split H i); [ now apply H1 | now apply H2 ].
Qed.

Definition s_cat {F Γ1 Γ2 Δ} : Γ1 =[F]> Δ -> Γ2 =[F]> Δ -> (Γ1 +▶ Γ2) =[F]> Δ :=
  s_cover cover_cat .
Notation "[ u , v ]" := (s_cat u v) (at level 9).

Definition r_concat_l {Γ Δ : ctx X} : Γ ⊆ (Γ +▶ Δ) :=
  r_cover_l cover_cat .

Definition r_cover_l_nil {Γ} : r_cover_l cover_nil_r ≡ₐ @r_id Γ .
  intros ? i; induction Γ; dependent elimination i.
  - reflexivity.
  - cbn; unfold r_id, s_ren, s_map, s_pop.
    f_equal; apply (IHΓ h).
Qed.

Definition r_concat_r {Γ Δ : ctx X} : Δ ⊆ (Γ +▶ Δ) :=
  r_cover_r cover_cat .

Definition r_concat3_1 {Γ Δ ϒ : ctx X} : (Γ +▶ Δ) ⊆ (Γ +▶ (Δ +▶ ϒ)) :=
  [ r_concat_l , r_concat_r ⊛ᵣ r_concat_l ].

Definition r_concat3_2 {Γ Δ ϒ : ctx X} : (Γ +▶ ϒ) ⊆ (Γ +▶ (Δ +▶ ϒ)) :=
  [ r_concat_l , r_concat_r ⊛ᵣ r_concat_r ].

Definition r_concat3_3 {Γ Δ ϒ : ctx X} : (Δ +▶ ϒ) ⊆ ((Γ +▶ Δ) +▶ ϒ) :=
  [ r_concat_l ⊛ᵣ r_concat_r , r_concat_r ].

Lemma s_eq_cover_empty_r {F Γ1 Δ} (u : Γ1 =[F]> Δ) : s_cat u s_empty ≡ₐ u.
  intros ? i; unfold s_cat, s_cover.
  destruct (cover_split cover_cat i); cbn.
  + rewrite r_cover_l_nil; eauto.
  + inversion j.
Qed.

Lemma s_eq_cover_l {F Γ1 Γ2 Γ3 Δ} (H : Γ1 ⊎ Γ2 ≡ Γ3) (u : Γ1 =[F]> Δ) (v : Γ2 =[F]> Δ)
      : [ u , H , v ] ⊛ᵣ r_cover_l H ≡ₐ u.
  intros ? i.
  unfold s_cover, s_ren, s_map.
  remember (r_cover_l H a i) as ii.
  destruct (cover_split H ii).
  - f_equal; exact (r_cover_l_inj H _ _ Heqii).
  - destruct (r_cover_disj H i j (eq_sym Heqii)).
Qed.

Lemma s_eq_cat_l {F Γ1 Γ2 Δ} (u : Γ1 =[F]> Δ) (v : Γ2 =[F]> Δ)
      : [ u , v ] ⊛ᵣ r_concat_l ≡ₐ u.
  apply s_eq_cover_l.
Qed.

Lemma s_eq_cover_r {F Γ1 Γ2 Γ3 Δ} (H : Γ1 ⊎ Γ2 ≡ Γ3) (u : Γ1 =[F]> Δ) (v : Γ2 =[F]> Δ)
      : [ u , H , v ] ⊛ᵣ r_cover_r H ≡ₐ v.
  intros ? j.
  unfold s_cover, s_ren, s_map.
  remember (r_cover_r H a j) as jj.
  destruct (cover_split H jj).
  - destruct (r_cover_disj H i j Heqjj).
  - f_equal; exact (r_cover_r_inj H _ _ Heqjj).
Qed.

Lemma s_eq_cat_r {F Γ1 Γ2 Δ} (u : Γ1 =[F]> Δ) (v : Γ2 =[F]> Δ)
      : [ u , v ] ⊛ᵣ r_concat_r ≡ₐ v.
  apply s_eq_cover_r.
Qed.

Lemma cat_split_l {Γ1 Γ2} {x : X} (i : Γ1 ∋ x) : cat_split (r_concat_l (Δ:=Γ2) _ i) = CLeftV i .
  pose (uu := cat_split (r_concat_l (Δ:=Γ2) x i)); fold uu.
  dependent induction uu.
  - apply r_cover_l_inj in x1; rewrite x1 in x.
    dependent destruction x; now simpl_depind.
  - symmetry in x1; apply r_cover_disj in x1; destruct x1.
Qed.

Lemma cat_split_r {Γ1 Γ2} {x : X} (i : Γ2 ∋ x) : cat_split (r_concat_r (Γ:=Γ1) _ i) = CRightV i .
  pose (uu := cat_split (r_concat_r (Γ:=Γ1) x i)); fold uu.
  dependent induction uu.
  - apply r_cover_disj in x1; destruct x1.
  - apply r_cover_r_inj in x1; rewrite x1 in x.
    dependent destruction x; now simpl_depind.
Qed.

Lemma s_eq_cover_uniq {F Γ1 Γ2 Γ3 Δ} (H : Γ1 ⊎ Γ2 ≡ Γ3)
       (u : Γ1 =[F]> Δ) (v : Γ2 =[F]> Δ) (w : Γ3 =[F]> Δ)
       (H1 : u ≡ₐ w ⊛ᵣ r_cover_l H)
       (H2 : v ≡ₐ w ⊛ᵣ r_cover_r H)
       : [ u , H , v ] ≡ₐ w .
  intros ? i; unfold s_cover.
  destruct (cover_split H i); [ exact (H1 a i) | exact (H2 a j) ].
Qed.

Lemma s_eq_cover_map {F G Γ1 Γ2 Γ3 Δ1 Δ2} (f : F Δ1 ⇒ᵢ G Δ2)
  (H : Γ1 ⊎ Γ2 ≡ Γ3) (u : Γ1 =[F]> Δ1) (v : Γ2 =[F]> Δ1)
  : s_map f ([ u , H , v ]) ≡ₐ ([ s_map f u , H , s_map f v ]).
  symmetry; apply s_eq_cover_uniq; intros ? i; unfold s_ren, s_map; f_equal; symmetry.
  now apply s_eq_cover_l.
  now apply s_eq_cover_r.
Qed.

Lemma s_eq_cover_id {Γ1 Γ2 Γ3} (H : Γ1 ⊎ Γ2 ≡ Γ3)
      : [ r_cover_l H , H , r_cover_r H ] ≡ₐ r_id .
  now apply s_eq_cover_uniq.
Qed.

Definition r_assoc_r {Γ1 Γ2 : ctx X} Γ3 : (Γ1 +▶ Γ2 +▶ Γ3) ⊆ (Γ1 +▶ (Γ2 +▶ Γ3))
  := [ r_concat3_1 , r_concat_r ⊛ᵣ r_concat_r ].

Definition r_assoc_l {Γ1 Γ2 : ctx X} Γ3 : (Γ1 +▶ (Γ2 +▶ Γ3)) ⊆ (Γ1 +▶ Γ2 +▶ Γ3)
  := [ r_concat_l ⊛ᵣ r_concat_l , r_concat3_3 ] .

Lemma r_assoc_rl {Γ1 Γ2 Γ3 : ctx X} : @r_assoc_r Γ1 Γ2 Γ3 ⊛ᵣ @r_assoc_l Γ1 Γ2 Γ3 ≡ₐ r_id .
  unfold r_assoc_r, r_assoc_l, r_concat3_1, r_concat3_3.
  etransitivity; [ unfold s_ren at 1; apply s_eq_cover_map; change (s_map ?a ?b) with (s_ren a b) | ].
  etransitivity; [ eapply s_cover_proper; [ now rewrite s_ren_comp, 2 s_eq_cat_l | ] | ].
  - etransitivity; [ unfold s_ren at 1; apply s_eq_cover_map; change (s_map ?a ?b) with (s_ren a b) | ].
    eapply s_cover_proper.
    * now rewrite s_ren_comp, s_eq_cat_l, s_eq_cat_r.
    * now rewrite s_eq_cat_r.
  - apply s_eq_cover_uniq; [ reflexivity | ].
    unfold s_ren; rewrite <- s_eq_cover_map; change (s_map ?a ?b) with (s_ren a b).
    now rewrite s_eq_cover_id.
Qed.

Lemma r_assoc_lr {Γ1 Γ2 Γ3 : ctx X} : @r_assoc_l Γ1 Γ2 Γ3 ⊛ᵣ @r_assoc_r Γ1 Γ2 Γ3 ≡ₐ r_id .
  unfold r_assoc_r, r_assoc_l, r_concat3_1, r_concat3_3.
  etransitivity; [ unfold s_ren at 1; apply s_eq_cover_map | ]; change (s_map ?a ?b) with (s_ren a b) .
  etransitivity; [ eapply s_cover_proper; [ | now rewrite s_ren_comp, 2 s_eq_cat_r ] | ].
  - etransitivity; [ unfold s_ren at 1; apply s_eq_cover_map | ]; change (s_map ?a ?b) with (s_ren a b) .
    eapply s_cover_proper.
    * now rewrite s_eq_cat_l.
    * now rewrite s_ren_comp, s_eq_cat_r, s_eq_cat_l.
  - apply s_eq_cover_uniq; [ | reflexivity ].
    unfold s_ren; rewrite <- s_eq_cover_map; change (s_map ?a ?b) with (s_ren a b).
    now rewrite s_eq_cover_id.
Qed.

End lemma.

Definition map_has {X Y} (f : X -> Y) (Γ : ctx X)
  {x} (i : has Γ x) : has (c_map f Γ) (f x).
  induction Γ; dependent elimination i.
  - exact top.
  - exact (pop (IHΓ h)).
Defined.

Variant has_map_view {X Y} (f : X -> Y) Γ : forall y, has (c_map f Γ) y -> Type :=
| MapV {x} (i : has Γ x) : has_map_view f Γ _ (map_has f Γ i)
.
#[global] Arguments MapV {X Y f Γ x}.

Definition view_has_map {X Y} (f : X -> Y) Γ
  [y] (i : has (c_map f Γ) y) : has_map_view f Γ y i.
induction Γ; dependent elimination i.
- exact (MapV top).
- destruct (IHΓ h); exact (MapV (pop i)).
Defined.

Lemma map_cat {X Y} (f : X -> Y) (Γ Δ : ctx X)
  : c_map f (Γ +▶ Δ) = (c_map f Γ +▶ c_map f Δ)%ctx.
  induction Δ; [ reflexivity | ].
  cbn; f_equal; exact IHΔ.
Qed.

#[global] Notation join_even := (join_even_odd_aux true) .
#[global] Notation join_odd := (join_even_odd_aux false) .
#[global] Notation "Γ ∋ x" := (has Γ%ctx x) (at level 30) : type_scope.
#[global] Notation "a ⊎ b ≡ c" := (cover a%ctx b%ctx c%ctx) (at level 30) : type_scope.
#[global] Notation "Γ ⊆ Δ" := (assignment has Γ%ctx Δ%ctx) (at level 30) : type_scope.
#[global] Notation "Γ =[ F ]> Δ" := (assignment F Γ%ctx Δ%ctx) (at level 30) : type_scope.
#[global] Notation "[ u , v ]" := (s_cat u v) (at level 14).
#[global] Notation "u ≡ₐ v" := (ass_eq _ _ u v) (at level 50).

#[global] Infix "⊛ᵣ" := s_ren (at level 14).

Section any.
  Context {X : Type}.

Variant any (P : X -> Type) (xs : ctx X) : Type :=
| Any {x} : xs ∋ x -> P x -> any P xs
.
#[global] Arguments Any {P xs x} i p.
Derive NoConfusion for any.

Equations any_el {P xs} : any P xs -> X :=
  any_el (@Any _ _ x _ _) := x .

Equations any_coh {P xs} (a : any P xs) : P (any_el a) :=
  any_coh (Any _ p) := p .

Equations any_elim {P} {A : forall x, P x -> Type} (f : forall x p, A x p)
          xs (a : any P xs) : A (any_el a) (any_coh a) :=
  any_elim f xs (Any _ p) := f _ p .

Definition allS (R : X -> SProp) (Γ : ctx X) : SProp := forall x, Γ ∋ x -> R x.
Definition ctx_s (R : X -> SProp) : Type := sigS (allS R).
Definition coe_ctx {R} : ctx_s R -> ctx X := sub_elt.
#[global] Coercion coe_ctx : ctx_s >-> ctx.

Program Definition snil {R} : ctx_s R := {| sub_elt := ∅%ctx |}.
Next Obligation. intros ? i; inversion i. Qed.

Program Definition scon {R} (Γ : ctx_s R) (x : sigS R) : ctx_s R := {| sub_elt := (Γ ▶ x.(sub_elt))%ctx |}.
Next Obligation.
  intros ? i; remember (Γ ▶ x.(sub_elt))%ctx as Δ.
  destruct i; injection HeqΔ as -> ->.
  exact x.(sub_prf).
  exact (Γ.(sub_prf) _ i).
Qed.

Definition scat {R} (Γ Δ : ctx_s R) : ctx_s R :=
  {| sub_prf := (fun x i => match cat_split i with
                          | CLeftV i => Γ.(sub_prf) x i
                          | CRightV j => Δ.(sub_prf) x j
                          end) : allS R (Γ +▶ Δ) |} .

Definition s_elt_upg {R} {Γ : ctx_s R} {x : X} (i : Γ ∋ x) : sigS R :=
  {| sub_prf := Γ.(sub_prf) x i |}.

Definition s_var_upg {R} {Γ : ctx_s R} {x : X} (i : Γ ∋ x) : Γ ∋ (s_elt_upg i).(sub_elt)
  := i.

Equations ctx_s_map' {Y} {R : X -> SProp} (f : sigS R -> Y) Γ (H : forall x, Γ ∋ x -> R x) : ctx Y :=
  ctx_s_map' f (∅)      H := ∅ ;
  ctx_s_map' f (Γ ▶ _) H := ctx_s_map' f Γ (fun _ i => H _ (pop i))
                              ▶ f {| sub_prf := H _ top |} .

Definition ctx_s_map {Y} {R : X -> SProp} (f : sigS R -> Y) (Γ : ctx_s R) : ctx Y :=
  ctx_s_map' f Γ.(sub_elt) Γ.(sub_prf) .

Definition ctx_s_to_ctx {R : X -> SProp} (Γ : ctx_s R) : ctx (sigS R) :=
  ctx_s_map (fun x => x) Γ.

Equations s_map_has' {Y} {R : X -> SProp} (f : sigS R -> Y) Γ (H : forall x, Γ ∋ x -> R x)
          {x} (i : Γ ∋ x) : ctx_s_map' f Γ H ∋ f {| sub_prf := H _ i |} :=
  s_map_has' f (Γ ▶ _) H top     := top ;
  s_map_has' f (Γ ▶ _) H (pop i) := pop (s_map_has' f Γ _ i) .

Definition s_map_has {Y} {R : X -> SProp} (f : sigS R -> Y) (Γ : ctx_s R)
  {x} (i : Γ ∋ x) : ctx_s_map f Γ ∋ f (s_elt_upg i) :=
  s_map_has' f Γ.(sub_elt) Γ.(sub_prf) i.

Variant s_has_map_view {Y R} (f : sigS R -> Y) Γ : forall y, ctx_s_map f Γ ∋ y -> Type :=
| SMapV {x} (i : Γ ∋ x) : s_has_map_view f Γ _ (s_map_has f Γ i)
.
#[global] Arguments SMapV {Y R f Γ x}.

Definition view_s_has_map {Y R} (f : sigS R -> Y) Γ
  [y] (i : ctx_s_map f Γ ∋ y) : s_has_map_view f Γ y i.
destruct Γ as [ Γ H ].
induction Γ; dependent elimination i.
- exact (@SMapV _ _ _ {| sub_prf := H |} _ top).
- destruct (IHΓ (fun _ i => H _ (pop i)) h).
  exact (@SMapV _ _ _ {| sub_prf := H |} _ (pop i)).
Defined.

Lemma ctx_s_to_ctx_eq {R : X -> SProp} (Γ : ctx_s R)
      : (Γ : ctx X) = c_map sub_elt (ctx_s_to_ctx Γ).
  destruct Γ as [ Γ H ].
  induction Γ; [ reflexivity | ].
  cbn; f_equal; apply IHΓ.
Qed.

Variant any_s {R : X -> SProp} (P : sigS R -> Type) (xs : ctx_s R) : Type :=
| AnyS {x} : xs ∋ x.(sub_elt) -> P x -> any_s P xs
.
#[global] Arguments AnyS {R P xs x} i p.
Derive NoConfusion for any_s.

Equations any_s_el {R P xs} : @any_s R P xs -> sigS R :=
  any_s_el (@AnyS _ _ _ x _ _) := x .

Equations any_s_coh {R P xs} (a : @any_s R P xs) : P (any_s_el a) :=
  any_s_coh (AnyS _ p) := p .

Equations any_s_elim {R P} {A : forall x, P x -> Type} (f : forall x p, A x p)
          {xs} (a : @any_s R P xs) : A (any_s_el a) (any_s_coh a) :=
  any_s_elim f (AnyS _ p) := f _ p .

End any.

#[global] Notation "∅ₛ" := (snil) : ctx_scope.
#[global] Notation "Γ ▶ₛ x" := (scon Γ%ctx x) (at level 40, left associativity) : ctx_scope.
#[global] Notation "Γ +▶ₛ Δ" := (scat Γ%ctx Δ%ctx) (at level 50, left associativity) : ctx_scope.
