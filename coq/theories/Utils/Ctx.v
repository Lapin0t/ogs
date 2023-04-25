From Coq Require Import Program.Equality.
From Equations Require Import Equations.
Set Equations Transparent.

Import EqNotations.

From Coinduction Require Import lattice.

From OGS Require Import Utils.
From OGS Require Import Utils.Prelude.

From Coq.Vectors Require Fin.

Definition fin := Fin.t.
Notation F0 := (Fin.F1).
Notation FS := (Fin.FS).

Inductive ctx (X : Type) : Type :=
| cnil : ctx X
| ccon : ctx X -> X -> ctx X
.
Arguments cnil {X}.
Arguments ccon {X} Γ x.
Derive NoConfusion for ctx.

#[global] Declare Scope ctx_scope.
#[global] Delimit Scope ctx_scope with ctx.
#[global] Bind Scope ctx_scope with ctx.

#[global] Notation "∅" := (cnil) : ctx_scope.
#[global] Notation "Γ ▶ x" := (ccon Γ%ctx x) (at level 40, left associativity) : ctx_scope.

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

Equations join : ctx (ctx X) -> ctx X :=
  join (∅)     := ∅ ;
  join (Γ ▶ xs) := join Γ +▶ xs .

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
    
Inductive has : ctx X -> X -> Type :=
| top {Γ x} : has (Γ ▶ x) x
| pop {Γ x y} : has Γ x -> has (Γ ▶ y) x.
Notation "Γ ∋ x" := (has Γ%ctx x) (at level 30).
Derive Signature for has.

Equations length : ctx X -> nat :=
  length ∅       := O ;
  length (Γ ▶ x) := S (length Γ) .

Equations get (xs : ctx X) : fin (length xs) -> X :=
  get (Γ ▶ x) (F0)   := x ;
  get (Γ ▶ x) (FS i) := get Γ i .
Notation "Γ .[ i ]" := (get Γ%ctx i) (at level 30).

Definition substitution (F : ctx X -> X -> Type) (Γ Δ : ctx X) := forall x, Γ ∋ x -> F Δ x.
Notation "Γ ⊆ Δ" := (substitution has Γ%ctx Δ%ctx) (at level 30).
Notation "Γ =[ F ]> Δ" := (substitution F Γ%ctx Δ%ctx) (at level 30).

Definition sub_eq {F : ctx X -> X -> Type} Γ Δ : relation (Γ =[F]> Δ) :=
  dpointwise_relation (fun x => pointwise_relation _ eq)%signature.

#[global] Instance sub_equivalence {F Γ Δ} : Equivalence (@sub_eq F Γ Δ).
econstructor.
- intros u ? i; reflexivity.
- intros u h ? i ?; symmetry; now apply (H i a).
- intros u v w h1 h2 ? i. transitivity (v a i); [ now apply h1 | now apply h2 ].
Qed.

Definition s_ren {F Γ1 Γ2 Γ3} (a : Γ2 =[F]> Γ3) (b : Γ1 ⊆ Γ2) : Γ1 =[F]> Γ3 :=
  fun _ i => a _ (b _ i).

#[global] Instance s_ren_proper {F Γ1 Γ2 Γ3} : Proper (sub_eq _ _ ==> sub_eq _ _ ==> sub_eq _ _) (@s_ren F Γ1 Γ2 Γ3) .
Proof.
  intros ? ? H1 ? ? H2 ? i.
  unfold s_ren; now rewrite H2, H1.
Qed.

Definition r_id {Γ} : Γ ⊆ Γ := fun _ i => i .
Definition r_comp {Γ1 Γ2 Γ3} (a : Γ2 ⊆ Γ3) (b : Γ1 ⊆ Γ2) : Γ1 ⊆ Γ3 :=
  s_ren a b.

Lemma s_ren_comp {F Γ1 Γ2 Γ3 Γ4} (u : Γ3 =[F]> Γ4) (v : Γ2 ⊆ Γ3) (w : Γ1 ⊆ Γ2)
      : sub_eq _ _ (s_ren u (r_comp v w)) (s_ren (s_ren u v) w).
Proof. reflexivity. Qed.

Definition r_pop {Γ : ctx X} {x : X} : Γ ⊆ (Γ ▶ x) := fun _ i => pop i.

Equations has_get (Γ : ctx X) i : Γ ∋ (Γ.[i]) :=
  has_get (Γ ▶ x) F0     := top ;
  has_get (Γ ▶ x) (FS i) := pop (has_get Γ i) .

Equations has_index {Γ : ctx X} {x} : Γ ∋ x -> fin (length Γ) :=
  has_index top     := F0 ;
  has_index (pop p) := FS (has_index p) .

Equations get_has {Γ : ctx X} {x} (p : Γ ∋ x) : Γ.[has_index p] = x :=
  get_has top     := eq_refl ;
  get_has (pop i) := get_has i .

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
Arguments CNil.
Arguments CLeft {x xs ys zs} c.
Arguments CRight {x xs ys zs} c.
Notation "a ⊎ b ≡ c" := (cover a b c) (at level 30).
Derive NoConfusion for cover.

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

Equations cat_cover {xs0 xs1 ys0 ys1 zs0 zs1} : xs0 ⊎ ys0 ≡ zs0 -> xs1 ⊎ ys1 ≡ zs1
    -> (xs0 +▶ xs1) ⊎ (ys0 +▶ ys1) ≡ (zs0 +▶ zs1) :=
  cat_cover a (CNil)     := a ;
  cat_cover a (CLeft b)  := CLeft (cat_cover a b) ;
  cat_cover a (CRight b) := CRight (cat_cover a b) .

Equations ext_cover_l {xs ys zs} (u : ctx X) : xs ⊎ ys ≡ zs -> (xs +▶ u) ⊎ ys ≡ (zs +▶ u) :=
  ext_cover_l ∅ c := c ; 
  ext_cover_l (uu ▶ _) c := CLeft (ext_cover_l uu c) .

Equations ext_cover_r {xs ys zs} (u : ctx X) : xs ⊎ ys ≡ zs -> xs ⊎ (ys +▶ u) ≡ (zs +▶ u) :=
  ext_cover_r ∅ c := c ; 
  ext_cover_r (uu ▶ _) c := CRight (ext_cover_r uu c) .

Equations r_cover_l {xs ys zs} (p : xs ⊎ ys ≡ zs) : xs ⊆ zs :=
  r_cover_l (CLeft c)  _ top     := top ;
  r_cover_l (CLeft c)  _ (pop i) := pop (r_cover_l c _ i) ;
  r_cover_l (CRight c) _ i       := pop (r_cover_l c _ i) .

Equations r_cover_r {xs ys zs} (p : xs ⊎ ys ≡ zs) : ys ⊆ zs :=
  r_cover_r (CLeft c)  _ i       := pop (r_cover_r c _ i) ;
  r_cover_r (CRight c) _ top     := top ;
  r_cover_r (CRight c) _ (pop i) := pop (r_cover_r c _ i) .

Equations cover_split {xs ys zs} (p : xs ⊎ ys ≡ zs) [x] : zs ∋ x -> xs ∋ x + ys ∋ x:=
  cover_split (CLeft c)  top     := inl top ;
  cover_split (CRight c) top     := inr top ;
  cover_split (CLeft c)  (pop i) with cover_split c i :=
      { | inl j := inl (pop j) ;
        | inr j := inr j } ;
  cover_split (CRight c) (pop i) with cover_split c i :=
      { | inl j := inl j ;
      | inr j := inr (pop j) } .

Equations r_cover_split_r {xs ys zs} (p : xs ⊎ ys ≡ zs) [x] (i : zs ∋ x) {j : xs ∋ x} : cover_split p i = inl j -> i = r_cover_l p _ j :=
  r_cover_split_r (CLeft c) top h := _ ;
  r_cover_split_r (CRight c) top h := _ ;
  r_cover_split_r (CLeft c) (pop i) h := _ ;
  r_cover_split_r (CRight c) (pop i) h := _ .
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Equations r_cover_split_l {xs ys zs} (p : xs ⊎ ys ≡ zs) [x] (i : zs ∋ x) {j : ys ∋ x} : cover_split p i = inr j -> i = r_cover_r p _ j :=
  r_cover_split_l (CLeft c) top h := _ ;
  r_cover_split_l (CRight c) top h := _ ;
  r_cover_split_l (CLeft c) (pop i) h := _ ;
  r_cover_split_l (CRight c) (pop i) h := _ .
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Equations s_empty {F Γ} : ∅ =[F]> Γ :=
  s_empty x (!).

Equations cover_assoc {Γ1 Γ2 Γ12 Γ3 Γ123} (H1 : Γ1 ⊎ Γ2 ≡ Γ12) (H2 : Γ12 ⊎ Γ3 ≡ Γ123)
  : { Γ23 : _ & (Γ1 ⊎ Γ23 ≡ Γ123 * Γ2 ⊎ Γ3 ≡ Γ23)%type } :=
  cover_assoc u          CNil :=
    (_ ,' (u , cover_nil_r)) ;
  cover_assoc (CLeft u)  (CLeft v) :=
    let '(_ ,' (x1 , x2)) := cover_assoc u v
    in (_ ,' (CLeft x1 , x2)) ;
  cover_assoc (CRight u) (CLeft v) :=
    let '(_ ,' (x1 , x2)) := cover_assoc u v
    in (_ ,' (CRight x1 , CLeft x2)) ;
  cover_assoc u          (CRight v) :=
    let '(_ ,' (x1 , x2)) := cover_assoc u v
    in (_ ,' (CRight x1 , CRight x2)) .

Lemma cover_assoc_eq1 {Γ1 Γ2 Γ12 Γ3 Γ123} (H1 : Γ1 ⊎ Γ2 ≡ Γ12) (H2 : Γ12 ⊎ Γ3 ≡ Γ123) :
  sub_eq _ _
    (r_comp (r_cover_l H2)
            (r_cover_l H1))
    (r_cover_l (fst (projT2 (cover_assoc H1 H2)))).
Admitted.

Lemma cover_assoc_eq2 {Γ1 Γ2 Γ12 Γ3 Γ123} (H1 : Γ1 ⊎ Γ2 ≡ Γ12) (H2 : Γ12 ⊎ Γ3 ≡ Γ123) :
  sub_eq _ _
    (r_comp (r_cover_l H2)
            (r_cover_r H1))
    (r_comp (r_cover_r (fst (projT2 (cover_assoc H1 H2))))
            (r_cover_l (snd (projT2 (cover_assoc H1 H2))))) .
Admitted.

Lemma cover_assoc_eq3 {Γ1 Γ2 Γ12 Γ3 Γ123} (H1 : Γ1 ⊎ Γ2 ≡ Γ12) (H2 : Γ12 ⊎ Γ3 ≡ Γ123) :
  sub_eq _ _
    (r_cover_r H2)
    (r_comp (r_cover_r (fst (projT2 (cover_assoc H1 H2))))
            (r_cover_r (snd (projT2 (cover_assoc H1 H2))))) .
Admitted.


Equations s_cover {F Γ1 Γ2 Γ3 Δ} : Γ1 ⊎ Γ2 ≡ Γ3 -> Γ1 =[F]> Δ -> Γ2 =[F]> Δ -> Γ3 =[F]> Δ :=
  s_cover h u v _ i with cover_split h i := {
    | inl j := u _ j ;
    | inr j := v _ j
  } .

#[global] Instance s_cover_proper {F Γ1 Γ2 Γ3 Δ} (H : Γ1 ⊎ Γ2 ≡ Γ3) : Proper (sub_eq _ _ ==> sub_eq _ _ ==> sub_eq _ _) (s_cover (F:=F) (Δ:=Δ) H).
intros ? ? H1 ? ? H2 ? i.
unfold s_cover, s_cover_clause_1.
destruct (cover_split H i).
now apply H1.
now apply H2.
Qed.



Definition s_cat {F Γ1 Γ2 Δ} : Γ1 =[F]> Δ -> Γ2 =[F]> Δ -> (Γ1 +▶ Γ2) =[F]> Δ :=
  s_cover cover_cat .
Notation "[ u , v ]" := (s_cat u v) (at level 14, only printing, format "[ u  ,  v ]").

Definition r_concat_l {Γ Δ : ctx X} : Γ ⊆ (Γ +▶ Δ) :=
  r_cover_l cover_cat .

Definition r_cover_l_nil {Γ} : sub_eq Γ Γ (r_cover_l cover_nil_r) r_id .
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
  s_cat r_concat_l (r_comp r_concat_r r_concat_l).

Definition r_concat3_2 {Γ Δ ϒ : ctx X} : (Γ +▶ ϒ) ⊆ (Γ +▶ (Δ +▶ ϒ)) :=
  s_cat r_concat_l (r_comp r_concat_r r_concat_r).

Lemma s_eq_cover_empty_r {F Γ1 Δ} (u : Γ1 =[F]> Δ)
          : sub_eq _ _ (s_cat u s_empty) u.
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
                                end) Γ0) h
                    with
                    | inl h0 => u x1 (pop h0)
                    | inr h0 => s_empty x1 h0
                    end).
      destruct (cover_split ((fix cover_nil_r (xs : ctx X) : xs ⊎ ∅ ≡ xs :=
                                match xs as c return (c ⊎ ∅ ≡ c) with
                                | ∅%ctx => CNil
                                | (c ▶ x)%ctx => CLeft (cover_nil_r c)
                                end) Γ0) h);
        eauto.
      apply (IHΓ1 _ (fun _ i => u _ (pop i))).
  Qed.

Lemma s_eq_cover_empty_l {F Γ1 Δ} (u : Γ1 =[F]> Δ)
          : sub_eq _ _ (s_cat s_empty u) (rew <- [fun x => x =[F]> _] ccat_empty_l in u).
Admitted.

Lemma s_eq_cover_l {F Γ1 Γ2 Γ3 Δ} (H : Γ1 ⊎ Γ2 ≡ Γ3) (u : Γ1 =[F]> Δ) (v : Γ2 =[F]> Δ)
      : sub_eq _ _ (s_ren (s_cover H u v) (r_cover_l H)) u.
Proof.
  intros ? i. dependent induction H.
  - dependent elimination i.
  - dependent elimination i.
    + reflexivity.
    + unfold s_ren, s_cover, s_cover_clause_1; cbn; unfold cover_split_clause_3.
      transitivity (match cover_split H (r_cover_l H _ h) with
                    | inl h0 => u _ (pop h0)
                    | inr h0 => v _ h0
                    end).
      destruct (cover_split H (r_cover_l H _ h)); eauto.
      now apply (IHcover (fun _ i => u _ (pop i)) v).
  - unfold s_ren, s_cover, s_cover_clause_1; cbn; unfold cover_split_clause_4.
    transitivity (match cover_split H (r_cover_l H _ i) with
                  | inl h0 => u _ h0
                  | inr h0 => v _ (pop h0)
                  end).
    destruct (cover_split H (r_cover_l H _ i)); eauto.
    now apply (IHcover u (fun _ i => v _ (pop i))).
Qed.

Lemma s_eq_cat_l {F Γ1 Γ2 Δ} (u : Γ1 =[F]> Δ) (v : Γ2 =[F]> Δ)
      : sub_eq _ _ (s_ren (s_cat u v) r_concat_l) u.
  apply s_eq_cover_l.
Qed.

Lemma s_eq_cover_r {F Γ1 Γ2 Γ3 Δ} (H : Γ1 ⊎ Γ2 ≡ Γ3) (u : Γ1 =[F]> Δ) (v : Γ2 =[F]> Δ)
      : sub_eq _ _ (s_ren (s_cover H u v) (r_cover_r H)) v.
Proof.
  dependent induction H; intros ? i.
  - dependent elimination i.
  - unfold s_ren, s_cover, s_cover_clause_1, r_comp.
    rewrite r_cover_r_equation_2, cover_split_equation_3.
      unfold cover_split_clause_3.
      transitivity (match cover_split H (r_cover_r H _ i) with
                    | inl h0 => u _ (pop h0)
                    | inr h0 => v _ h0
                    end).
      destruct (cover_split H (r_cover_r H a i)); eauto.
      now apply (IHcover (fun _ i => u _ (pop i)) v).
  - dependent elimination i.
    reflexivity.
    unfold s_ren, s_cover, s_cover_clause_1, r_comp.
    rewrite r_cover_r_equation_4, cover_split_equation_5.
    unfold cover_split_clause_4.
    transitivity (match cover_split H (r_cover_r H _ h) with
                  | inl h0 => u _ h0
                  | inr h0 => v _ (pop h0)
                  end).
    destruct (cover_split H (r_cover_r H x1 h)); eauto.
    now apply (IHcover u (fun _ i => v _ (pop i))).
Qed.

Lemma s_eq_cat_r {F Γ1 Γ2 Δ}
           (u : Γ1 =[F]> Δ) (v : Γ2 =[F]> Δ)
          : sub_eq _ _ (s_ren (s_cat u v) r_concat_r) v.
  apply s_eq_cover_r.
Qed.

Lemma s_eq_cover_uniq {F Γ1 Γ2 Γ3 Δ} (H : Γ1 ⊎ Γ2 ≡ Γ3) (u : Γ1 =[F]> Δ) (v : Γ2 =[F]> Δ) (w : Γ3 =[F]> Δ)
       (H1 : sub_eq _ _ u (s_ren w (r_cover_l H)))
       (H2 : sub_eq _ _ v (s_ren w (r_cover_r H)))
       : sub_eq _ _ (s_cover H u v) w.
  intros ? i.
  unfold s_cover, s_cover_clause_1.
  destruct (cover_split H i) eqn:?.
  rewrite (r_cover_split_r H _ Heqs); apply H1.
  rewrite (r_cover_split_l H _ Heqs); apply H2.
Qed.

Definition s_cover_assoc {F Γ1 Γ2 Γ12 Γ3 Γ123 Δ}
  (H1 : Γ1 ⊎ Γ2 ≡ Γ12) (H2 : Γ12 ⊎ Γ3 ≡ Γ123)
  (u1 : Γ1 =[F]> Δ) (u2 : Γ2 =[F]> Δ) (u3 : Γ3 =[F]> Δ)
  : sub_eq _ _ (s_cover H2 (s_cover H1 u1 u2) u3)
       (s_cover (fst (projT2 (cover_assoc H1 H2))) u1 (s_cover (snd (projT2 (cover_assoc H1 H2))) u2 u3)).
  apply s_eq_cover_uniq.
  + apply s_eq_cover_uniq; rewrite <- s_ren_comp.
    * now rewrite cover_assoc_eq1, s_eq_cover_l.
    * now rewrite cover_assoc_eq2, s_ren_comp, s_eq_cover_r, s_eq_cover_l.
  + now rewrite (cover_assoc_eq3 H1), s_ren_comp, 2 s_eq_cover_r.
  Qed.

End lemma.

#[global] Notation join_even := (join_even_odd_aux true) .
#[global] Notation join_odd := (join_even_odd_aux false) .
#[global] Notation "Γ ∋ x" := (has Γ%ctx x) (at level 30) : type_scope.
#[global] Notation "a ⊎ b ≡ c" := (cover a%ctx b%ctx c%ctx) (at level 30) : type_scope.
#[global] Notation "Γ ⊆ Δ" := (substitution has Γ%ctx Δ%ctx) (at level 30) : type_scope.
#[global] Notation "Γ =[ F ]> Δ" := (substitution F Γ%ctx Δ%ctx) (at level 30) : type_scope.
#[global] Notation "a ∘⊆ b" := (r_comp a%ctx b%ctx) (at level 30).
#[global] Notation "[ u , v ]" := (s_cat u v) (at level 14, only printing, format "[ u  ,  v ]").
