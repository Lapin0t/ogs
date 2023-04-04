From Coq Require Import Program.Equality.
From Equations Require Import Equations.
Set Equations Transparent.

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

Section lemma.
Context {X : Type}.

Search "concat".

Equations join : ctx (ctx X) -> ctx X :=
  join (∅)     := ∅ ;
  join (Γ ▶ xs) := join Γ +▶ xs .

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

(* handful of lemma on concatenation *)
Equations r_concat_l (Γ Δ : ctx X) : Γ ⊆ (Γ +▶ Δ) :=
  r_concat_l Γ ∅       _ i := i ;
  r_concat_l Γ (Δ ▶ x) _ i := pop (r_concat_l _ _ _ i) .
Arguments r_concat_l {Γ Δ}.

Equations r_concat_r (Γ Δ : ctx X) : Δ ⊆ (Γ +▶ Δ) :=
  r_concat_r Γ (Δ ▶ x) _ top     := top ;
  r_concat_r Γ (Δ ▶ x) _ (pop i) := pop (r_concat_r _ _ _ i) .
Arguments r_concat_r {Γ Δ}.

Equations r_concat3_1 (Γ Δ ϒ : ctx X) : (Γ +▶ Δ) ⊆ (Γ +▶ (Δ +▶ ϒ)) :=
  r_concat3_1 Γ Δ ∅       _ i := i ;
  r_concat3_1 Γ Δ (ϒ ▶ _) _ i := pop (r_concat3_1 Γ Δ ϒ _ i). 
Arguments r_concat3_1 {Γ Δ ϒ}.

Equations r_concat3_2 (Γ Δ ϒ : ctx X) : (Γ +▶ ϒ) ⊆ (Γ +▶ (Δ +▶ ϒ)) :=
  r_concat3_2 Γ Δ ∅       _ i       := r_concat_l _ i ;
  r_concat3_2 Γ Δ (ϒ ▶ _) _ top     := top ;
  r_concat3_2 Γ Δ (ϒ ▶ _) _ (pop i) := pop (r_concat3_2 Γ Δ ϒ _ i) .
Arguments r_concat3_2 {Γ Δ ϒ}.

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
End lemma.

#[global] Notation "Γ ∋ x" := (has Γ%ctx x) (at level 30) : type_scope.
#[global] Notation "a ⊎ b ≡ c" := (cover a b c) (at level 30) : type_scope.
#[global] Notation "Γ ⊆ Δ" := (substitution has Γ%ctx Δ%ctx) (at level 30) : type_scope.
#[global] Notation "Γ =[ F ]> Δ" := (substitution F Γ%ctx Δ%ctx) (at level 30) : type_scope.
