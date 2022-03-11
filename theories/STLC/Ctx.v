Import EqNotations.
From ExtLib.Data Require Import Nat Fin List.
From Equations Require Import Equations.
From OGS Require Import Utils.
Set Equations Transparent.

Definition ctx (X : Type) : Type := list X.

#[global] Declare Scope ctx_scope.
#[global] Delimit Scope ctx_scope with ctx.
#[global] Bind Scope ctx_scope with ctx.

#[global] Notation "∅" := nil : ctx_scope.
#[global] Notation "Γ ▶ x" := (x :: Γ%ctx) (at level 40, left associativity) : ctx_scope.
#[global] Notation "Γ +▶ Δ" := (app Δ%ctx Γ%ctx) (at level 50, left associativity) : ctx_scope.


Section lemma.
Context {X : Type}.

Definition join : ctx (ctx X) -> ctx X := @Lists.List.concat X.

Equations join_cat Γs Δs : join (Γs +▶ Δs)%ctx = ((join Γs) +▶ (join Δs))%ctx :=
  join_cat Γs ∅%ctx        := eq_refl ;
  join_cat Γs (Δs ▶ Δ)%ctx :=
    rew app_assoc Δ (join Δs) (join Γs)
     in f_equal (app Δ) (join_cat Γs Δs).
Arguments join_cat {Γs Δs}.
    
Inductive has : ctx X -> X -> Type :=
| top {Γ x} : has (Γ ▶ x) x
| pop {Γ x y} : has Γ x -> has (Γ ▶ y) x.
Notation "Γ ∋ x" := (has Γ%ctx x) (at level 30).
Derive Signature for has.

Equations has_get (Γ : ctx X) i : Γ ∋ (Γ.[i]) :=
  has_get (x :: xs) F0     := top ;
  has_get (x :: xs) (FS i) := pop (has_get xs i) .

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

Definition r_shift {Γ Δ : ctx X} {a} (f : forall t, Γ ∋ t -> Δ ∋ t)
  : forall t, (Γ ▶ a) ∋ t -> (Δ ▶ a) ∋ t
  := has_case top (fun _ i => pop (f _ i)).

Definition r_shift2 {Γ Δ : ctx X} {a b} (f : forall t, Γ ∋ t -> Δ ∋ t)
  : forall t, (Γ ▶ a ▶ b) ∋ t -> (Δ ▶ a ▶ b) ∋ t
  := r_shift (r_shift f).

Equations concat_split (Γ Δ : ctx X) {s} : (Γ +▶ Δ) ∋ s -> (Γ ∋ s) + (Δ ∋ s) :=
  concat_split Γ ∅       i := inl i ;
  concat_split Γ (Δ ▶ x) top     := inr top ;
  concat_split Γ (Δ ▶ x) (pop i) with concat_split Γ Δ i := {
    | inl j := inl j ;
    | inr j := inr (pop j) } .

(* handful of lemma on concatenation *)
Equations r_concat_l (Γ Δ : ctx X) : forall t, Γ ∋ t -> (Γ +▶ Δ) ∋ t :=
  r_concat_l Γ ∅       _ i := i ;
  r_concat_l Γ (Δ ▶ x) _ i := pop (r_concat_l _ _ _ i) .
Arguments r_concat_l {Γ Δ}.

Equations r_concat_r (Γ Δ : ctx X) : forall t, Δ ∋ t -> (Γ +▶ Δ) ∋ t :=
  r_concat_r Γ (Δ ▶ x) _ top     := top ;
  r_concat_r Γ (Δ ▶ x) _ (pop i) := pop (r_concat_r _ _ _ i) .
Arguments r_concat_r {Γ Δ}.

Equations r_concat3_1 (Γ Δ ϒ : ctx X) : forall t, (Γ +▶ Δ) ∋ t -> (Γ +▶ (Δ +▶ ϒ)) ∋ t :=
  r_concat3_1 Γ Δ ∅       _ i := i ;
  r_concat3_1 Γ Δ (ϒ ▶ _) _ i := pop (r_concat3_1 Γ Δ ϒ _ i). 
Arguments r_concat3_1 {Γ Δ ϒ}.

Equations r_concat3_2 (Γ Δ ϒ : ctx X) : forall t, (Γ +▶ ϒ) ∋ t -> (Γ +▶ (Δ +▶ ϒ)) ∋ t :=
  r_concat3_2 Γ Δ ∅       _ i       := r_concat_l _ i ;
  r_concat3_2 Γ Δ (ϒ ▶ _) _ top     := top ;
  r_concat3_2 Γ Δ (ϒ ▶ _) _ (pop i) := pop (r_concat3_2 Γ Δ ϒ _ i) .
Arguments r_concat3_2 {Γ Δ ϒ}.

Variant any (P : X -> Type) (xs : list X) : Type :=
| Any {x} : xs ∋ x -> P x -> any P xs
.
Arguments Any {P xs x} i p.

Equations any_el {P xs} : any P xs -> X :=
  any_el (@Any _ _ x _ _) := x .

Equations any_coh {P xs} (a : any P xs) : P (any_el a) :=
  any_coh (Any _ p) := p .

Equations any_elim {P} {A : forall x, P x -> Type} (f : forall x p, A x p)
          xs (a : any P xs) : A (any_el a) (any_coh a) :=
  any_elim f xs (Any _ p) := f _ p .

Inductive cover : ctx X -> ctx X -> ctx X -> Type :=
| CNil :                                 cover ∅        ∅        ∅
| CLeft {x xs ys zs} : cover xs ys zs ->  cover (xs ▶ x) ys       (zs ▶ x)
| CRight {x xs ys zs} : cover xs ys zs -> cover xs       (ys ▶ x) (zs ▶ x)
.
Arguments CNil.
Arguments CLeft {x xs ys zs} c.
Arguments CRight {x xs ys zs} c.
Notation "a ⊎ b ≡ c" := (cover a b c) (at level 30).

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

Equations r_cover_l {xs ys zs} (p : xs ⊎ ys ≡ zs) [x] : xs ∋ x -> zs ∋ x :=
  r_cover_l (CLeft c)  top     := top ;
  r_cover_l (CLeft c)  (pop i) := pop (r_cover_l c i) ;
  r_cover_l (CRight c) i       := pop (r_cover_l c i) .

Equations r_cover_r {xs ys zs} (p : xs ⊎ ys ≡ zs) [x] : ys ∋ x -> zs ∋ x :=
  r_cover_r (CLeft c)  i       := pop (r_cover_r c i) ;
  r_cover_r (CRight c) top     := top ;
  r_cover_r (CRight c) (pop i) := pop (r_cover_r c i) .

Equations cover_split {xs ys zs} (p : xs ⊎ ys ≡ zs) [x] : zs ∋ x -> xs ∋ x + ys ∋ x:=
  cover_split (CLeft c)  top     := inl top ;
  cover_split (CRight c) top     := inr top ;
  cover_split (CLeft c)  (pop i) with cover_split c i :=
      { | inl j := inl (pop j) ;
        | inr j := inr j } ;
  cover_split (CRight c) (pop i) with cover_split c i :=
      { | inl j := inl j ;
        | inr j := inr (pop j) } .

Equations any_c_split {P xs ys zs} : xs ⊎ ys ≡ zs -> any P zs -> any P xs + any P ys :=
  any_c_split c (Any i p) with cover_split c i :=
    { | inl j := inl (Any j p) ;
      | inr j := inr (Any j p) } .

Equations r_any {P xs ys} (ρ : forall x, xs ∋ x -> ys ∋ x) : any P xs -> any P ys :=
  r_any ρ (Any i p) := Any (ρ _ i) p .

(*
Equations any_c_split_coh1 {P xs ys zs} (c : xs ⊎ ys ≡ zs) (a : any P zs) :
  any_el a = match any_c_split c a with
             | inl a' => any_el a'
             | inr a' => any_el a'
             end :=
  any_c_split_coh1 c (@Any _ _ x i p) with cover_split c i :=
    { | inl j := eq_refl ;
      | inr j := eq_refl } .

Equations any_c_split_coh2 {P xs ys zs} (c : xs ⊎ ys ≡ zs) (a : any P zs) :
  any_el a = match any_c_split c a with
             | inl a' => any_el a'
             | inr a' => any_el a'
             end :=
  any_c_split_coh1 c (@Any _ _ x i p) with cover_split c i :=
    { | inl j := eq_refl ;
      | inr j := eq_refl } .
*)

End lemma.
#[global] Notation "Γ ∋ x" := (has Γ%ctx x) (at level 30).
#[global] Notation "a ⊎ b ≡ c" := (cover a b c) (at level 30).
