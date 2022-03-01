Import EqNotations.
From ExtLib.Data Require Import Nat Fin List.
From Equations Require Import Equations.
From OGS Require Import Utils.

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

End lemma.
#[global] Notation "Γ ∋ x" := (has Γ%ctx x) (at level 30).
