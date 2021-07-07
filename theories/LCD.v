(*From Ltac2 Require Import Ltac2.*)
Require Import Psatz.
From ExtLib.Data Require Import Nat Fin List Unit.
From Coq Require Import Logic.
Import EqNotations.
From Equations Require Import Equations.

From OGS Require Import EventD CatD ITreeD Utils RecD AngelicD.

Set Primitive Projections.
Set Equations Transparent.

Notation "a ,& b" := (existT _ a b) (at level 30).
(*Notation "'ex' a" := (existT _ _ a) (at level 30).*)

Definition uncurry2 {A B : Type} {C : A -> B -> Type}
                    (f : forall a b, C a b) (i : A * B) :=
  f (fst i) (snd i).
Definition curry2 {A B : Type} {C : A -> B -> Type}
                  (f : forall i, C (fst i) (snd i)) a b :=
  f (a , b).

(* Naming & Abbreviations

   ty : 'type', STLC type
   ctx : 'context', STLC typing context
   t_env : 'typing environment', STLC context + STLC type, ie argument
     of typing judgement
   nc : 'negative context', context containing only negative types
   nt : 'negative type'

   r_X : prefix for renaming-related stuff
   s_X : prefix for substitution-related stuff
   e_X : prefix for eager-reduction-related stuff
   t_X : prefix for term-related stuff
   ty_X : prefix for type-related stuff
*)


Inductive ty : Type :=
| Unit : ty
| Prod : ty -> ty -> ty
| Arr : ty -> ty -> ty
| Sum : ty -> ty -> ty
.

Derive NoConfusion for ty.
Declare Scope ty_scope.
Delimit Scope ty_scope with ty.
Bind Scope ty_scope with ty.
Notation "A → B" := (Arr A B) (at level 40) : ty_scope .
Notation "A × B" := (Prod A B) (at level 40) : ty_scope.
Notation "A + B" := (Sum A B) : ty_scope.

Variant is_neg : ty -> Type := | NArr {a b} : is_neg (a → b) .
Definition neg_ty : Type := { t : ty & is_neg t }.
Definition of_n_ty (t : neg_ty) : ty := projT1 t.
Coercion of_n_ty : neg_ty >-> ty.

(*
Variant polarity : Type := Pos | Neg .
Derive NoConfusion for polarity.

Equations ty_pol : ty -> polarity :=
  ty_pol (_ → _) := Neg ;
  ty_pol (_ × _) := Pos ;
  ty_pol (_ + _) := Pos ;
  ty_pol Unit    := Pos .

Definition p_ty (p : polarity) : Type := { t : ty & ty_pol_graph t p }.
Definition of_p_ty {p} (t : p_ty p) : ty := projT1 t.
Coercion of_p_ty : p_ty >-> ty.

Definition p_ty_of_t (t : ty) : p_ty (ty_pol t) := t ,& ty_pol_graph_correct t.
Coercion p_ty_of_t : ty >-> p_ty.

Equations ty_pol_graph_coherent (t : ty) (p : polarity) : ty_pol_graph t p -> ty_pol t = p :=
  ty_pol_graph_coherent _ _ (ty_pol_graph_equation_1) := eq_refl ;
  ty_pol_graph_coherent _ _ (ty_pol_graph_equation_2 _ _) := eq_refl ;
  ty_pol_graph_coherent _ _ (ty_pol_graph_equation_3 _ _) := eq_refl ;
  ty_pol_graph_coherent _ _ (ty_pol_graph_equation_4 _ _) := eq_refl .

Bind Scope ty_scope with p_ty.

Definition is_pos (t : ty) : Type := ty_pol_graph t Pos.
Definition is_neg (t : ty) : Type := ty_pol_graph t Neg.
*)

Definition ctx : Type := list ty.
Notation "∅" := nil.
Notation "Γ ▶ x" := (x :: Γ) (at level 20).
Notation "Γ +▶ Δ" := (Δ ++ Γ) (at level 50, left associativity).

Definition neg_ctx : Type := list neg_ty.
Definition of_n_ctx : neg_ctx -> ctx := map of_n_ty.
Coercion of_n_ctx : neg_ctx >-> ctx.

Inductive has : ctx -> ty -> Type :=
| top {Γ x} : has (Γ ▶ x) x
| pop {Γ x y} : has Γ x -> has (Γ ▶ y) x.
Notation "Γ ∋ t" := (has Γ t) (at level 30).

Equations neg_var {Γ : neg_ctx} {x} : Γ ∋ x -> is_neg x :=
  @neg_var ∅       _ (!) ;
  @neg_var (_ ▶ t) _ (top)   := projT2 t ;
  @neg_var (_ ▶ _) _ (pop i) := neg_var i .

Equations has_get Γ i : Γ ∋ (Γ.[i]) :=
  has_get (x :: xs) F0     := top ;
  has_get (x :: xs) (FS i) := pop (has_get xs i) .

(* helper for defining various shiftings *)
Equations has_case {Γ Δ} {F : ctx -> ty -> Type} {a}
  : F Δ a -> (forall x, Γ ∋ x -> F Δ x) -> forall x, (Γ ▶ a) ∋ x -> F Δ x :=
  has_case z s _ top     := z ;
  has_case z s _ (pop i) := s _ i .

Definition r_shift {Γ Δ a} (f : forall t, Γ ∋ t -> Δ ∋ t)
  : forall t, (Γ ▶ a) ∋ t -> (Δ ▶ a) ∋ t
  := has_case top (fun _ i => pop (f _ i)).

Definition r_shift2 {Γ Δ a b} (f : forall t, Γ ∋ t -> Δ ∋ t)
  : forall t, (Γ ▶ a ▶ b) ∋ t -> (Δ ▶ a ▶ b) ∋ t
  := r_shift (r_shift f).

(* handful of lemma on concatenation *)
Equations r_concat_l Γ Δ : forall t, Γ ∋ t -> (Γ +▶ Δ) ∋ t :=
  r_concat_l Γ ∅       _ i := i ;
  r_concat_l Γ (Δ ▶ x) _ i := pop (r_concat_l _ _ _ i) .
Arguments r_concat_l {Γ Δ}.

Equations r_concat_r Γ Δ : forall t, Δ ∋ t -> (Γ +▶ Δ) ∋ t :=
  r_concat_r Γ (Δ ▶ x) _ top     := top ;
  r_concat_r Γ (Δ ▶ x) _ (pop i) := pop (r_concat_r _ _ _ i) .
Arguments r_concat_r {Γ Δ}.

Equations r_concat3_1 Γ Δ ϒ : forall t, (Γ +▶ Δ) ∋ t -> (Γ +▶ (Δ +▶ ϒ)) ∋ t :=
  r_concat3_1 Γ Δ ∅       _ i := i ;
  r_concat3_1 Γ Δ (ϒ ▶ _) _ i := pop (r_concat3_1 Γ Δ ϒ _ i). 
Arguments r_concat3_1 {Γ Δ ϒ}.

Equations r_concat3_2 Γ Δ ϒ : forall t, (Γ +▶ ϒ) ∋ t -> (Γ +▶ (Δ +▶ ϒ)) ∋ t :=
  r_concat3_2 Γ Δ ∅       _ i       := r_concat_l _ i ;
  r_concat3_2 Γ Δ (ϒ ▶ _) _ top     := top ;
  r_concat3_2 Γ Δ (ϒ ▶ _) _ (pop i) := pop (r_concat3_2 Γ Δ ϒ _ i) .
Arguments r_concat3_2 {Γ Δ ϒ}.

Inductive term : ctx -> ty -> Type :=
| Var {Γ a} (i : Γ ∋ a) : term Γ a
| Lam {Γ a b} (u : term (Γ ▶ a) b) : term Γ (a → b)
| Rec {Γ a b} (u : term (Γ ▶ (a → b)%ty ▶ a) b) : term Γ (a → b)
| App {Γ a b} (u : term Γ (a → b)) (v : term Γ a) : term Γ b
| Pair {Γ a b} (u : term Γ a) (v : term Γ b) : term Γ (a × b)
| PMatch {Γ a b x} (u : term Γ (a × b)) (v : term (Γ ▶ a ▶ b) x) : term Γ x
| Inl {Γ a b} (u : term Γ a) : term Γ (a + b)
| Inr {Γ a b} (u : term Γ b) : term Γ (a + b)
| SMatch {Γ a b x} (u : term Γ (a + b)) (v : term (Γ ▶ a) x) (w : term (Γ ▶ b) x)
         : term Γ x
.

(*****************************)
(* renaming and substitution *)

Equations t_rename {Γ Δ} (f : forall t, Γ ∋ t -> Δ ∋ t) {t} : term Γ t -> term Δ t :=
  t_rename f (Var i)        := Var (f _ i) ;
  t_rename f (Lam u)        := Lam (t_rename (r_shift f) u) ;
  t_rename f (Rec u)        := Rec (t_rename (r_shift (r_shift f)) u) ;
  t_rename f (App u v)      := App (t_rename f u) (t_rename f v) ;
  t_rename f (Pair u v)     := Pair (t_rename f u) (t_rename f v) ;
  t_rename f (PMatch u v)   := PMatch (t_rename f u) (t_rename (r_shift2 f) v) ;
  t_rename f (Inl u)        := Inl (t_rename f u) ; 
  t_rename f (Inr u)        := Inr (t_rename f u) ; 
  t_rename f (SMatch u v w) := SMatch (t_rename f u) (t_rename (r_shift f) v)
                                                     (t_rename (r_shift f) w).

Definition t_shift {Γ} {x y} : term Γ x -> term (Γ ▶ y) x :=
  t_rename (fun _ => pop).

Definition s_shift {Γ Δ a} (f : forall t, Γ ∋ t -> term Δ t)
  : forall t, (Γ ▶ a) ∋ t -> term (Δ ▶ a) t
  := has_case (Var top) (fun _ i => t_shift (f _ i)).

Definition s_shift2 {Γ Δ a b} (f : forall t, Γ ∋ t -> term Δ t)
                    : forall t, (Γ ▶ a ▶ b) ∋ t -> term (Δ ▶ a ▶ b) t
  := s_shift (s_shift f).

Equations t_subst {Γ Δ} (f : forall t, Γ ∋ t -> term Δ t) {t} : term Γ t -> term Δ t :=
  t_subst f (Var i)       := f _ i ;
  t_subst f (Lam u)       := Lam (t_subst (s_shift f) u) ;
  t_subst f (Rec u)       := Rec (t_subst (s_shift2 f) u) ;
  t_subst f (App u v)     := App (t_subst f u) (t_subst f v) ;
  t_subst f (Pair u v)    := Pair (t_subst f u) (t_subst f v) ;
  t_subst f (PMatch u v)  := PMatch (t_subst f u) (t_subst (s_shift2 f) v) ;
  t_subst f (Inl u)       := Inl (t_subst f u) ;
  t_subst f (Inr u)       := Inr (t_subst f u) ;
  t_subst f (SMatch u v w) := SMatch (t_subst f u) (t_subst (s_shift f) v)
                                                   (t_subst (s_shift f) w).

Equations t_subst1 {Γ a b} (u : term (Γ ▶ a) b) (v : term Γ a) : term Γ b :=
  t_subst1 u v := t_subst f u
    where f : forall t, (Γ ▶ a) ∋ t -> term Γ t := {
          f _ top := v ;
          f _ (pop i) := Var i }.

Notation "u /ₛ v" := (t_subst1 u v) (at level 50, left associativity).

(**************************************************)
(* Eager values, evaluation contexts, redexes etc *)

Inductive e_val (Γ : ctx) : ty -> Type :=
| VVar {x} : Γ ∋ x -> e_val Γ x
| VLam {a b} : term (Γ ▶ a) b -> e_val Γ (a → b)
| VRec {a b} : term (Γ ▶ (a → b)%ty ▶ a) b -> e_val Γ (a → b)
| VPair {a b} : e_val Γ a -> e_val Γ b -> e_val Γ (a × b)
| VInl {a b} : e_val Γ a -> e_val Γ (a + b)
| VInr {a b} : e_val Γ b -> e_val Γ (a + b)
.
Arguments VVar {Γ x}.
Arguments VLam {Γ a b}.
Arguments VRec {Γ a b}.
Arguments VPair {Γ a b}.
Arguments VInl {Γ a b}.
Arguments VInr {Γ a b}.

Equations t_of_val {Γ x} : e_val Γ x -> term Γ x :=
  t_of_val (VVar i) := Var i ;
  t_of_val (VLam u) := Lam u ;
  t_of_val (VRec u) := Rec u ;
  t_of_val (VPair u v) := Pair (t_of_val u) (t_of_val v) ;
  t_of_val (VInl u) := Inl (t_of_val u) ;
  t_of_val (VInr u) := Inr (t_of_val u) .
Coercion t_of_val : e_val >-> term.

Equations v_rename {Γ Δ} (f : forall t, Γ ∋ t -> Δ ∋ t) {t} : e_val Γ t -> e_val Δ t :=
  v_rename f (VVar i)    := VVar (f _ i) ;
  v_rename f (VLam u)    := VLam (t_rename (r_shift f) u) ;
  v_rename f (VRec u)    := VRec (t_rename (r_shift2 f) u) ;
  v_rename f (VPair u v) := VPair (v_rename f u) (v_rename f v) ;
  v_rename f (VInl u)    := VInl (v_rename f u) ;
  v_rename f (VInr u)    := VInr (v_rename f u) .
  
(*
Inductive p_val : forall {p}, ctx -> p_ty p -> Type :=
| PVar {Γ x} : Γ ∋ x -> p_val Γ x
| PLam {Γ a b} : term (Γ ▶ a) b -> p_val Γ (a → b)
| PRec {Γ a b} : term (Γ ▶ (a → b)%ty ▶ a) b -> p_val Γ (a → b)
| PPair {Γ} {a b : ty} : p_val Γ a -> p_val Γ b -> p_val Γ (a × b)
| PInl {Γ} {a b : ty} : p_val Γ a -> p_val Γ (a + b)
| PInr {Γ} {a b : ty} : p_val Γ b -> p_val Γ (a + b)
.
*)
(*
neg_var i := { | existT _ (NArr a b) eq_refl := NVVar i } ;
  to_nv (VLam u) := NVLam u ;
  to_nv (VRec u) := NVRec u ;
  to_nv (VPair u v) := NVPair (to_nv u) (to_nv v) ;
  to_nv (VInl u) := NVInl (to_nv u) ;
  to_nv (VInr u) := NVInr (to_nv u) .
*)


(* e_ctx Γ y x is an eager evaluation context with:
    - variables in Γ,
    - hole type x and
    - return type y
   They grow on the outwards, that is the operation closest to the hole will be
   the topmost constructor. This is exactly the type of the call-stack of the
   CBV evaluator.
*)
Inductive e_ctx (Γ : ctx) (t : ty) : ty -> Type :=
| EHole : e_ctx Γ t t
| EApp_l {a b} : e_ctx Γ t b -> term Γ a -> e_ctx Γ t (a → b)
| EApp_r {a b} : e_ctx Γ t b -> e_val Γ (a → b) -> e_ctx Γ t a
| EPair_l {a b} : e_ctx Γ t (a × b) -> term Γ b -> e_ctx Γ t a
| EPair_r {a b} : e_ctx Γ t (a × b) -> e_val Γ a -> e_ctx Γ t b
| EPMatch {a b x} : e_ctx Γ t x -> term (Γ ▶ a ▶ b) x -> e_ctx Γ t (a × b)
| EInl {a b} : e_ctx Γ t (a + b) -> e_ctx Γ t a
| EInr {a b} : e_ctx Γ t (a + b) -> e_ctx Γ t b
| ESMatch {a b x} : e_ctx Γ t x -> term (Γ ▶ a) x -> term (Γ ▶ b) x -> e_ctx Γ t (a + b)
.
Arguments EHole {Γ t}.
Arguments EApp_l {Γ t a b}.
Arguments EApp_r {Γ t a b}.
Arguments EPair_l {Γ t a b}.
Arguments EPair_r {Γ t a b}.
Arguments EPMatch {Γ t a b x}.
Arguments EInl {Γ t a b}.
Arguments EInr {Γ t a b}.
Arguments ESMatch {Γ t a b x}.

(*
Equations e_fill {Γ x y} : e_ctx Γ y x -> term (Γ ▶ x) y :=
  e_fill EHole           := Var top ;
  e_fill (EApp_l E u)    := _ ; (*App (e_fill E) (t_shift u) ;*)
  e_fill (EApp_r E u)    := _ ; (*App (t_shift (t_of_val u)) (e_fill E) ;*)
  e_fill (EPair_l E u)   := _ ; (* Pair (e_fill E) (t_shift u) ;*)
  e_fill (EPair_r E u)   := _ ; (*Pair (t_shift (t_of_val u)) (e_fill E) ;*)
  e_fill (EPMatch E u)   := _ ; (*PMatch (t_fill E) (t_shift u) .*)
  e_fill (EInl E)        := _ ;
  e_fill (EInr E)        := _ ;
  e_fill (ESMatch E u v) := _ .
Obligation 1.
*)


Equations e_rename {Γ Δ x y} (f : forall t, Γ ∋ t -> Δ ∋ t) : e_ctx Γ y x -> e_ctx Δ y x :=
  e_rename f EHole         := EHole ;
  e_rename f (EApp_r E u)  := EApp_r (e_rename f E) (v_rename f u) ;
  e_rename f (EApp_l E u)  := EApp_l (e_rename f E) (t_rename f u) ;
  e_rename f (EPair_r E u) := EPair_r (e_rename f E) (v_rename f u) ;
  e_rename f (EPair_l E u) := EPair_l (e_rename f E) (t_rename f u) ;
  e_rename f (EPMatch E u) := EPMatch (e_rename f E) (t_rename (r_shift2 f) u) ;
  e_rename f (EInl E)      := EInl (e_rename f E) ;
  e_rename f (EInr E)      := EInr (e_rename f E) ;
  e_rename f (ESMatch E u v) := ESMatch (e_rename f E) (t_rename (r_shift f) u)
                                                       (t_rename (r_shift f) v) .

(* useless? now that we work efficiently
Equations e_plug {Γ x y} : e_ctx Γ y x -> term Γ x -> term Γ y :=
  e_plug EHole         t := t ;
  e_plug (EApp_r E u)  t := e_plug E (App (t_of_val u) t) ;
  e_plug (EApp_l E u)  t := e_plug E (App t u) ;
  e_plug (EPair_r E u) t := e_plug E (Pair (t_of_val u) t) ;
  e_plug (EPair_l E u) t := e_plug E (Pair t u) ;
  e_plug (EPMatch E u) t := e_plug E (PMatch t u) ;
  e_plug (EInl E)      t := e_plug E (Inl t) ;
  e_plug (EInr E)      t := e_plug E (Inr t) ;
  e_plug (ESMatch E u v) t := e_plug E (SMatch t u v) .

Definition e_fill {Γ x y} (E : e_ctx Γ y x) : term (Γ ▶ x) y :=
  e_plug (e_rename (fun _ => pop) E) (Var top).

Equations e_concat {Γ x y z} : e_ctx Γ z y -> e_ctx Γ y x -> e_ctx Γ z x :=
  e_concat E0 EHole          := E0 ;
  e_concat E0 (EApp_l E1 u)  := EApp_l (e_concat E0 E1) u ;
  e_concat E0 (EApp_r E1 u)  := EApp_r (e_concat E0 E1) u ;
  e_concat E0 (EPair_l E1 u) := EPair_l (e_concat E0 E1) u ;
  e_concat E0 (EPair_r E1 u) := EPair_r (e_concat E0 E1) u ;
  e_concat E0 (EPMatch E1 u) := EPMatch (e_concat E0 E1) u .

*)

(* 'e_redex Γ x y' represents eliminators on term Γ x returning a term Γ y *)
Variant e_redex (Γ : ctx) : ty -> ty -> Type :=
| RApp {a b} : e_val Γ a -> e_redex Γ (a → b) b
| RPMatch {a b x} : term (Γ ▶ a ▶ b) x -> e_redex Γ (a × b) x
| RSMatch {a b x} : term (Γ ▶ a) x -> term (Γ ▶ b) x -> e_redex Γ (a + b) x
.
Arguments RApp {Γ a b}.
Arguments RPMatch {Γ a b x}.
Arguments RSMatch {Γ a b x}.

Variant e_term (Γ : ctx) (x : ty) : Type :=
| EVal : e_val Γ x -> e_term Γ x
| ERed {a b} : e_ctx Γ x b -> e_val Γ a -> e_redex Γ a b -> e_term Γ x
.
Arguments EVal {Γ x}.
Arguments ERed {Γ x a b}.

Module focus_aux.
(* Given an ongoing computation, that is a term in an evaluation context, E[t],
   we want to find the next redex in CBV evaluation order. This is done efficiently
   using only tail-calls, to produce an evaluator in abstract-machine style. *)
(* The recursion pattern for these tail calls is weird so we need some helpers
   defining a strictly decreasing measure on arguments across calls. *)
Equations term_size {Γ x} : term Γ x -> nat :=
  term_size (Var _) := S O ;
  term_size (Lam _) := S O ;
  term_size (Rec _) := S O ;
  term_size (App a b) := S (S (term_size a + term_size b)) ;
  term_size (Pair a b) := S (S (S (term_size a + term_size b))) ;
  term_size (PMatch a b) := S (term_size a) ;
  term_size (Inl a) := S (S (term_size a)) ;
  term_size (Inr a) := S (S (term_size a)) ;
  term_size (SMatch a b c) := S (term_size a) .

Equations ctx_size {Γ y x} : e_ctx Γ y x -> nat :=
  ctx_size EHole := O ;
  ctx_size (EApp_l E u) := S (ctx_size E + term_size u) ;
  ctx_size (EApp_r E u) := O ;
  ctx_size (EPair_l E u) := S (S (ctx_size E + term_size u)) ;
  ctx_size (EPair_r E u) := S (ctx_size E) ;
  ctx_size (EPMatch E u) := O ;
  ctx_size (EInl E) := S (ctx_size E) ;
  ctx_size (EInr E) := S (ctx_size E) ;
  ctx_size (ESMatch E u v) := O .

Equations aux_size {Γ x} : term Γ x + e_val Γ x -> nat :=
  aux_size (inl t) := term_size t ;
  aux_size (inr v) := O .

(* This should actually be two mutually recursive functions:
     e_focus : e_ctx Γ y x → term Γ x → e_term Γ y 
     e_focus_backtrack : e_ctx Γ y x → e_val Γ x → e_term Γ y
   But Equations doesn't allow 'by wf ..' hints in mutual blocks so we
   have to hack the type into a sum. 

   The idea is that e_focus will descend into the left-most branches,
   recording its path as an evaluation context and stopping at values.
   When a value is hit we have to backtrack on the evaluation context,
   either finding a suitable redex or descending in an other branch.
 *)

Equations focus_aux {Γ x y} (E : e_ctx Γ y x) (t : term Γ x + e_val Γ x)
                : e_term Γ y by wf (ctx_size E + aux_size t)%nat lt :=
  focus_aux E (inl (Var i))      := focus_aux E (inr (VVar i)) ;
  focus_aux E (inl (Lam a))      := focus_aux E (inr (VLam a)) ;
  focus_aux E (inl (Rec a))      := focus_aux E (inr (VRec a)) ;
  focus_aux E (inl (App a b))    := focus_aux (EApp_l E b) (inl a) ;
  focus_aux E (inl (Pair a b))   := focus_aux (EPair_l E b) (inl a) ;
  focus_aux E (inl (PMatch a b)) := focus_aux (EPMatch E b) (inl a) ;
  focus_aux E (inl (Inl a))      := focus_aux (EInl E) (inl a) ;
  focus_aux E (inl (Inr a))      := focus_aux (EInr E) (inl a) ;
  focus_aux E (inl (SMatch a b c)) := focus_aux (ESMatch E b c) (inl a) ;

  focus_aux EHole         (inr v) := EVal v ;
  focus_aux (EApp_l E u)  (inr v) := focus_aux (EApp_r E v) (inl u) ;
  focus_aux (EApp_r E u)  (inr v) := ERed E u (RApp v) ;
  focus_aux (EPair_l E u) (inr v) := focus_aux (EPair_r E v) (inl u) ;
  focus_aux (EPair_r E u) (inr v) := focus_aux E (inr (VPair u v)) ;
  focus_aux (EPMatch E b) (inr v) := ERed E v (RPMatch b) ;
  focus_aux (EInl E)      (inr v) := focus_aux E (inr (VInl v)) ;
  focus_aux (EInr E)      (inr v) := focus_aux E (inr (VInr v)) ;
  focus_aux (ESMatch E a b) (inr v) := ERed E v (RSMatch a b) .
Obligation 1. lia. Qed.
Obligation 2. lia. Qed.
Obligation 3. lia. Qed.
Obligation 4. lia. Qed.
Obligation 5. lia. Qed.
Obligation 6. lia. Qed.
Obligation 7. lia. Qed.
Obligation 8. lia. Qed.
Obligation 9. lia. Qed.
Obligation 10. lia. Qed.
Obligation 11. lia. Qed.
End focus_aux.
 
(* pack a term and an evaluation context *)
Variant eval_arg (Γ : ctx) (x : ty) : Type :=
| EA {y} : e_ctx Γ x y -> term Γ y -> eval_arg Γ x.
Arguments EA {Γ x y}.

(* efficiently find the first redex in E[t] *)
Equations e_focus {Γ x} : eval_arg Γ x -> e_term Γ x :=
  e_focus (EA E t) := focus_aux.focus_aux E (inl t).


(************************************)
(* evaluation to eager normal forms *)

Variant e_nf (Γ : ctx) (x : ty) : Type :=
| NVal : e_val Γ x -> e_nf Γ x
| NRed {a b} : e_ctx Γ x b -> Γ ∋ a -> e_redex Γ a b -> e_nf Γ x
.
Arguments NVal {Γ x}.
Arguments NRed {Γ x a b}.

Definition t_env : Type := ctx * ty.
Definition neg_t_env : Type := neg_ctx * ty.
Definition of_nte : neg_t_env -> t_env := fun '(Γ , x) => (of_n_ctx Γ , x).
Coercion of_nte : neg_t_env >-> t_env.

(*
Definition term' := t_uncurry term.
Definition e_nf' := t_uncurry e_nf.
Definition e_val' := t_uncurry e_val.
*)

(* one evaluation step on focused terms (e_term) *)
Equations eval_aux {Γ x} (t : e_term Γ x) : eval_arg Γ x + e_nf Γ x :=
  eval_aux (EVal v)                   := inr (NVal v) ;
  eval_aux (ERed E (VVar i) r)        := inr (NRed E i r) ;
  eval_aux (ERed E (VRec u) (RApp v)) :=
    inl (EA E (u /ₛ t_shift (t_of_val v) /ₛ Rec u)) ;
  eval_aux (ERed E (VLam u) (RApp v)) :=
    inl (EA E (u /ₛ t_of_val v)) ;
  eval_aux (ERed E (VPair u0 u1) (RPMatch a)) :=
    inl (EA E (a /ₛ t_shift (t_of_val u1) /ₛ t_of_val u0)) ;
  eval_aux (ERed E (VInl u) (RSMatch a b)) :=
    inl (EA E (a /ₛ t_of_val u)) ;
  eval_aux (ERed E (VInr u) (RSMatch a b)) :=
    inl (EA E (b /ₛ t_of_val u)) .

Definition eval_enf {Γ x} : eval_arg Γ x -> itree₀ ∅ₑ (e_nf Γ x) :=
  iterₐ (ret₀ ∘ eval_aux ∘ e_focus).

(* visible part of a type (will occur in traces), this is what is called
   "abstract values" in OGS. *)
Inductive a_val (Γ : neg_ctx) : ty -> Type :=
| AArr {a b} : a_val Γ (a → b)
| APair {a b} : a_val Γ a -> a_val Γ b -> a_val Γ (a × b)
| AInl {a b} : a_val Γ a -> a_val Γ (a + b)
| AInr {a b} : a_val Γ b -> a_val Γ (a + b)
.
Derive NoConfusion for a_val.
Arguments AArr {Γ a b}.
Arguments APair {Γ a b}.
Arguments AInl {Γ a b}.
Arguments AInr {Γ a b}.


Equations a_cext {Γ x} : a_val Γ x -> neg_ctx :=
  a_cext (@AArr a b)   := nil ▶ ((a → b)%ty ,& NArr) ;
  a_cext (APair u v)   := a_cext u +▶ a_cext v ;
  a_cext (AInl u)      := a_cext u ;
  a_cext (AInr u)      := a_cext u .

Ltac r_fixup x :=
  cbn; unfold of_n_ctx in *;
  repeat rewrite map_app in *;
  eapply x;
  auto.

Equations t_of_a {Γ x} (u : a_val Γ x) : term (Γ +▶ a_cext u : neg_ctx) x :=
  t_of_a (AArr)      := Var top ;
  t_of_a (APair u v) := Pair (t_rename _ (t_of_a u)) (t_rename _ (t_of_a v));
  t_of_a (AInl u)    := Inl (t_of_a u) ;
  t_of_a (AInr u)    := Inr (t_of_a u) .
Obligation 1. r_fixup uconstr:(r_concat3_1). Qed.
Obligation 2. r_fixup uconstr:(r_concat3_2). Qed.

(* observable/queriable part of a type *)
Equations a_obs {Γ x} : a_val Γ x -> Type :=
  a_obs (@AArr a b) := a_val Γ a ;
  a_obs (APair u v) := a_obs u + a_obs v ;
  a_obs (AInl u)    := a_obs u ;
  a_obs (AInr u)    := a_obs u .

Equations a_cont {Γ x} (v : a_val Γ x) : a_obs v -> neg_t_env :=
  a_cont (@AArr a b) v       := (Γ +▶ a_cext v , b) ;
  a_cont (APair u v) (inl o) := a_cont u o ;
  a_cont (APair u v) (inr o) := a_cont v o ;
  a_cont (AInl u)    o       := a_cont u o ;
  a_cont (AInr u)    o       := a_cont u o .

Definition term' : neg_t_env -> Type := uncurry2 (term ∘ of_n_ctx).

Equations a_of_val {Γ : neg_ctx} x (v : e_val Γ x) : a_val Γ x :=
  a_of_val (_ → _) v           := AArr ;
  a_of_val (_ × _) (VPair u v) := APair (a_of_val _ u) (a_of_val _ v) ;
  a_of_val (_ + _) (VInl u)    := AInl (a_of_val _ u) ;
  a_of_val (_ + _) (VInr u)    := AInr (a_of_val _ u) ;

  a_of_val (Unit)  (VVar i) with neg_var i := { | (!) } ;
  a_of_val (_ × _) (VVar i) with neg_var i := { | (!) } ;
  a_of_val (_ + _) (VVar i) with neg_var i := { | (!) } .
Arguments a_of_val {Γ x}.

Equations apply_obs {Γ : neg_ctx} x (v : e_val Γ x) (o : a_obs (a_of_val v))
           : term' (a_cont (a_of_val v) o) :=
  apply_obs (_ → _) v           o := App (t_rename _ (t_of_val v)) (t_of_a o) ;
  apply_obs (_ × _) (VPair u v) (inl o) := apply_obs _ u o ;
  apply_obs (_ × _) (VPair u v) (inr o) := apply_obs _ v o ;
  apply_obs (_ + _) (VInl u)    o := apply_obs _ u o ;
  apply_obs (_ + _) (VInr u)    o := apply_obs _ u o ;

  apply_obs (Unit)  (VVar i)    o with neg_var i := { | (!) } ;
  apply_obs (_ × _) (VVar i)    o with neg_var i := { | (!) } ;
  apply_obs (_ + _) (VVar i)    o with neg_var i := { | (!) } .
Obligation 1. r_fixup uconstr:(r_concat_l). Qed.
Arguments apply_obs {Γ x}.


Variant enf_qry (Γ : neg_ctx) (x : ty) : Type :=
| LVal : a_val Γ x -> enf_qry Γ x
| LRed a b : Γ ∋ (a → b) -> a_val Γ a -> enf_qry Γ x.
Arguments LVal {Γ x}.
Arguments LRed {Γ x} a b.

Equations enf_rsp Γ x : enf_qry Γ x -> Type :=
  enf_rsp Γ x (LVal v) := a_obs v ;
  enf_rsp Γ x (LRed a b i v) := a_obs v + a_val Γ b .
  (* a_obs v   := continue on value
     a_val Γ b := continue on context, giving abstract result of opponent function *)

Equations enf_nxt Γ x (q : enf_qry Γ x) : enf_rsp Γ x q -> neg_t_env :=
  enf_nxt Γ x (LVal v)       o       := a_cont v o ;
  enf_nxt Γ x (LRed a b i v) (inl o) := a_cont v o ;
  enf_nxt Γ x (LRed a b i v) (inr v) := (Γ +▶ a_cext v , x) .

Definition enf_e : event neg_t_env neg_t_env :=
  Event (uncurry2 enf_qry)
        (uncurry2 enf_rsp)
        (uncurry2 enf_nxt).

Canonical enf_e.

Definition lassen : endo (neg_t_env -> Type) := itree enf_e.

Definition eval_arg' : neg_t_env -> Type := uncurry2 (eval_arg ∘ of_n_ctx).

Definition lassen_val {Γ : neg_ctx} {x} (v : e_val Γ x)
           : lassen (eval_arg' +ᵢ ∅ᵢ) (Γ , x) :=
  vis (LVal (a_of_val v) : qry enf_e (Γ , x))
      (fun o => ret (inl (EA EHole (apply_obs v o)))).

Equations lassen_enf {Γ : neg_ctx} {x} (v : e_nf Γ x)
          : lassen (eval_arg' +ᵢ ∅ᵢ) (Γ , x) :=
  lassen_enf (NVal v)     := lassen_val v ;
  lassen_enf (NRed E i r) with neg_var i := {
    lassen_enf (NRed E i (RApp v)) NArr :=
      vis (LRed _ _ i (a_of_val v) : qry enf_e (_,_))
          (λ { | inl o => ret (inl (EA EHole (apply_obs v o))) ;
               | inr v    => ret (inl _) })
                                           }.
Obligation 1.
  refine (EA _ _).
  + refine (e_rename _ E); r_fixup uconstr:(r_concat_l).
  + refine (t_of_a v).
Qed.

Definition eval_lassen : eval_arg' ⇒ᵢ lassen ∅ᵢ :=
  iter (fun '(_ , _) t => emb_comp _ _ (eval_enf t) !>= lassen_enf).

(****************************************)
(* various proofs on eager normal forms *)

(* useless for now
Equations t_of_e_term {Γ x} : e_term Γ x -> term Γ x :=
  t_of_e_term (EVal v) := t_of_val v ;
  t_of_e_term (ERed E v r) := e_plug E (t_of_red (t_of_val v) r) .

Equations t_of_red {Γ x y} : term Γ x -> e_redex Γ x y -> term Γ y :=
  t_of_red e (RApp v) := App e (t_of_val v) ;
  t_of_red e (RPMatch a) := PMatch e a .

Equations t_of_e_nf {Γ x} : e_nf Γ x -> term Γ x :=
  t_of_e_nf (NVal v) := t_of_val v ;
  t_of_e_nf (NRed E i r) := e_plug E (t_of_red (Var i) r).

Lemma e_split_val {Γ x} (v : e_val Γ x) : e_split (t_of_val v) = EVal v.
  destruct v; auto.
Qed.


Lemma e_split_correct {Γ x} (t : term Γ x) : t_of_e_term (e_split t) = t.
  funelim (e_split t); intros; cbn in *.
  + f_equal.
  + f_equal.
  + rewrite Heq in Hind. rewrite Heq, <-Hind. reflexivity.
  + rewrite Heq0; cbn; rewrite Heq.
    rewrite Heq in Hind; rewrite Heq0 in Hind0.
    rewrite <-Hind, <-Hind0. reflexivity.
  + rewrite Heq0; cbn; rewrite Heq.
    rewrite Heq in Hind; rewrite Heq0 in Hind0.
    rewrite <-Hind, <-Hind0. reflexivity.
Qed.

Lemma e_split_coherent {Γ x} (t : e_term Γ x) : e_split (t_of_e_term t) = t.
  funelim (t_of_e_term t).
  + destruct e; auto.
  + revert e1 e2; induction e0; intros; cbn.
    - destruct (e_split (t_of_val e2)) eqn:H; cbn;
        rewrite (e_split_val e2) in H;
        try discriminate H;
        injection H as ->.
      destruct (e_split (t_of_val e1)) eqn:H; cbn;
        rewrite (e_split_val e1) in H;
        try discriminate H;
        injection H as ->.
      reflexivity.
    - cbn in IHe0; rewrite (IHe0 e1 e2); reflexivity.
    - destruct (e_split (t_of_val e)) eqn:H; cbn;
        rewrite (e_split_val e) in H;
        try discriminate H;
        injection H as ->.
      cbn in IHe0; rewrite (IHe0 e1 e2); reflexivity.
Qed.

Lemma e_split_unique {Γ x} {a : term Γ x} {b} : a = t_of_e_term b <-> e_split a = b.
  econstructor; intro p.
  rewrite<- (e_split_coherent b); f_equal; exact p.
  rewrite<- (e_split_correct a); f_equal; exact p.
Qed.

Lemma e_split_inj {Γ a} {x y : term Γ a} (p : e_split x = e_split y) : x = y.
  rewrite<- e_split_correct, e_split_unique.
  exact p.
Qed.
*)
