Require Import Psatz.
From ExtLib.Data Require Import Nat Fin List Unit.
From Coq Require Import Logic.
Import EqNotations.
From Equations Require Import Equations.

From OGS Require Import EventD CatD ITreeD Utils RecD AngelicD.

Set Primitive Projections.
Set Equations Transparent.

Inductive ty : Type :=
| Base : ty
| Prod : ty -> ty -> ty
| Arr : ty -> ty -> ty.
Derive NoConfusion for ty.

Declare Scope ty_scope.
Delimit Scope ty_scope with ty.
Bind Scope ty_scope with ty.
Notation "A → B" := (Arr A B) (at level 40) : ty_scope .
Notation "A × B" := (Prod A B) (at level 40) : ty_scope.

Definition ctx : Type := list ty.
Definition elt (Γ : ctx) : Type := fin (length Γ).

Notation "Γ ▶ x" := (x :: Γ) (at level 20).

Inductive has : ctx -> ty -> Type :=
| top {Γ x} : has (Γ ▶ x) x
| pop {Γ x y} : has Γ x -> has (Γ ▶ y) x.
Notation "Γ ∋ t" := (has Γ t) (at level 30).

Equations has_get Γ i : Γ ∋ (Γ.[i]) :=
  has_get (x :: xs) F0 := top ;
  has_get (x :: xs) (FS i) := pop (has_get xs i) .

Inductive term : ctx -> ty -> Type :=
| Var {Γ a} (i : Γ ∋ a) : term Γ a
| Lam {Γ a b} (u : term (Γ ▶ a) b) : term Γ (a → b)
| App {Γ a b} (u : term Γ (a → b)) (v : term Γ a) : term Γ b
| Pair {Γ a b} (u : term Γ a) (v : term Γ b) : term Γ (a × b)
| PMatch {Γ a b x} (u : term Γ (a × b)) (v : term (Γ ▶ a ▶ b) x) : term Γ x
| Rec {Γ a b} (u : term (Γ ▶ (a → b)%ty ▶ a) b) : term Γ (a → b)
.

(*****************************)
(* renaming and substitution *)

(* helper for defining various shiftings of renamings and substitutions *)
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

Equations t_rename {Γ Δ} (f : forall t, Γ ∋ t -> Δ ∋ t) {t} : term Γ t -> term Δ t :=
  t_rename f (Var i)        := Var (f _ i) ;
  t_rename f (App u v)      := App (t_rename f u) (t_rename f v) ;
  t_rename f (Lam u)        := Lam (t_rename (r_shift f) u) ;
  t_rename f (Pair u v)     := Pair (t_rename f u) (t_rename f v) ;
  t_rename f (PMatch u v)   := PMatch (t_rename f u) (t_rename (r_shift2 f) v) ;
  t_rename f (Rec u)        := Rec (t_rename (r_shift (r_shift f)) u).

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
  t_subst f (App u v)     := App (t_subst f u) (t_subst f v) ;
  t_subst f (Lam u)       := Lam (t_subst (s_shift f) u) ;
  t_subst f (Pair u v)    := Pair (t_subst f u) (t_subst f v) ;
  t_subst f (PMatch u v)  := PMatch (t_subst f u) (t_subst (s_shift2 f) v) ;
  t_subst f (Rec u)       := Rec (t_subst (s_shift2 f) u) .

Equations t_subst1 {Γ a b} (u : term (Γ ▶ a) b) (v : term Γ a) : term Γ b :=
  t_subst1 u v := t_subst f u
    where f : forall t, (Γ ▶ a) ∋ t -> term Γ t := {
          f _ top := v ;
          f _ (pop i) := Var i }.

Notation "u /ₛ v" := (t_subst1 u v) (at level 50, left associativity).

(**************************************************)
(* Eager values, evaluation contexts, redexes etc *)

Inductive e_val : ctx -> ty -> Type :=
| VVar {Γ x} : Γ ∋ x -> e_val Γ x
| VLam {Γ a b} : term (Γ ▶ a) b -> e_val Γ (a → b)
| VRec {Γ a b} : term (Γ ▶ (a → b)%ty ▶ a) b -> e_val Γ (a → b)
| VPair {Γ a b} : e_val Γ a -> e_val Γ b -> e_val Γ (a × b)
.

Equations t_of_val {Γ x} : e_val Γ x -> term Γ x :=
  t_of_val (VVar i) := Var i ;
  t_of_val (VLam u) := Lam u ;
  t_of_val (VRec u) := Rec u ;
  t_of_val (VPair u v) := Pair (t_of_val u) (t_of_val v) .

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
.
Arguments EHole {Γ t}.
Arguments EApp_l {Γ t a b}.
Arguments EApp_r {Γ t a b}.
Arguments EPair_l {Γ t a b}.
Arguments EPair_r {Γ t a b}.
Arguments EPMatch {Γ t a b x}.

(* useless? now that we work efficiently
Equations e_plug {Γ x y} : e_ctx Γ y x -> term Γ x -> term Γ y :=
  e_plug EHole         t := t ;
  e_plug (EApp_r E u)  t := e_plug E (App (t_of_val u) t) ;
  e_plug (EApp_l E u)  t := e_plug E (App t u) ;
  e_plug (EPair_r E u) t := e_plug E (Pair (t_of_val u) t) ;
  e_plug (EPair_l E u) t := e_plug E (Pair t u) ;
  e_plug (EPMatch E u) t := e_plug E (PMatch t u) .

Equations e_concat {Γ x y z} : e_ctx Γ z y -> e_ctx Γ y x -> e_ctx Γ z x :=
  e_concat E0 EHole          := E0 ;
  e_concat E0 (EApp_l E1 u)  := EApp_l (e_concat E0 E1) u ;
  e_concat E0 (EApp_r E1 u)  := EApp_r (e_concat E0 E1) u ;
  e_concat E0 (EPair_l E1 u) := EPair_l (e_concat E0 E1) u ;
  e_concat E0 (EPair_r E1 u) := EPair_r (e_concat E0 E1) u ;
  e_concat E0 (EPMatch E1 u) := EPMatch (e_concat E0 E1) u .
*)

(* todo
Equations e_fill {Γ x y} : e_ctx Γ y x -> term (Γ ▶ x) y :=
  e_fill EHole := Var top ;
  e_fill (EApp_l E u) := App (e_fill E) (t_shift u) ;
  e_fill (EApp_r E u) := App (t_shift (t_of_val u)) (e_fill E) ;
  e_fill (EPair_l E u) := Pair (e_fill E) (t_shift u) ;
  e_fill (EPair_r E u) := Pair (t_shift (t_of_val u)) (e_fill E) ;
  e_fill (EPMatch E u) := PMatch (t_fill E) (t_shift u) .
*)

(* 'e_redex Γ x y' represents eliminators on term Γ x returning a term Γ y *)
Variant e_redex (Γ : ctx) : ty -> ty -> Type :=
| RApp {a b} : e_val Γ a -> e_redex Γ (a → b) b
| RPMatch {a b x} : term (Γ ▶ a ▶ b) x -> e_redex Γ (a × b) x
.
Arguments RApp {Γ a b}.
Arguments RPMatch {Γ a b x}.

Variant e_term (Γ : ctx) (x : ty) : Type :=
| EVal : e_val Γ x -> e_term Γ x
| ERed {a b} : e_ctx Γ x b -> e_val Γ a -> e_redex Γ a b -> e_term Γ x
.
Arguments EVal {Γ x}.
Arguments ERed {Γ x a b}.

Module EFocus.
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
  term_size (PMatch a b) := S (term_size a) ;
  term_size (Pair a b) := S (S (S (term_size a + term_size b))) .

Equations ctx_size {Γ y x} : e_ctx Γ y x -> nat :=
  ctx_size EHole := O ;
  ctx_size (EApp_l E u) := S (ctx_size E + term_size u) ;
  ctx_size (EApp_r E u) := O ;
  ctx_size (EPair_l E u) := S (S (ctx_size E + term_size u)) ;
  ctx_size (EPair_r E u) := S (ctx_size E) ;
  ctx_size (EPMatch E b) := O .

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
Equations e_focus' {Γ x y} (E : e_ctx Γ y x) (t : term Γ x + e_val Γ x)
                : e_term Γ y by wf (ctx_size E + aux_size t)%nat lt :=
  e_focus' E (inl (App a b)) := e_focus' (EApp_l E b) (inl a) ;
  e_focus' E (inl (Pair a b)) := e_focus' (EPair_l E b) (inl a) ;
  e_focus' E (inl (PMatch a b)) := e_focus' (EPMatch E b) (inl a) ;
  e_focus' E (inl (Rec a)) := e_focus' E (inr (VRec a)) ;
  e_focus' E (inl (Var i)) := e_focus' E (inr (VVar i)) ;
  e_focus' E (inl (Lam a)) := e_focus' E (inr (VLam a)) ;

  e_focus' EHole         (inr v) := EVal v ;
  e_focus' (EApp_l E u)  (inr v) := e_focus' (EApp_r E v) (inl u) ;
  e_focus' (EApp_r E u)  (inr v) := ERed E u (RApp v) ;
  e_focus' (EPair_l E u) (inr v) := e_focus' (EPair_r E v) (inl u) ;
  e_focus' (EPair_r E u) (inr v) := e_focus' E (inr (VPair u v)) ;
  e_focus' (EPMatch E b) (inr v) := ERed E v (RPMatch b)  .
Obligation 1. lia. Qed.
Obligation 2. lia. Qed.
Obligation 3. lia. Qed.
Obligation 4. lia. Qed.
Obligation 5. lia. Qed.
Obligation 6. lia. Qed.
Obligation 7. lia. Qed.
Obligation 8. lia. Qed.
End EFocus.

(* pack a term and an evaluation context *)
Variant eval_arg (Γ : ctx) (x : ty) : Type :=
| EA {y} : e_ctx Γ x y -> term Γ y -> eval_arg Γ x.
Arguments EA {Γ x y}.

(* efficiently find the first redex in E[t] *)
Equations e_focus {Γ x} : eval_arg Γ x -> e_term Γ x :=
  e_focus (EA E t) := EFocus.e_focus' E (inl t).


(************************************)
(* evaluation to eager normal forms *)

Variant e_nf (Γ : ctx) (x : ty) : Type :=
| NVal : e_val Γ x -> e_nf Γ x
| NRed {a b} : e_ctx Γ x b -> Γ ∋ a -> e_redex Γ a b -> e_nf Γ x
.
Arguments NVal {Γ x}.
Arguments NRed {Γ x a b}.

Record t_env : Type := TEnv { Ctx : ctx ; Ty : ty }.
Definition t_uncurry {A : ctx -> ty -> Type} (f : forall Γ x, A Γ x) i :=
  f i.(Ctx) i.(Ty).
Definition t_curry {A : ctx -> ty -> Type} (f : forall i, A i.(Ctx) i.(Ty)) Γ x :=
  f (TEnv Γ x).

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
    inl (EA E (a /ₛ t_shift (t_of_val u1) /ₛ t_of_val u0)) .

Definition eval_enf {Γ x} : eval_arg Γ x -> itree₀ ∅ₑ (e_nf Γ x) :=
  iterₐ (ret₀ ∘ eval_aux ∘ e_focus).

(* WIP below this point *)

(*
Variant polarity : Type := Neg | Pos.
Equations get_polarity : ty -> polarity :=
  get_polarity (a → b) := Neg ;
  get_polarity Base := Pos ;
  get_polarity (a × b) := Pos .
*)

Variant enf_qry (Γ : ctx) (x : ty) : Type :=
| NQVal : enf_qry Γ x
| NQRed a b : Γ ∋ (a → b) -> enf_qry Γ x.
Arguments NQVal {Γ x}.
Arguments NQRed {Γ x} a b.

Definition enf_rsp Γ x : enf_qry Γ x -> Type :=
  fun q => match q with
        | NQVal => match x with
                  | Base => T0    (* no opponent move on base type *)
                  | Prod a b => T0
                  | Arr a b => T1 (* sinle opponent move: evaluation *)
                  end
        | NQRed _ _ _ => T2 (* continue on context or evaluate argument *)
        end.

Definition enf_nxt Γ x (q : enf_qry Γ x) : enf_rsp Γ x q -> t_env.
  destruct q.
  + destruct x as [|a b|a b]; intros []. refine (TEnv (a :: Γ) b).
  + intros []. refine (TEnv (b :: Γ) x). refine (TEnv Γ a).
Defined.

Definition enf_e : event t_env t_env :=
  Event (t_uncurry enf_qry)
        (t_uncurry enf_rsp)
        (t_uncurry enf_nxt).

Definition lassen_tree (X : ctx -> ty -> Type) : ctx -> ty -> Type :=
  @t_curry (fun _ _ => Type) (itree enf_e (t_uncurry X)).


Definition lassen_val {Γ x} (v : e_val Γ x) : lassen_tree (fun Γ x => term Γ x + T0) Γ x.
  refine (Vis (NQVal : qry enf_e (TEnv Γ x)) _).
  destruct x; intros [].
  refine (Ret (inl _)).
  refine (App (t_shift (t_of_val v)) (Var top)).
Defined.

Definition lassen_enf {Γ x} (v : e_nf Γ x) : lassen_tree (fun Γ x => term Γ x + T0) Γ x.
  destruct v as [v | a b E i v].
  + refine (lassen_val v).
  + refine (Vis (NQRed a b i : qry enf_e (TEnv Γ x)) _).
    intros [].
    - refine (Ret (inl _)).
      refine (e_fill E).
    - refine (lassen_val v).
Defined.

Definition eval_lassen : forall Γ x, term Γ x -> lassen_tree (fun _ _ => T0) Γ x.
  refine (@t_curry (fun Γ x => term Γ x -> lassen_tree (fun _ _ => T0) Γ x) _).
  refine (iter (fun _ t => emb_comp _ _ (eval_enf t) >>= _)).
  refine (fun _ '(Fib a) => _).
  refine (lassen_enf a).
Defined.

(****************************************)
(* various proofs on eager normal forms *)

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
