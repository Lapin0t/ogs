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

(*Definition snoc (Γ : ctx) (x : ty) : ctx := x :: Γ.*)
Notation "Γ ▶ x" := (x :: Γ) (at level 20).

Inductive has : ctx -> ty -> Type :=
| top {Γ x} : has (Γ ▶ x) x
| pop {Γ x y} : has Γ x -> has (Γ ▶ y) x.

Notation "Γ ∋ t" := (has Γ t) (at level 30).
Definition pop' {Γ} : forall t, Γ ∋ t -> (Γ ▶ t) ∋ t := fun _ => pop.

Equations has_get Γ i : Γ ∋ (Γ.[i]) :=
  has_get (x :: xs) F0 := top ;
  has_get (x :: xs) (FS i) := pop (has_get xs i) .

Inductive term : ctx -> ty -> Type :=
| Var {Γ a} (i : Γ ∋ a) : term Γ a
| Lam {Γ a b} (u : term (Γ ▶ a) b) : term Γ (a → b)
| App {Γ a b} (u : term Γ (a → b)) (v : term Γ a) : term Γ b
| Pair {Γ a b} (u : term Γ a) (v : term Γ b) : term Γ (a × b)
| Fst {Γ a b} (u : term Γ (a × b)) : term Γ a
| Snd {Γ a b} (u : term Γ (a × b)) : term Γ b
| Letrec {Γ a} (u : term (Γ ▶ a) a) : term Γ a
.


Equations t_rename {Γ Δ} (f : forall t, Γ ∋ t -> Δ ∋ t) {t} : term Γ t -> term Δ t :=
  t_rename f (Var i)        := Var (f _ i) ;
  t_rename f (App u v)      := App (t_rename f u) (t_rename f v) ;
  t_rename f (@Lam _ a _ u) := Lam (t_rename f' u)
    where f' : forall t, (_ ▶ a) ∋ t -> (_ ▶ a) ∋ t := {
          f' _ top := top ;
          f' _ (pop i) := pop (f _ i) } ;
  t_rename f (Pair u v)     := Pair (t_rename f u) (t_rename f v) ;
  t_rename f (Fst u)        := Fst (t_rename f u) ;
  t_rename f (Snd u)        := Snd (t_rename f u) ;
  t_rename f (@Letrec _ a u) := Letrec (t_rename f' u)
    where f' : forall t, (_ ▶ a) ∋ t -> (_ ▶ a) ∋ t := {
          f' _ top := top ;
          f' _ (pop i) := pop (f _ i) } .

Definition t_shift {Γ} {x y} : term Γ x -> term (Γ ▶ y) x :=
  t_rename (fun _ => pop).

Equations t_subst {Γ Δ} (f : forall t, Γ ∋ t -> term Δ t) {t} : term Γ t -> term Δ t :=
  t_subst f (Var i)        := f _ i ;
  t_subst f (App u v)      := App (t_subst f u) (t_subst f v) ;
  t_subst f (@Lam _ a _ u) := Lam (t_subst f' u)
    where f' : forall t, (_ ▶ a) ∋ t -> term (_ ▶ a) t := {
          f' _ top := Var top ;
          f' _ (pop i) := t_shift (f _ i) } ;
  t_subst f (Pair u v)     := Pair (t_subst f u) (t_subst f v) ;
  t_subst f (Fst u)        := Fst (t_subst f u) ;
  t_subst f (Snd u)        := Snd (t_subst f u) ;
  t_subst f (@Letrec _ a u) := Letrec (t_subst f' u)
    where f' : forall t, (_ ▶ a) ∋ t -> term (_ ▶ a) t := {
          f' _ top := Var top ;
          f' _ (pop i) := t_shift (f _ i) } .

Equations t_subst1 {Γ a b} (u : term (Γ ▶ a) b) (v : term Γ a) : term Γ b :=
  t_subst1 u v := t_subst f u
    where f : forall t, (Γ ▶ a) ∋ t -> term Γ t := {
          f _ top := v ;
          f _ (pop i) := Var i }.

Inductive e_val : ctx -> ty -> Type :=
| VVar {Γ x} : Γ ∋ x -> e_val Γ x
| VLam {Γ a b} : term (Γ ▶ a) b -> e_val Γ (a → b)
| VRec {Γ a} : term (Γ ▶ a) a -> e_val Γ a
| VPair {Γ a b} : e_val Γ a -> e_val Γ b -> e_val Γ (a × b)
.

Equations t_of_val {Γ x} : e_val Γ x -> term Γ x :=
  t_of_val (VVar i) := Var i ;
  t_of_val (VLam u) := Lam u ;
  t_of_val (VRec u) := Letrec u ;
  t_of_val (VPair u v) := Pair (t_of_val u) (t_of_val v) .

Inductive e_ctx (Γ : ctx) (t : ty) : ty -> Type :=
| EHole : e_ctx Γ t t
| EApp_l {a b} : e_ctx Γ t (a → b) -> term Γ a -> e_ctx Γ t b
| EApp_r {a b} : e_val Γ (a → b) -> e_ctx Γ t a -> e_ctx Γ t b
| EPair_l {a b} : e_ctx Γ t a -> term Γ b -> e_ctx Γ t (a × b)
| EPair_r {a b} : e_val Γ a -> e_ctx Γ t b -> e_ctx Γ t (a × b)
| EFst {a b} : e_ctx Γ t (a × b) -> e_ctx Γ t a
| ESnd {a b} : e_ctx Γ t (a × b) -> e_ctx Γ t b
.
Arguments EHole {Γ t}.
Arguments EApp_l {Γ t a b}.
Arguments EApp_r {Γ t a b}.
Arguments EPair_l {Γ t a b}.
Arguments EPair_r {Γ t a b}.
Arguments EFst {Γ t a b}.
Arguments ESnd {Γ t a b}.

Equations e_plug {Γ x y} (E : e_ctx Γ x y) : term Γ x -> term Γ y :=
  e_plug EHole t := t ;
  e_plug (EApp_r u E) t := App (t_of_val u) (e_plug E t) ;
  e_plug (EApp_l E u) t := App (e_plug E t) u ;
  e_plug (EPair_r u E) t := Pair (t_of_val u) (e_plug E t) ;
  e_plug (EPair_l E u) t := Pair (e_plug E t) u ;
  e_plug (EFst E)      t := Fst (e_plug E t) ;
  e_plug (ESnd E)      t := Snd (e_plug E t) .

Equations e_concat {Γ x y z} : e_ctx Γ x y -> e_ctx Γ y z -> e_ctx Γ x z :=
  e_concat E0 EHole          := E0 ;
  e_concat E0 (EApp_l E1 u)  := EApp_l (e_concat E0 E1) u ;
  e_concat E0 (EApp_r u E1)  := EApp_r u (e_concat E0 E1) ;
  e_concat E0 (EPair_l E1 u) := EPair_l (e_concat E0 E1) u ;
  e_concat E0 (EPair_r u E1) := EPair_r u (e_concat E0 E1) ;
  e_concat E0 (EFst E1)      := EFst (e_concat E0 E1) ;
  e_concat E0 (ESnd E1)      := ESnd (e_concat E0 E1) .

Equations e_fill {Γ x y} : e_ctx Γ x y -> term (Γ ▶ x) y :=
  e_fill EHole := Var top ;
  e_fill (EApp_l E u) := App (e_fill E) (t_shift u) ;
  e_fill (EApp_r u E) := App (t_shift (t_of_val u)) (e_fill E) ;
  e_fill (EPair_l E u) := Pair (e_fill E) (t_shift u) ;
  e_fill (EPair_r u E) := Pair (t_shift (t_of_val u)) (e_fill E) ;
  e_fill (EFst E)      := Fst (e_fill E) ;
  e_fill (ESnd E)      := Snd (e_fill E) .

Variant e_redex (Γ : ctx) : ty -> ty -> Type :=
| RApp {a b} : e_val Γ a -> e_redex Γ (a → b) b
| RFst {a b} : e_redex Γ (a × b) a
| RSnd {a b} : e_redex Γ (a × b) b
.
Arguments RApp {Γ a b}.
Arguments RFst {Γ a b}.
Arguments RSnd {Γ a b}.

Equations t_of_red {Γ x y} : term Γ x -> e_redex Γ x y -> term Γ y :=
  t_of_red e (RApp v) := App e (t_of_val v) ;
  t_of_red e RFst := Fst e ;
  t_of_red e RSnd := Snd e.

Variant e_term (Γ : ctx) (x : ty) : Type :=
| EVal : e_val Γ x -> e_term Γ x
| ERed {a b} : e_ctx Γ b x -> e_val Γ a -> e_redex Γ a b -> e_term Γ x
.
Arguments EVal {Γ x}.
Arguments ERed {Γ x a b}.

(*
Equations e_plug_val {Γ x y} : e_ctx Γ x y -> e_val Γ x -> e_term Γ y :=
  e_plug_val EHole         v := EVal v ;
  e_plug_val (EApp_l E u)  v := _ ;
  e_plug_val (EApp_r u E)  v := _ ;
  e_plug_val (EPair_l E u) v := _ ;
  e_plug_val (EPair_r u E) v := _ ;
  e_plug_val (EFst E)      v := _ ;
  e_plug_val (ESnd E)      v :=  .
*)

Equations t_of_e_term {Γ x} : e_term Γ x -> term Γ x :=
  t_of_e_term (EVal v) := t_of_val v ;
  t_of_e_term (ERed E v r) := e_plug E (t_of_red (t_of_val v) r) .

Equations e_split {Γ x} : term Γ x -> e_term Γ x :=
  e_split (Var i) := EVal (VVar i) ;
  e_split (Lam u) := EVal (VLam u) ;
  e_split (App a b) with e_split a := {
    | EVal u0 with e_split b := {
      | EVal v0 := ERed EHole u0 (RApp v0) ;
      | ERed E v0 r := ERed (EApp_r u0 E) v0 r } ;
    | ERed E u0 r := ERed (EApp_l E b) u0 r } ;
  e_split (Pair a b) with e_split a := {
    | EVal u0 with e_split b := {
      | EVal v0 := EVal (VPair u0 v0) ;
      | ERed E v0 r := ERed (EPair_r u0 E) v0 r } ;
    | ERed E u0 r := ERed (EPair_l E b) u0 r } ;
  e_split (Fst a) with e_split a := {
    | EVal u0 := ERed EHole u0 RFst ;
    | ERed E u0 r := ERed (EFst E) u0 r } ;
  e_split (Snd a) with e_split a := {
    | EVal u0 := ERed EHole u0 RSnd ;
    | ERed E u0 r := ERed (ESnd E) u0 r } ;
  e_split (Letrec a) := EVal (VRec a) .
          
Variant e_nf (Γ : ctx) (x : ty) : Type :=
| NVal : e_val Γ x -> e_nf Γ x
| NRed {a b} : e_ctx Γ b x -> Γ ∋ a -> e_redex Γ a b -> e_nf Γ x
.
Arguments NVal {Γ x}.
Arguments NRed {Γ x a b}.

Equations t_of_e_nf {Γ x} : e_nf Γ x -> term Γ x :=
  t_of_e_nf (NVal v) := t_of_val v ;
  t_of_e_nf (NRed E i r) := e_plug E (t_of_red (Var i) r).

Record t_env : Type := TEnv { Ctx : ctx ; Ty : ty }.
Definition t_uncurry {A : ctx -> ty -> Type} (f : forall Γ x, A Γ x) i :=
  f i.(Ctx) i.(Ty).
Definition t_curry {A : ctx -> ty -> Type} (f : forall i, A i.(Ctx) i.(Ty)) Γ x :=
  f (TEnv Γ x).

Definition term' := t_uncurry term.
Definition e_nf' := t_uncurry e_nf.
Definition e_val' := t_uncurry e_val.

Equations eval_enf' {Γ x} (t : e_term Γ x) : itree₀ ∅ₑ (term Γ x + e_nf Γ x) :=
  eval_enf' (EVal v)                   := ret₀ (inr (NVal v)) ;
  eval_enf' (ERed E (VVar i) r)        := ret₀ (inr (NRed E i r)) ;
  eval_enf' (ERed E (VRec u) r)        := _ ;
  eval_enf' (ERed E (VLam u) (RApp v)) :=
    ret₀ (inl (e_plug E (t_subst1 u (t_of_val v)))) ;
  eval_enf' (ERed E (VPair u0 u1) RFst) := ret₀ (inl (e_plug E (t_of_val u0))) ;
  eval_enf' (ERed E (VPair u0 u1) RSnd) := ret₀ (inl (e_plug E (t_of_val u1))) .
Obligation 1.

Definition eval_enf {Γ x} : term Γ x -> itree₀ ∅ₑ (e_nf Γ x) :=
  iterₐ (eval_enf' ∘ e_split).

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
