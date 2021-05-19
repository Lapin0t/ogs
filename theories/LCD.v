From ExtLib.Data Require Import Nat Fin List Unit.
From Coq Require Import Logic.
Import EqNotations.
From Equations Require Import Equations.

From OGS Require Import EventD ITreeD Utils RecD.

Set Primitive Projections.
Set Equations Transparent.

Inductive Tele : Type :=
| Tnil : Tele
| Tcons (X : Type) : (X -> Tele) -> Tele
.

Equations Tfold (A : Type) : A -> (forall (X : Type), (X -> A) -> A) -> Tele -> A :=
  Tfold A a h Tnil := a ;
  Tfold A a h (Tcons X T) := h X (fun x => Tfold A a h (T x)) .

Definition Tsg := Tfold Type unit (fun X f => {x : X & f x }).
Definition Tpi (A : Type) := Tfold Type A (fun X f => forall (x : X), f x).

Equations curry T {A} : (Tsg T -> A) -> Tpi A T :=
  curry Tnil f := f tt ;
  curry (Tcons X T) f := fun x => curry (T x) (fun r => f (existT _ x r)) .

Equations uncurry_ T {A} : Tpi A T -> Tsg T -> A :=
  uncurry_ Tnil x _ := x ;
  uncurry_ (Tcons X T) f (existT _ x r) := uncurry_ (T x) (f x) r .

Ltac mk_tele_ ty :=
  match ty with
  | ?X -> ?T => let t := mk_tele_ T in uconstr:(Tcons X (fun _ => t))
  | forall (x : ?X), ?T => let t := mk_tele_ T in uconstr:(Tcons X (fun _ => t))
  | ?T => uconstr:(Tnil)
  end.
Ltac mk_tele tm := let ty := type of tm in mk_tele_ ty.
Notation mk_tele tm := (ltac:(let t := mk_tele tm in exact t)).
Notation uncurry f := (uncurry_ (mk_tele f) f). 

Inductive ty : Type :=
| Base : ty
| Arr : ty -> ty -> ty.
Derive NoConfusion for ty.

Notation "A =:> B" := (Arr A B) (at level 60).

Definition ctx : Type := list ty.
Definition elt (Γ : ctx) : Type := fin (length Γ).

Inductive has : ctx -> ty -> Type :=
| top {Γ x} : has (x :: Γ) x
| pop {Γ x y} : has Γ x -> has (y :: Γ) x.

Notation "Γ ∋ t" := (has Γ t) (at level 30).
Definition pop' {Γ} : forall t, Γ ∋ t -> (t :: Γ) ∋ t := fun _ => pop.

Equations has_get Γ i : Γ ∋ (Γ.[i]) :=
  has_get (x :: xs) F0 := top ;
  has_get (x :: xs) (FS i) := pop (has_get xs i) .

Inductive term : ctx -> ty -> Type :=
| Var {Γ a} (i : Γ ∋ a) : term Γ a
| Lam {Γ a b} (u : term (a :: Γ) b) : term Γ (a =:> b)
| App {Γ a b} (u : term Γ (a =:> b)) (v : term Γ a) : term Γ b.

(* t_ctx Γ a Δ b := term Γ a --o term Δ b *)
Inductive t_ctx (Γ : ctx) (t : ty) : ctx -> ty -> Type :=
| CHole : t_ctx Γ t Γ t
| CApp_l {Δ a b} : term Δ (a =:> b) -> t_ctx Γ t Δ a -> t_ctx Γ t Δ b
| CApp_r {Δ a b} : t_ctx Γ t Δ (a =:> b) -> term Δ a -> t_ctx Γ t Δ b
| CLam {Δ a b} : t_ctx Γ t (a :: Δ) b -> t_ctx Γ t Δ (a =:> b).
Arguments CHole {Γ t}.
Arguments CApp_l {Γ t Δ a b}.
Arguments CApp_r {Γ t Δ a b}.
Arguments CLam {Γ t Δ a b}.

Equations plug {Γ Δ a b} : t_ctx Γ a Δ b -> term Γ a -> term Δ b :=
  plug CHole t := t ;
  plug (CApp_r C u) t := App (plug C t) u ;
  plug (CApp_l u C) t := App u (plug C t);
  plug (CLam C) t := Lam (plug C t).

Equations t_rename {Γ Δ} (f : forall t, Γ ∋ t -> Δ ∋ t) {t} : term Γ t -> term Δ t :=
  t_rename f (Var i)        := Var (f _ i) ;
  t_rename f (App u v)      := App (t_rename f u) (t_rename f v) ;
  t_rename f (@Lam _ a _ u) := Lam (t_rename f' u)
    where f' : forall t, (a :: _) ∋ t -> (a :: _) ∋ t := {
          f' _ top := top ;
          f' _ (pop i) := pop (f _ i) }.

Definition t_shift {Γ} {x y} : term Γ x -> term (y :: Γ) x :=
  t_rename (fun _ => pop).


Equations t_subst {Γ Δ} (f : forall t, Γ ∋ t -> term Δ t) {t} : term Γ t -> term Δ t :=
  t_subst f (Var i)        := f _ i ;
  t_subst f (App u v)      := App (t_subst f u) (t_subst f v) ;
  t_subst f (@Lam _ a _ u) := Lam (t_subst f' u)
    where f' : forall t, (a :: _) ∋ t -> term (a :: _) t := {
          f' _ top := Var top ;
          f' _ (pop i) := t_shift (f _ i) }.

Equations t_subst1 {Γ a b} (u : term (a :: Γ) b) (v : term Γ a) : term Γ b :=
  t_subst1 u v := t_subst f u
    where f : forall t, (a :: Γ) ∋ t -> term Γ t := {
          f _ top := v ;
          f _ (pop i) := Var i }.

Variant e_val : ctx -> ty -> Type :=
| VVar {Γ x} : Γ ∋ x -> e_val Γ x
| VLam {Γ a b} : term (a :: Γ) b -> e_val Γ (a =:> b)
.

Equations t_of_val {Γ x} : e_val Γ x -> term Γ x :=
  t_of_val (VVar i) := Var i ;
  t_of_val (VLam u) := Lam u.

Inductive e_ctx (Γ : ctx) (t : ty) : ctx -> ty -> Type :=
| EHole : e_ctx Γ t Γ t
| EApp_l {Δ a b} : term Δ (a =:> b) -> e_ctx Γ t Δ a -> e_ctx Γ t Δ b
| EApp_r {Δ a b} : e_ctx Γ t Δ (a =:> b) -> e_val Δ a -> e_ctx Γ t Δ b
.
Arguments EHole {Γ t}.
Arguments EApp_l {Γ t Δ a b}.
Arguments EApp_r {Γ t Δ a b}.

Equations e_plug {Γ x Δ y} (E : e_ctx Γ x Δ y) : term Γ x -> term Δ y :=
  e_plug EHole t := t ;
  e_plug (EApp_l u E) t := App u (e_plug E t) ;
  e_plug (EApp_r E u) t := App (e_plug E t) (t_of_val u) .

Equations e_fill {Γ x Δ y} : e_ctx Γ x Δ y -> term (x :: Δ) y :=
  e_fill EHole := Var top ;
  e_fill (EApp_l u E) := App (t_shift u) (e_fill E) ;
  e_fill (EApp_r E u) := App (e_fill E) (t_shift (t_of_val u)) .

Variant e_term (Γ : ctx) (x : ty) : Type :=
| EVal : e_val Γ x -> e_term Γ x
| ERed {Δ a b} : e_ctx Δ b Γ x -> e_val Δ (a =:> b) -> e_val Δ a -> e_term Γ x
.
Arguments EVal {Γ x}.
Arguments ERed {Γ x Δ a b}.

Equations t_of_e_term {Γ x} : e_term Γ x -> term Γ x :=
  t_of_e_term (EVal v) := t_of_val v ;
  t_of_e_term (ERed E v0 v1) := e_plug E (App (t_of_val v0) (t_of_val v1)).

Equations e_split {Γ x} : term Γ x -> e_term Γ x :=
  e_split (Var i) := EVal (VVar i) ;
  e_split (Lam u) := EVal (VLam u) ;
  e_split (App a b) with e_split b := {
    | EVal v0 with e_split a := {
      | EVal u0 := ERed EHole u0 v0 ;
      | ERed E u0 u1 := ERed (EApp_r E v0) u0 u1 } ;
    | ERed E v0 v1 := ERed (EApp_l a E) v0 v1 }.

Variant e_nf (Γ : ctx) (x : ty) : Type :=
| NVal : e_val Γ x -> e_nf Γ x
| NRed {Δ a b} : e_ctx Δ b Γ x -> Δ ∋ (a =:> b) -> e_val Δ a -> e_nf Γ x
.
Arguments NVal {Γ x}.
Arguments NRed {Γ x Δ a b}.

Equations t_of_e_nf {Γ x} : e_nf Γ x -> term Γ x :=
  t_of_e_nf (NVal v) := t_of_val v ;
  t_of_e_nf (NRed E i v) := e_plug E (App (Var i) (t_of_val v)).

Definition t_ix : Type := Tsg (mk_tele term).
Definition term' : t_ix -> Type := uncurry term.
Definition e_nf' : t_ix -> Type := uncurry e_nf.

Definition t_to_t' {Γ x} (t : term Γ x) : term' (existT _ Γ (existT _ x tt)) := t.
Definition t'_to_t {i} (t : term' i) : term (projT1 i) (projT1 (projT2 i)).
  destruct i as [ Γ [ x [] ] ]; auto.
Defined.
Definition n_to_n' {Γ x} (t : e_nf Γ x) : e_nf' (existT _ Γ (existT _ x tt)) := t.
Definition n'_to_n {i} (t : e_nf' i) : e_nf (projT1 i) (projT1 (projT2 i)).
  destruct i as [ Γ [ x [] ] ]; auto.
Defined.

Definition to_ix (Γ : ctx) (x : ty) : t_ix := existT _ Γ (existT _ x tt).
(*Definition from_ix t_ix : t_ix := existT _ Γ (existT _ x tt).*)

Equations eval_enf' {i} (t : term' i) : itree (esum (Event term' (fun i _ => e_nf' i) (fun i _ _ => i)) evoid) e_nf' i :=
  @eval_enf' (existT _ Γ (existT _ x tt)) t with e_split t := {
     | EVal v => Ret (n_to_n' (NVal v)) ;
     | ERed E (VVar i) v => Ret (n_to_n' (NRed E i v)) ;
     | ERed E (VLam u) v => Vis _ _
    }.
Obligation 1. exact (inl (e_plug E (t_subst1 u (t_of_val v)))). Defined.
Obligation 2. exact (Ret (n_to_n' r)). Defined.

Definition eval_enf {i} (t : term' i) : itree evoid e_nf' i.
  refine (mrec _ _ _ ?>= _).
  intros j q.
  
  mrec eval_enf'.

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
