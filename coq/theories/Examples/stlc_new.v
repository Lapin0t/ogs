(** * Minimal example: Call-by-Value Simply Typed Lambda Calculus

We demonstrate how to instantiate our framework to define the OGS associated to
for the cbv lambda-calculus. With the instance comes the proof that bisimilarity
of the OGS entails substitution equivalence, which coincides with ciu-equivalence.¹

Note: in order to fit into our abstract result, the calculus's dynamics is
presented as an abstract machine. See the paper for an extended discussion.

Remark: this example is designed to be minimal, hiding by nature some difficulties.
In particular, it has no positive types.

¹ See paper, formal proof omitted here.
*)

From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel Ctx.
From OGS.Game Require Import Event.
From OGS.ITree Require Import ITree Eq Delay Structure Properties.
Set Equations Transparent.

(** * Syntax *)

(* Non-polarised types: we only consider a ground type ι and arrow types *)
Inductive ty0 : Type :=
| ι : ty0
| Arr : ty0 -> ty0 -> ty0
.

Derive NoConfusion for ty0.
Declare Scope ty_scope.
Delimit Scope ty_scope with ty.
Bind Scope ty_scope with ty0.
Notation "A → B" := (Arr A B) (at level 40) : ty_scope .

(* Types [a] can be either polarised as producer [t+ a] or consumer [t- a] *)
Variant ty : Type :=
| VTy : ty0 -> ty
| KTy : ty0 -> ty
.
Derive NoConfusion for ty.
Bind Scope ty_scope with ty.
Notation "'t+' t" := (VTy t) (at level 20) : ty_scope .
Notation "'t-' t" := (KTy t) (at level 20) : ty_scope .
Open Scope ty_scope.

(* Swaping the polarity of a type *)
Equations t_neg : ty -> ty :=
  t_neg (t+ a) := t- a ;
  t_neg (t- a) := t+ a .

(* Typing contexts *)
Definition t_ctx : Type := Ctx.ctx ty.
Bind Scope ctx_scope with t_ctx.

(* Intrinsically typed configurations.
   Configurations (dubbed [state] here) are a pair ⟨e | π⟩ of a term and a context of opposite polarities.
   Top-level stlc terms [t] are embedded into configurations ⟨t | x⟩ with [x] a fresh variable.
 *)
Inductive term : t_ctx -> ty -> Type :=
| Val    {Γ a}   : val Γ a -> term Γ a
| App    {Γ a b} : term Γ (t+ (a → b)) -> term Γ (t+ a) -> term Γ (t+ b)
with val : t_ctx -> ty -> Type :=
| Var    {Γ a}   : Γ ∋ a -> val Γ a
| LamRec {Γ a b} : term (Γ ▶ t+ (a → b) ▶ t+ a) (t+ b) -> val Γ (t+ (a → b))
| KFun   {Γ a b} : term Γ (t+ (a → b)) -> val Γ (t- b) -> val Γ (t- a)
| KArg   {Γ a b} : val  Γ (t+ a) -> val Γ (t- b) -> val Γ (t- (a → b))
.

Variant state : t_ctx -> Type :=
| Cut {Γ a} : term Γ (t+ a) -> val Γ (t- a) -> state Γ
.

(* Embedding variables into values *)
Definition a_id {Γ} : has Γ ⇒ᵢ val Γ := fun _ => Var.

(* Renaming of values/terms/configurations *)
Equations t_rename {Γ Δ} : Γ ⊆ Δ -> term Γ ⇒ᵢ term Δ :=
  t_rename f _ (Val v)   := Val (v_rename f _ v) ;
  t_rename f _ (App u k) := App (t_rename f _ u) (t_rename f _ k) ;
with v_rename {Γ Δ} : Γ ⊆ Δ -> val Γ ⇒ᵢ val Δ :=
  v_rename f _ (Var i)    := Var (f _ i) ;
  v_rename f _ (LamRec u) := LamRec (t_rename (r_shift2 f) _ u) ;
  v_rename f _ (KFun t π) := KFun (t_rename f _ t) (v_rename f _ π) ;
  v_rename f _ (KArg u π) := KArg (v_rename f _ u) (v_rename f _ π) ;
.
Equations s_rename {Γ Δ} : Γ ⊆ Δ -> state Γ -> state Δ :=
  s_rename f (Cut v k) := Cut (t_rename f _ v) (v_rename f _ k).

(* Renaming in value assignments *)
Definition a_ren {Γ1 Γ2 Γ3} : Γ2 ⊆ Γ3 -> Γ1 =[val]> Γ2 -> Γ1 =[val]> Γ3 :=
  fun f g _ i => v_rename f _ (g _ i) .

(* Shiftings terms, values, configurations *)
Definition t_shift  {Γ} [y] : term Γ ⇒ᵢ term (Γ ▶ y)  := @t_rename _ _ s_pop.
Definition v_shift  {Γ} [y] : val Γ ⇒ᵢ val (Γ ▶ y)    := @v_rename _ _ s_pop.
Definition s_shift  {Γ} [y] : state Γ -> state (Γ ▶ y) := @s_rename _ _ s_pop.
Definition v_shift2  {Γ} [y z] : val Γ ⇒ᵢ val (Γ ▶ y ▶ z)  := @v_rename _ _ (s_pop ⊛ᵣ s_pop).

(* Shifting assignments *)
Definition a_shift {Γ Δ} [y] (a : Γ =[val]> Δ) : (Γ ▶ y) =[val]> (Δ ▶ y) :=
  s_append (fun _ i => v_shift _ (a _ i)) (Var top).
Definition a_shift2 {Γ Δ} [x y] (a : Γ =[val]> Δ) : (Γ ▶ x ▶ y) =[val]> (Δ ▶ x ▶ y) :=
  s_append (s_append (fun _ i => v_shift2 _ (a _ i))
              (Var (pop top)))
    (Var top).

(* Substitution (of values) in values/terms/configurations *)
Equations t_subst {Γ Δ} : Γ =[val]> Δ -> term Γ ⇒ᵢ term Δ :=
  t_subst f _ (Val v)   := Val (v_subst f _ v) ;
  t_subst f _ (App u k) := App (t_subst f _ u) (t_subst f _ k) ;
with v_subst {Γ Δ} : Γ =[val]> Δ -> val Γ ⇒ᵢ val Δ :=
  v_subst f _ (Var i)    := f _ i ;
  v_subst f _ (LamRec u) := LamRec (t_subst (a_shift2 f) _ u) ;
  v_subst f _ (KFun t π) := KFun (t_subst f _ t) (v_subst f _ π) ;
  v_subst f _ (KArg u π) := KArg (v_subst f _ u) (v_subst f _ π) ;
.
Equations s_subst {Γ Δ} : Γ =[val]> Δ -> state Γ -> state Δ :=
  s_subst f (Cut v k) := Cut (t_subst f _ v) (v_subst f _ k).

Definition a_comp {Γ1 Γ2 Γ3} : Γ2 =[val]> Γ3 -> Γ1 =[val]> Γ2 -> Γ1 =[val]> Γ3 :=
  fun f g _ i => v_subst f _ (g _ i) .

(* Substitution of a single variable and of a pair of variables *)
Definition ass1 {Γ a} (v : val Γ a) : (Γ ▶ a) =[val]> Γ := s_append a_id v .
Definition t_subst1  {Γ a b} (u : term (Γ ▶ a) b) v := t_subst (ass1 v) _ u.
Definition v_subst1  {Γ a b} (u : val (Γ ▶ a) b)  v := v_subst (ass1 v) _ u.
Definition s_subst1  {Γ a}   (u : state (Γ ▶ a))  v := s_subst (ass1 v) u.

Equations ass2 {Γ a b} (u : val Γ a) (v : val Γ b)
  : (Γ ▶ a ▶ b) =[val]> Γ :=
  ass2 u v _ top                 := v ;
  ass2 u v _ (pop top)           := u ;
  ass2 u v _ (pop (pop i))     := Var i.
Definition t_subst2 {Γ a b c} (x : term (Γ ▶ a ▶ b) c) (u : val Γ a) (v : val Γ b) : term Γ c
  := t_subst (ass2 u v) _ x.

Notation "u /ₜ v" := (t_subst1 u v) (at level 50, left associativity).
Notation "u /ᵥ v" := (v_subst1 u v) (at level 50, left associativity).
Notation "u /ₛ v" := (s_subst1 u v) (at level 50, left associativity).
Notation "u /ₜ[ v , w ]" := (t_subst2 u v w) (at level 50, left associativity).


(* As mentioned in preamble, this calculus is simple enough to hide subtleties.
   In the absence of positive types, patterns and their domains are reduced to the
   a variable.
   Patterns, their domains and conversions between values and patterns are therefore
   so degenerate that we omit the following definitions and simply inline them.
   In contrast, compare with the situation for [MuMuTilde] that features in particular
   positive types.
PB: TODO fix comment
*)

Variant pat : ty -> Type :=
| PPos {a} : pat (t+ a)
| PApp {a b} : pat (t- (a → b))
.

Equations pat_dom {a} : pat a -> t_ctx :=
  pat_dom (@PPos a)   := ∅ ▶ t+ a ;
  pat_dom (@PApp a b) := ∅ ▶ t+ a ▶ t- b .

(** * Normal forms
    Normal forms happen when stuck on a variable [x] of some type [a].
    I carries with it a value of the opposite polarity,
    i.e. normal forms can only be of two shapes, depending on the polarity of [a]:
    - for a producer type: "⟨ x | π ⟩"
    - for a consumer type: "⟨ v | x ⟩"
 *)
Definition nf0 (Γ : t_ctx) (a : ty) : Type := { p : pat a & pat_dom p =[val]> Γ } .
Definition nf  (Γ : t_ctx) : Type :=
  { a : ty & (Γ ∋ a * nf0 Γ (t_neg a))%type } .

(** * Evaluator
    The (call-by-value) evaluator. The reduction rules should come to no surprise:

    (1) ⟨ v | t ⋅ π ⟩ →  ⟨ t | [v] ⋅ π ⟩
    (2) ⟨ rec f(x).t | [v] ⋅ π ⟩ → ⟨ t[rec f(x).t/f, v/x] |  π ⟩
    (3) ⟨ t1 t2 | π ⟩ → ⟨ t2 | t1 ⋅ π ⟩

    (4) ⟨ v | x ⟩
    (5) ⟨ x | π ⟩

    Rules 1-3 step to a new configuration, while cases 4-5 are stuck
    on normal forms.

    We formalize here this evaluator by iteration in the delay monad, where
    case 4-5 take an explicit step translating trivially the configuration to
    the corresponding normal form.
 *)
Equations eval_aux {Γ : t_ctx} : state Γ -> (state Γ + nf Γ) :=
  eval_aux (Cut (App t1 t2)      (π))        := inl (Cut t2 (KFun t1 π)) ;
  eval_aux (Cut (Val v)          (Var i))    := inr (_ ,' (i, (PPos ,' s_append s_empty v))) ;
  eval_aux (Cut (Val v)          (KFun t π)) := inl (Cut t (KArg v π)) ;
  eval_aux (Cut (Val (Var i))    (KArg v π)) := inr (_,' (i, (PApp ,' (s_append (s_append s_empty v) π)))) ;
  eval_aux (Cut (Val (LamRec t)) (KArg v π)) := inl (Cut (t/ₜ[ LamRec t , v ]) π) .

Definition eval {Γ : t_ctx} : state Γ -> delay (nf Γ)
  := iter_delay (fun c => Ret' (eval_aux c)).

Definition p_app {Γ x} (v : val Γ x) (m : pat (t_neg x)) (γ : pat_dom m =[val]> Γ) : state Γ .
  destruct x; cbn in *; dependent elimination m; cbn in *.
  - exact (Cut (Val v) (KArg (γ _ (pop top)) (γ _ top))).
  - exact (Cut (Val (γ _ top)) v).
Defined.

Scheme term_mut := Induction for term Sort Prop
   with val_mut := Induction for val Sort Prop .

Record syn_ind_args (P_t : forall Γ A, term Γ A -> Prop)
                    (P_v : forall Γ A, val Γ A -> Prop) :=
  {
    ind_s_val {Γ a} v (_ : P_v Γ a v) : P_t Γ a (Val v) ;
    ind_s_app {Γ a b} t1 (_ : P_t Γ (t+ (a → b)) t1) t2 (_ : P_t Γ (t+ a) t2) : P_t Γ (t+ b) (App t1 t2) ;
    ind_s_var {Γ a} i : P_v Γ a (Var i) ;
    ind_s_lamrec {Γ a b} t (_ : P_t (Γ ▶ t+ (a → b) ▶ t+ a)%ctx (t+ b) t) : P_v Γ (t+ (a → b)) (LamRec t) ;
    ind_s_kfun {Γ a b} t (_ : P_t Γ (t+ (a → b)) t) π (_ : P_v Γ (t- b) π) : P_v Γ (t- a) (KFun t π) ;
    ind_s_karg {Γ a b} v (_ : P_v Γ (t+ a) v) π (_ : P_v Γ (t- b) π) : P_v Γ (t- (a → b)) (KArg v π) ;
  } .

Lemma term_ind_mut P_t P_v (H : syn_ind_args P_t P_v) Γ a t : P_t Γ a t .
  destruct H; now apply (term_mut P_t P_v).
Qed.

Lemma val_ind_mut P_t P_v (H : syn_ind_args P_t P_v) Γ a v : P_v Γ a v .
  destruct H; now apply (val_mut P_t P_v).
Qed.

Definition t_ren_proper_P Γ a (t : term Γ a) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> t_rename f1 a t = t_rename f2 a t .
Definition v_ren_proper_P Γ a (v : val Γ a) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> v_rename f1 a v = v_rename f2 a v .
Lemma ren_proper_prf : syn_ind_args t_ren_proper_P v_ren_proper_P.
  econstructor.
  all: unfold t_ren_proper_P, v_ren_proper_P.
  all: intros; cbn; f_equal; auto.
  now apply H.
  now apply H, r_shift_eq, r_shift_eq.
Qed.

#[global] Instance t_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@t_rename Γ Δ).
  intros f1 f2 H1 a x y ->; now apply (term_ind_mut _ _ ren_proper_prf).
Qed.

#[global] Instance v_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@v_rename Γ Δ).
  intros f1 f2 H1 a x y ->; now apply (val_ind_mut _ _ ren_proper_prf).
Qed.

#[global] Instance s_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> eq ==> eq) (@s_rename Γ Δ).
  intros f1 f2 H1 x y ->; destruct y; cbn; now rewrite H1.
Qed.

#[global] Instance a_ren_eq {Γ1 Γ2 Γ3}
  : Proper (ass_eq _ _ ==> ass_eq _ _ ==> ass_eq _ _) (@a_ren Γ1 Γ2 Γ3).
  intros r1 r2 H1 a1 a2 H2 ? i; unfold a_ren; cbn.
  apply (v_ren_eq _ _ H1), H2.
Qed.

#[global] Instance a_shift_eq {Γ Δ y} : Proper (ass_eq _ _ ==> ass_eq _ _) (@a_shift Γ Δ y).
  intros ? ? H ? h.
  dependent elimination h; cbn; auto.
  now rewrite H.
Qed.

#[global] Instance a_shift2_eq {Γ Δ x y} : Proper (ass_eq _ _ ==> ass_eq _ _) (@a_shift2 Γ Δ x y).
  intros ? ? H ? h.
  do 2 (dependent elimination h; cbn; auto).
  now rewrite H.
Qed.

Definition t_ren_ren_P Γ1 a (t : term Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2),
    t_rename f1 a (t_rename f2 a t) = t_rename (s_ren f1 f2) a t.
Definition v_ren_ren_P Γ1 a (v : val Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2),
    v_rename f1 a (v_rename f2 a v) = v_rename (s_ren f1 f2) a v.

Lemma ren_ren_prf : syn_ind_args t_ren_ren_P v_ren_ren_P.
  econstructor.
  all: unfold t_ren_ren_P, v_ren_ren_P.
  all: intros; cbn; f_equal; auto.
  all: unfold r_shift2; now repeat rewrite r_shift_comp.
Qed.

Lemma t_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) a (t : term Γ1 a)
  : t_rename f1 a (t_rename f2 a t) = t_rename (s_ren f1 f2) a t.
  now apply (term_ind_mut _ _ ren_ren_prf).
Qed.
Lemma v_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) a (v : val Γ1 a)
  : v_rename f1 a (v_rename f2 a v) = v_rename (s_ren f1 f2) a v.
  now apply (val_ind_mut _ _ ren_ren_prf).
Qed.
Lemma s_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) (s : state Γ1)
  : s_rename f1 (s_rename f2 s) = s_rename (s_ren f1 f2) s.
  destruct s; cbn; f_equal.
  now apply t_ren_ren.
  now apply v_ren_ren.
Qed.

Definition t_ren_id_l_P Γ a (t : term Γ a) : Prop := t_rename r_id a t = t.
Definition v_ren_id_l_P Γ a (v : val Γ a)  : Prop := v_rename r_id a v = v.

Lemma ren_id_l_prf : syn_ind_args t_ren_id_l_P v_ren_id_l_P.
  econstructor.
  all: unfold t_ren_id_l_P, v_ren_id_l_P.
  all: intros; cbn; f_equal; auto.
  unfold r_shift2; now repeat rewrite r_shift_id.
Qed.

Lemma t_ren_id_l {Γ} a (t : term Γ a) : t_rename r_id a t = t.
  now apply (term_ind_mut _ _ ren_id_l_prf).
Qed.
Lemma v_ren_id_l {Γ} a (v : val Γ a) : v_rename r_id a v = v.
  now apply (val_ind_mut _ _ ren_id_l_prf).
Qed.
Lemma s_ren_id_l {Γ} (s : state Γ) : s_rename r_id s = s.
  destruct s; cbn; f_equal.
  now apply t_ren_id_l.
  now apply v_ren_id_l.
Qed.

Lemma v_ren_id_r {Γ Δ} (f : Γ ⊆ Δ) a (i : Γ ∋ a) : v_rename f a (Var i) = Var (f _ i).
  reflexivity.
Qed.

Lemma a_shift_id {Γ a} : @a_shift Γ Γ a a_id ≡ₐ a_id.
  intros x i; destruct x; dependent elimination i; auto.
Qed.

Lemma a_shift2_id {Γ x y} : @a_shift2 Γ Γ x y a_id ≡ₐ a_id.
  unfold a_shift2, v_shift2; intros ? h.
  do 2 (dependent elimination h; cbn; auto).
Qed.

Lemma a_shift_a_ren {Γ1 Γ2 Γ3 y} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[ val ]> Γ2)
      : a_shift (y:=y) (a_ren f1 f2) ≡ₐ a_ren (r_shift f1) (a_shift f2) .
  unfold r_shift, a_shift, a_ren, v_shift; intros ? h.
  dependent elimination h; cbn; auto.
  now rewrite 2 v_ren_ren.
Qed.

Lemma a_shift_s_ren {Γ1 Γ2 Γ3 y} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 ⊆ Γ2)
  : a_shift (y:=y) (s_ren f1 f2) ≡ₐ s_ren (a_shift f1) (r_shift f2) .
  intros ? i; dependent elimination i; auto.
Qed.

Lemma a_shift2_s_ren {Γ1 Γ2 Γ3 x y} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 ⊆ Γ2)
  : a_shift2 (x:=x) (y:=y) (s_ren f1 f2) ≡ₐ s_ren (a_shift2 f1) (r_shift2 f2) .
  intros ? h; do 2 (dependent elimination h; auto).
Qed.

Lemma a_shift2_a_ren {Γ1 Γ2 Γ3 x y} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[ val ]> Γ2)
      : a_shift2 (x:=x) (y:=y) (a_ren f1 f2) ≡ₐ a_ren (r_shift2 f1) (a_shift2 f2) .
  unfold r_shift2, r_shift, a_shift2, v_shift2, a_ren; intros ? h.
  do 2 (dependent elimination h; cbn; auto).
  now rewrite 2 v_ren_ren.
Qed.

Definition t_sub_proper_P Γ a (t : term Γ a) : Prop :=
  forall Δ (f1 f2 : Γ =[val]> Δ), f1 ≡ₐ f2 -> t_subst f1 a t = t_subst f2 a t .
Definition v_sub_proper_P Γ a (v : val Γ a) : Prop :=
  forall Δ (f1 f2 : Γ =[val]> Δ), f1 ≡ₐ f2 -> v_subst f1 a v = v_subst f2 a v .

Lemma sub_proper_prf : syn_ind_args t_sub_proper_P v_sub_proper_P.
  econstructor.
  all: unfold t_sub_proper_P, v_sub_proper_P.
  all: intros; cbn; f_equal; auto.
  now apply H, a_shift2_eq.
Qed.

#[global] Instance t_sub_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> dpointwise_relation (fun a => eq ==> eq)) (@t_subst Γ Δ).
  intros f1 f2 H1 a x y ->; now apply (term_ind_mut _ _ sub_proper_prf).
Qed.

#[global] Instance v_sub_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> dpointwise_relation (fun a => eq ==> eq)) (@v_subst Γ Δ).
  intros f1 f2 H1 a x y ->; now apply (val_ind_mut _ _ sub_proper_prf).
Qed.

#[global] Instance s_sub_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> eq ==> eq) (@s_subst Γ Δ).
  intros f1 f2 H1 x y ->; destruct y; cbn; f_equal.
  now apply t_sub_eq.
  now apply v_sub_eq.
Qed.

#[global] Instance a_comp_eq {Γ1 Γ2 Γ3} : Proper (ass_eq _ _ ==> ass_eq _ _ ==> ass_eq _ _) (@a_comp Γ1 Γ2 Γ3).
  intros ? ? H1 ? ? H2 ? ?; apply v_sub_eq; [ apply H1 | apply H2 ].
Qed.

Definition t_ren_sub_P Γ1 a (t : term Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val]> Γ2),
    t_rename f1 a (t_subst f2 a t)
    = t_subst (a_ren f1 f2) a t .
Definition v_ren_sub_P Γ1 a (v : val Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val]> Γ2),
    v_rename f1 a (v_subst f2 a v)
    = v_subst (a_ren f1 f2) a v .
Lemma ren_sub_prf : syn_ind_args t_ren_sub_P v_ren_sub_P.
  econstructor.
  all: unfold t_ren_sub_P, v_ren_sub_P.
  all: intros; cbn; f_equal; auto.
  etransitivity; [ now apply H | ].  
  eapply t_sub_eq; auto.
  symmetry; apply a_shift2_a_ren.
Qed.
Lemma t_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val]> Γ2) a (t : term Γ1 a)
  : t_rename f1 a (t_subst f2 a t) = t_subst (a_ren f1 f2) a t.
  now apply (term_ind_mut _ _ ren_sub_prf).
Qed.
Lemma v_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val]> Γ2) a (v : val Γ1 a)
  : v_rename f1 a (v_subst f2 a v) = v_subst (a_ren f1 f2) a v.
  now apply (val_ind_mut _ _ ren_sub_prf).
Qed.
Lemma s_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val]> Γ2) (s : state Γ1)
  : s_rename f1 (s_subst f2 s) = s_subst (a_ren f1 f2) s.
  destruct s; cbn; f_equal.
  now apply t_ren_sub.
  now apply v_ren_sub.
Qed.

Definition t_sub_ren_P Γ1 a (t : term Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 ⊆ Γ2),
    t_subst f1 a (t_rename f2 a t)
    = t_subst (s_ren f1 f2) a t .
Definition v_sub_ren_P Γ1 a (v : val Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 ⊆ Γ2),
    v_subst f1 a (v_rename f2 a v)
    = v_subst (s_ren f1 f2) a v .
Lemma sub_ren_prf : syn_ind_args t_sub_ren_P v_sub_ren_P.
  econstructor.
  all: unfold t_sub_ren_P, v_sub_ren_P.
  all: intros; cbn; f_equal; auto.
  etransitivity; [ now apply H | ].  
  eapply t_sub_eq; auto.
  symmetry; apply a_shift2_s_ren.
Qed.

Lemma t_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 ⊆ Γ2) a (t : term Γ1 a)
  : t_subst f1 a (t_rename f2 a t) = t_subst (s_ren f1 f2) a t.
  now apply (term_ind_mut _ _ sub_ren_prf).
Qed.
Lemma v_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 ⊆ Γ2) a (v : val Γ1 a)
  : v_subst f1 a (v_rename f2 a v) = v_subst (s_ren f1 f2) a v.
  now apply (val_ind_mut _ _ sub_ren_prf).
Qed.
Lemma s_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 ⊆ Γ2) (s : state Γ1)
  : s_subst f1 (s_rename f2 s) = s_subst (s_ren f1 f2) s.
  destruct s; cbn; f_equal.
  now apply t_sub_ren.
  now apply v_sub_ren.
Qed.

Lemma v_sub_id_r {Γ Δ} (f : Γ =[val]> Δ) a (i : Γ ∋ a) : v_subst f a (Var i) = f _ i.
  reflexivity.
Qed.
Lemma a_comp_id_r {Γ1 Γ2} (a : Γ1 =[val]> Γ2) : a_comp a a_id ≡ₐ a .
  intros ? i; auto.
Qed.

Lemma a_shift_comp {Γ1 Γ2 Γ3 y} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2)
  : a_shift (y:=y) (a_comp f1 f2) ≡ₐ a_comp (a_shift f1) (a_shift f2) .
  intros x i; dependent elimination i; unfold a_shift, a_comp, v_shift; cbn; auto.
  now rewrite v_ren_sub, v_sub_ren.
Qed.

Lemma a_shift2_comp {Γ1 Γ2 Γ3 x y} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2)
  : a_shift2 (x:=x) (y:=y) (a_comp f1 f2) ≡ₐ a_comp (a_shift2 f1) (a_shift2 f2) .
  unfold a_shift2, v_shift2, a_comp; intros ? h.
  do 2 (dependent elimination h; cbn; auto).
  now rewrite v_ren_sub, v_sub_ren.
Qed.

Definition t_sub_sub_P Γ1 a (t : term Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2),
    t_subst f1 a (t_subst f2 a t) = t_subst (a_comp f1 f2) a t.
Definition v_sub_sub_P Γ1 a (v : val Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2),
    v_subst f1 a (v_subst f2 a v) = v_subst (a_comp f1 f2) a v.

Lemma sub_sub_prf : syn_ind_args t_sub_sub_P v_sub_sub_P.
  econstructor.
  all: unfold t_sub_sub_P, v_sub_sub_P.
  all: intros; cbn; f_equal; auto.
  etransitivity; [ now apply H | ].
  apply t_sub_eq; auto.
  symmetry; apply a_shift2_comp.
Qed.
Lemma t_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2) a (t : term Γ1 a)
  : t_subst f1 a (t_subst f2 a t) = t_subst (a_comp f1 f2) a t.
  now apply (term_ind_mut _ _ sub_sub_prf).
Qed.
Lemma v_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2) a (v : val Γ1 a)
  : v_subst f1 a (v_subst f2 a v) = v_subst (a_comp f1 f2) a v.
  now apply (val_ind_mut _ _ sub_sub_prf).
Qed.
Lemma s_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2) (s : state Γ1)
  : s_subst f1 (s_subst f2 s) = s_subst (a_comp f1 f2) s.
  destruct s; cbn; f_equal.
  now apply t_sub_sub.
  now apply v_sub_sub.
Qed.

Lemma a_comp_assoc {Γ1 Γ2 Γ3 Γ4} (u : Γ3 =[val]> Γ4) (v : Γ2 =[val]> Γ3) (w : Γ1 =[val]> Γ2)
           : a_comp u (a_comp v w) ≡ₐ a_comp (a_comp u v) w .
  intros ? i; unfold a_comp; now apply v_sub_sub.
Qed.

Definition t_sub_id_l_P Γ a (t : term Γ a) : Prop := t_subst a_id a t = t.
Definition v_sub_id_l_P Γ a (v : val Γ a) : Prop := v_subst a_id a v = v.

Lemma sub_id_l_prf : syn_ind_args t_sub_id_l_P v_sub_id_l_P.
  econstructor.
  all: unfold t_sub_id_l_P, v_sub_id_l_P.
  all: intros; cbn; f_equal; auto.
  etransitivity; [ | now apply H ].
  apply t_sub_eq; auto.
  now apply a_shift2_id.
Qed.

Lemma t_sub_id_l {Γ} a (t : term Γ a) : t_subst a_id a t = t.
  now apply (term_ind_mut _ _ sub_id_l_prf).
Qed.
Lemma v_sub_id_l {Γ} a (v : val Γ a) : v_subst a_id a v = v.
  now apply (val_ind_mut _ _ sub_id_l_prf).
Qed.
Lemma s_sub_id_l {Γ} (s : state Γ) : s_subst a_id s = s.
  destruct s; cbn; f_equal.
  now apply t_sub_id_l.
  now apply v_sub_id_l.
Qed.
Lemma a_comp_id_l {Γ1 Γ2} (a : Γ1 =[val]> Γ2) : a_comp a_id a ≡ₐ a .
  intros ? i; now apply v_sub_id_l.
Qed.


Lemma sub1_sub {Γ Δ a} (f : Γ =[val]> Δ) (v : val Γ a) :
  a_comp (ass1 (v_subst f a v)) (a_shift f) ≡ₐ a_comp f (ass1 v).
  intros ? i; dependent elimination i; cbn; auto.
  unfold v_shift; rewrite v_sub_ren.
  now apply v_sub_id_l.
Qed.

Lemma sub1_ren {Γ Δ a} (f : Γ ⊆ Δ) (v : val Γ a) :
  ass1 (v_rename f a v) ⊛ᵣ r_shift f ≡ₐ a_ren f (ass1 v) .
  intros ? i; dependent elimination i; auto.
Qed.

Lemma v_sub1_sub {Γ Δ a b} (f : Γ =[val]> Δ) (v : val Γ a) (w : val (Γ ▶ a) b)
  : v_subst (a_shift f) b w /ᵥ v_subst f a v = v_subst f b (w /ᵥ v) .
  unfold v_subst1; rewrite 2 v_sub_sub.
  apply v_sub_eq; auto.
  rewrite sub1_sub; reflexivity.
Qed.

Lemma v_sub1_ren {Γ Δ a b} (f : Γ ⊆ Δ) (v : val Γ a) (w : val (Γ ▶ a) b)
  : v_rename (r_shift f) b w /ᵥ v_rename f a v = v_rename f b (w /ᵥ v) .
  unfold v_subst1. rewrite v_sub_ren, v_ren_sub.
  apply v_sub_eq; auto.
  now rewrite sub1_ren.
Qed.

Lemma t_sub1_sub {Γ Δ a b} (f : Γ =[val]> Δ) (v : val Γ a) (t : term (Γ ▶ a) b)
  : t_subst (a_shift f) b t /ₜ v_subst f a v = t_subst f b (t /ₜ v) .
  unfold t_subst1; rewrite 2 t_sub_sub.
  apply t_sub_eq; auto.
  rewrite sub1_sub; reflexivity.
Qed.

Lemma t_sub1_ren {Γ Δ a b} (f : Γ ⊆ Δ) (v : val Γ a) (t : term (Γ ▶ a) b)
  : t_rename (r_shift f) b t /ₜ v_rename f a v = t_rename f b (t /ₜ v) .
  unfold t_subst1; rewrite t_sub_ren, t_ren_sub.
  apply t_sub_eq; auto.
  now rewrite sub1_ren.
Qed.

Lemma t_sub2_sub {Γ Δ x y z} (f : Γ =[val]> Δ) (t : term (Γ ▶ x ▶ y) z) u v
  : t_subst (a_shift2 f) _ t /ₜ[ v_subst f _ u , v_subst f _ v ] = t_subst f _ (t /ₜ[ u , v ]) .
  unfold t_subst2. rewrite 2 t_sub_sub.
  apply t_sub_eq; auto.
  intros ? h; do 2 (dependent elimination h; cbn; auto).
  unfold v_shift2; rewrite v_sub_ren.
  now apply v_sub_id_l.
Qed.

#[global] Instance p_app_eq {Γ x} (v : val Γ x) (m : pat (t_neg x)) : Proper (ass_eq _ _ ==> eq) (p_app v m) .
  intros u1 u2 H; destruct x; dependent elimination m; cbn in *; do 2 f_equal; apply H.
Qed.

From OGS.OGS Require Spec.

Definition stlc_spec : Spec.interaction_spec :=
  {| Spec.typ := ty ;
     Spec.msg := fun t => pat (t_neg t) ;
     Spec.dom := fun t p => pat_dom p |}
.

Program Definition stlc_val : @Spec.lang_monoid stlc_spec :=
  {| Spec.val := val ;
     Spec.v_var := @a_id ;
     Spec.v_sub := @v_subst
  |}.

Program Definition stlc_conf : @Spec.lang_module stlc_spec stlc_val :=
  {| Spec.conf := state ;
     Spec.c_sub := @s_subst ;
  |}.

Program Definition stlc_val_laws : @Spec.lang_monoid_laws stlc_spec stlc_val :=
  {| Spec.v_sub_proper := @v_sub_eq ;
     Spec.v_sub_var := @a_comp_id_r ;
     Spec.v_var_sub := @a_comp_id_l ;
     Spec.v_sub_sub := @a_comp_assoc ;
  |} .

Program Definition stlc_conf_laws : @Spec.lang_module_laws stlc_spec stlc_val stlc_conf :=
  {| Spec.c_sub_proper := @s_sub_eq ;
     Spec.c_var_sub := @s_sub_id_l ;
     Spec.c_sub_sub := @s_sub_sub ;
  |} .

Definition stlc_var_laws : @Spec.var_assumptions stlc_spec stlc_val .
  econstructor; intros.
  - unfold a_id in H; now dependent induction H.
  - induction v; try (apply inr; intros [ i H ]; now inversion H).
    apply inl; econstructor; auto.
  - destruct X as [ i H ].
    induction v; try now inversion H.
    refine (h ,' eq_refl).
Defined.

Program Definition stlc_machine : @Spec.machine stlc_spec stlc_val stlc_conf :=
  {| Spec.eval := @eval ;
     Spec.app := @p_app ; |}.

From Coinduction Require Import coinduction lattice rel tactics.
From OGS.ITree Require Import ITree Eq Structure.
From OGS.OGS Require Import Spec.

Lemma stlc_machine_law : @Spec.machine_laws stlc_spec stlc_val stlc_conf stlc_machine .
  econstructor; intros; unfold stlc_spec, stlc_val in *; cbn.
  - intros ? ? H1; now apply p_app_eq.
  - destruct x; dependent elimination m; cbn; f_equal.
  - revert c e; unfold comp_eq, it_eq; coinduction R CIH; intros c e.
    destruct c. cbn in v.
    dependent elimination t.
    * dependent elimination v.
      + simpl c_sub.
        unfold stlc_new.eval at 2.
        cbn - [ stlc_new.eval ].
        change (it_eqF ∅ₑ ?a ?b T1_0 (observe ?x) (_observe ?y)) with (it_eq_bt ∅ₑ a R T1_0 x y).
        refine (gfp_bt (it_eq_map ∅ₑ _) R T1_0 _ _ _); reflexivity.
      + cbn; econstructor.
        exact (CIH (Cut t1 (KArg v0 v)) e).
      + dependent elimination v0.
        ++ simpl s_subst.
           unfold stlc_new.eval at 2.
           cbn - [ stlc_new.eval ].
           change (it_eqF ∅ₑ ?a ?b T1_0 (observe ?x) (_observe ?y)) with (it_eq_bt ∅ₑ a R T1_0 x y).
           refine (gfp_bt (it_eq_map ∅ₑ _) R T1_0 _ _ _); reflexivity.
        ++ cbn; econstructor.
           change (LamRec _) with (v_subst e _ (LamRec t0)) at 1.
           rewrite t_sub2_sub.
           exact (CIH (Cut (t0 /ₜ[ LamRec t0 , v1 ]) v2) e).
    * cbn; econstructor.
      exact (CIH (Cut t1 (KFun t0 v)) e).
  - destruct u as [ a [ i [ p γ ] ]].
    unfold nf_ty', nf_var', nf_val', a_id; cbn in *.
    destruct a; dependent elimination p; cbn in *.
    all: unfold comp_eq; apply it_eq_unstep; cbn; econstructor.
    all: do 3 (unshelve econstructor; auto; cbn).
    all: intros ? h; do 3 (dependent elimination h; auto).
  - intros [ x p ].
    destruct x; dependent elimination p; econstructor.
    * intros [ z p ] H.
      destruct z; dependent elimination p; dependent elimination H.
      + dependent elimination v; try now destruct (p (_ ,' eq_refl)).
        apply it_eq_step in i0; now inversion i0.
      + dependent elimination v; try now destruct (p (_ ,' eq_refl)).
        apply it_eq_step in i0; now inversion i0.
    * intros [ z p ] H.
      destruct z; dependent elimination p; dependent elimination H.
      + cbn in *.
        pose (vv :=e (t+ a) Ctx.top); change (e (t+ a) Ctx.top) with vv in i0; remember vv; clear vv Heqv0 e.
        dependent elimination v; try now destruct (p (_ ,' eq_refl)).
        apply it_eq_step in i0; now inversion i0.
        dependent elimination v0; apply it_eq_step in i0; cbn in i0; dependent elimination i0.
        unfold msg_of_nf' in r_rel; cbn in r_rel.
        inversion_sigma r_rel; dependent elimination r_rel1; clear .
        econstructor; intros [ z p ] H.
        destruct z; dependent elimination p; dependent elimination H.
        ++ dependent elimination v; try now destruct (p (_ ,' eq_refl)).
           apply it_eq_step in i0; now inversion i0.
        ++ dependent elimination v; try now destruct (p (_ ,' eq_refl)).
           apply it_eq_step in i0; now inversion i0.
      + cbn in *.
        pose (vv :=e (t+ a) Ctx.top); change (e (t+ a) Ctx.top) with vv in i0; remember vv; clear vv Heqv0 e.
        dependent elimination v; try now destruct (p (_ ,' eq_refl)).
        apply it_eq_step in i0; now inversion i0.
        dependent elimination v0; apply it_eq_step in i0; cbn in i0; dependent elimination i0.
        unfold msg_of_nf' in r_rel; cbn in r_rel.
        inversion_sigma r_rel; inversion r_rel1.
Qed.

Check (@Spec.inj_init_act stlc_spec stlc_val stlc_conf).

Definition interp_act_s Δ {Γ} (c : state Γ) : @ogs_act stlc_spec Δ (∅ ▶ Γ) :=
  @Spec.m_strat stlc_spec stlc_val stlc_conf stlc_machine Δ (∅ ▶ Γ)
    (@Spec.inj_init_act stlc_spec stlc_val stlc_conf Δ Γ c) .
Notation "⟦ t ⟧ₛ" := (interp_act_s _ t) .

Definition ogs_weq_act Δ {Γ} : relation (@ogs_act stlc_spec Δ (∅ ▶ Γ)) := fun u v => u ≈ v .
Notation "u ≈[ogs Δ ]≈ v" := (ogs_weq_act Δ u v) (at level 40).

Definition stlc_eval_to_msg {Γ : t_ctx} : state Γ -> delay (@msg' stlc_spec Γ) :=
  @eval_to_msg stlc_spec stlc_val stlc_conf stlc_machine Γ .

Definition subst_eq Δ {Γ} : relation (state Γ) :=
  fun u v => forall (σ : Γ =[stlc_new.val]> Δ), stlc_eval_to_msg (s_subst σ u) ≈ stlc_eval_to_msg (s_subst σ v) .
Notation "x ≈[sub Δ ]≈ y" := (subst_eq Δ x y) (at level 10).

Theorem stlc_subst_correct Δ {Γ} (x y : state Γ)
  : ⟦ x ⟧ₛ ≈[ogs Δ ]≈ ⟦ y ⟧ₛ -> x ≈[sub Δ ]≈ y .
  exact (@ogs_correction stlc_spec stlc_val stlc_val_laws stlc_conf stlc_conf_laws stlc_var_laws
           stlc_machine stlc_machine_law Γ Δ x y).
Qed.

Definition c_of_t_p {Γ x} (t : term Γ (t+ x)) : state (Γ ▶ t- x) :=
  Cut (t_shift _ t) (Var Ctx.top) .
Notation "⟦ t ⟧ₚ" := (⟦ c_of_t_p t ⟧ₛ) .

Definition a_of_sk_p {Γ Δ x} (s : Γ =[stlc_new.val]> Δ) (k : stlc_new.val Δ (t- x))
  : (Γ ▶ t- x) =[stlc_new.val]> Δ :=
  s_append s k .

Definition ciu_p_eq Δ {Γ x} : relation (term Γ (t+ x)) :=
  fun u v => forall (σ : Γ =[stlc_new.val]> Δ) (k : stlc_new.val Δ (t- x)),
      stlc_eval_to_msg (Cut (t_subst σ _ u) k) ≈ stlc_eval_to_msg (Cut (t_subst σ _ v) k) .
Notation "x ≈[ciu Δ ]≈ y" := (ciu_p_eq Δ x y) (at level 10).

Lemma sub_csk_p {Γ Δ x} (t : term Γ (t+ x)) (s : Γ =[stlc_new.val]> Δ) (k : stlc_new.val Δ (t- x))
              : Cut (t_subst s _ t) k = s_subst (a_of_sk_p s k) (c_of_t_p t) .
  cbn; f_equal; unfold t_shift; now rewrite t_sub_ren.
Qed.

Theorem mu_ciu_p_correct Δ {Γ t} (x y : term Γ (t+ t)) : ⟦ x ⟧ₚ ≈[ogs Δ ]≈ ⟦ y ⟧ₚ -> x ≈[ciu Δ ]≈ y .
  intros H σ k.
  rewrite 2 sub_csk_p.
  now apply stlc_subst_correct.
Qed.
