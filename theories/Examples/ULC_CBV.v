(*|
Un(i)typed Call-by-value Lambda Calculus
========================================

This file follows very closely its sibling `CBVTyped.v`. It is recommended to read that
one first: the comments on this one will be quite more terse and focus on the differences.

.. coq:: none
|*)
From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.
From OGS.Ctx Require Import All Ctx Covering.
From OGS.ITree Require Import ITree Delay.
From OGS.OGS Require Import Soundness.
Set Warnings "-notation-overridden".
Set Warnings "-parsing".
(*|
Syntax
------

As our framework is "well-typed well-scoped", when we mean untyped, we really mean
unityped, i.e., we will take the single element set as set of types. Although, the
typing rules will not be as uninteresting as it would seem. Indeed, as we adopt a
single-sided sequent-calculus style of presentation, we do give types to continuations
(formally negated types), and we thus have not one type, but two: the type of terms
`⊕` and the type of continuations `⊖`.

Typing contexts, terms, values, evaluation contexts and configurations work
straightforwardly.
|*)
Variant ty : Type :=
| Left : ty
| Right : ty
.
(*| .. coq:: none |*)
Declare Scope ty_scope .
Derive NoConfusion for ty .
Bind Scope ty_scope with ty .
Open Scope ty_scope .
(*||*)
Notation "⊕" := (Left) (at level 20) : ty_scope .
Notation "⊖" := (Right) (at level 20) : ty_scope .

Definition t_ctx : Type := Ctx.ctx ty .
Bind Scope ctx_scope with t_ctx .
(*|
Note that is is the proper pure untyped lambda calculus: in constrast with our STLC example,
the lambda is not recursive and there is no unit value nor base type, only functions.
|*)
Inductive term (Γ : t_ctx) : Type :=
| Val : val Γ -> term Γ
| App : term Γ -> term Γ -> term Γ
with val (Γ : t_ctx) : Type :=
| Var : Γ ∋ ⊕ -> val Γ
| Lam : term (Γ ▶ₓ ⊕) -> val Γ
.
(*| .. coq:: none |*)
Arguments Val {Γ} & v .
Arguments App {Γ} & t1 t2 .
Arguments Var {Γ} & i .
Arguments Lam {Γ} & t .
(*||*)
Inductive ev_ctx (Γ : t_ctx) : Type :=
| K0 : Γ ∋ ⊖ -> ev_ctx Γ
| K1 : term Γ -> ev_ctx Γ -> ev_ctx Γ
| K2 : val Γ -> ev_ctx Γ -> ev_ctx Γ
.
(*| .. coq:: none |*)
Arguments K0 {Γ} & i .
Arguments K1 {Γ} & t π .
Arguments K2 {Γ} & v π .
(*||*)
Variant state (Γ : t_ctx) : Type :=
| Cut : term Γ -> ev_ctx Γ -> state Γ
.
(*| .. coq:: none |*)
Arguments Cut {Γ} t π.
(*|
We introduce the sorted family of generalized values, together with the generalized
variable.
|*)
Equations val_m : t_ctx -> ty -> Type :=
  val_m Γ (⊕) := val Γ ;
  val_m Γ (⊖) := ev_ctx Γ .

Equations a_id {Γ} : Γ =[val_m]> Γ :=
  a_id (⊕) i := Var i ;
  a_id (⊖) i := K0 i .
(*|
Substitution and Renaming
-------------------------
|*)
Equations t_rename {Γ Δ} : Γ ⊆ Δ -> term Γ -> term Δ :=
  t_rename f (Val v)     := Val (v_rename f v) ;
  t_rename f (App t1 t2) := App (t_rename f t1) (t_rename f t2) ;
with v_rename {Γ Δ} : Γ ⊆ Δ -> val Γ -> val Δ :=
  v_rename f (Var i) := Var (f _ i) ;
  v_rename f (Lam t) := Lam (t_rename (r_shift1 f) t) .

Equations e_rename {Γ Δ} : Γ ⊆ Δ -> ev_ctx Γ -> ev_ctx Δ :=
  e_rename f (K0 i)   := K0 (f _ i) ;
  e_rename f (K1 t π) := K1 (t_rename f t) (e_rename f π) ;
  e_rename f (K2 v π) := K2 (v_rename f v) (e_rename f π) .

Equations s_rename {Γ Δ} : Γ ⊆ Δ -> state Γ -> state Δ :=
  s_rename f (Cut t π) := Cut (t_rename f t) (e_rename f π).

Equations m_rename {Γ Δ} : Γ ⊆ Δ -> val_m Γ ⇒ᵢ val_m Δ :=
  m_rename f (⊕) v := v_rename f v ;
  m_rename f (⊖) π := e_rename f π .
(*|
Renaming an assigment on the left.
|*)
Definition a_ren {Γ1 Γ2 Γ3} : Γ1 =[val_m]> Γ2 -> Γ2 ⊆ Γ3 -> Γ1 =[val_m]> Γ3 :=
  fun f g _ i => m_rename g _ (f _ i) .
Arguments a_ren _ _ _ /.
(*|
The following bunch of notations will help us to keep the code readable:
|*)
Notation "t ₜ⊛ᵣ r" := (t_rename r%asgn t) (at level 14).
Notation "v ᵥ⊛ᵣ r" := (v_rename r%asgn v) (at level 14).
Notation "π ₑ⊛ᵣ r" := (e_rename r%asgn π) (at level 14).
Notation "v ₘ⊛ᵣ r" := (m_rename r%asgn _ v) (at level 14).
Notation "s ₛ⊛ᵣ r" := (s_rename r%asgn s) (at level 14).
Notation "a ⊛ᵣ r" := (a_ren a%asgn r%asgn) (at level 14) : asgn_scope.
(*|
The weakenings we will need for substitution..
|*)
Definition t_shift1 {Γ a} := @t_rename Γ (Γ ▶ₓ a) r_pop.
Definition v_shift1 {Γ a} := @v_rename Γ (Γ ▶ₓ a) r_pop.
Definition m_shift1 {Γ a} := @m_rename Γ (Γ ▶ₓ a) r_pop.
Definition a_shift1 {Γ Δ a} (f : Γ =[val_m]> Δ) :=
  [ a_map f m_shift1 ,ₓ a_id a top ]%asgn .
(*|
Substitutions
^^^^^^^^^^^^^
|*)
Equations t_subst {Γ Δ} : Γ =[val_m]> Δ -> term Γ -> term Δ :=
  t_subst f (Val v)     := Val (v_subst f v) ;
  t_subst f (App t1 t2) := App (t_subst f t1) (t_subst f t2) ;
with v_subst {Γ Δ} : Γ =[val_m]> Δ -> val Γ -> val Δ :=
  v_subst f (Var i) := f _ i ;
  v_subst f (Lam t) := Lam (t_subst (a_shift1 f) t) .

Equations e_subst {Γ Δ} : Γ =[val_m]> Δ -> ev_ctx Γ -> ev_ctx Δ :=
  e_subst f (K0 i)   := f _ i ;
  e_subst f (K1 t π) := K1 (t_subst f t) (e_subst f π) ;
  e_subst f (K2 v π) := K2 (v_subst f v) (e_subst f π) .

Notation "t `ₜ⊛ a" := (t_subst a%asgn t) (at level 30).
Notation "v `ᵥ⊛ a" := (v_subst a%asgn v) (at level 30).
Notation "π `ₑ⊛ a" := (e_subst a%asgn π) (at level 30).

Equations m_subst : val_m ⇒₁ ⟦ val_m , val_m ⟧₁ :=
  m_subst _ (⊕) v _ f := v `ᵥ⊛ f ;
  m_subst _ (⊖) π _ f := π `ₑ⊛ f .

Equations s_subst : state ⇒₀ ⟦ val_m , state ⟧₀ :=
  s_subst _ (Cut t π) _ f := Cut (t `ₜ⊛ f) (π `ₑ⊛ f) .
(*|
We can now instanciate the substitution monoid and module structures.
|*)
#[global] Instance val_m_monoid : subst_monoid val_m :=
  {| v_var := @a_id ; v_sub := m_subst |} .
#[global] Instance state_module : subst_module val_m state :=
  {| c_sub := s_subst |} .
(*|
Single-variable substitution.
|*)
Definition assign1 {Γ a} v : (Γ ▶ₓ a) =[val_m]> Γ := a_id ▶ₐ v .
Definition t_subst1 {Γ a} (t : term _) v := t `ₜ⊛ @assign1 Γ a v.
Notation "t /[ v ]" := (t_subst1 t v) (at level 50, left associativity).
(*|
An Evaluator
------------

Patterns and Observations
^^^^^^^^^^^^^^^^^^^^^^^^^

As before we define observations (copatterns), as there are only functions and
continuations there is exactly one pattern at each type. Knowing this, we could
have made this type (`obs`) disappear, but it is kept here for the sake of being
more explicit.
|*)
Variant obs : ty -> Type :=
| ORet : obs (⊖)
| OApp : obs (⊕)
.
(*|
Observation still behave as binders, returning bind a term (what we are returning) and
applying binds a term (the argument) and a continuation.
|*)
Equations obs_dom {a} : obs a -> t_ctx :=
  obs_dom (@ORet) := ∅ ▶ₓ ⊕ ;
  obs_dom (@OApp) := ∅ ▶ₓ ⊕ ▶ₓ ⊖ .

Definition obs_op : Oper ty t_ctx :=
  {| o_op := obs ; o_dom := @obs_dom |} .
Notation ORet' := (ORet : o_op obs_op _).
Notation OApp' := (OApp : o_op obs_op _).
(*|
We now define applying an observation with arguments to a value.
|*)
Equations obs_app {Γ a} (v : val_m Γ a) (p : obs a) (γ : obs_dom p =[val_m]> Γ) : state Γ :=
  obs_app v (OApp) γ := Cut (Val v) (K2 (γ _ (pop top)) (γ _ top)) ;
  obs_app π (ORet) γ := Cut (Val (γ _ top)) π .
(*|
Normal forms
^^^^^^^^^^^^

Normal forms take the exact same form as for ULC: a head variable and an observation on it,
with arguments.
|*)
Definition nf := c_var ∥ₛ (obs_op # val_m).
(*|
The CBV Machine
^^^^^^^^^^^^^^^

The evaluator as a state machine.

(1) `⟨ t1 t2 | π ⟩ → ⟨ t2 | t1 ⋅1 π ⟩`

(2) `⟨ v | x ⟩` normal

(3) `⟨ v | t ⋅1 π ⟩ →  ⟨ t | v ⋅2 π ⟩`

(4) `⟨ x | v ⋅2 π ⟩` normal

(5) `⟨ λx.t | v ⋅2 π ⟩ → ⟨ t[x↦v] |  π ⟩`

Rules 1,3,5 step to a new configuration, while cases 2,4 are stuck on normal
forms.
|*)
Equations eval_step {Γ : t_ctx} : state Γ -> (state Γ + nf Γ) :=
  eval_step (Cut (App t1 t2)   (π))      := inl (Cut t2 (K1 t1 π)) ;
  eval_step (Cut (Val v)       (K0 i))   := inr (i ⋅ ORet' ⦇ ! ▶ₐ v ⦈) ;
  eval_step (Cut (Val v)       (K1 t π)) := inl (Cut t (K2 v π)) ;
  eval_step (Cut (Val (Var i)) (K2 v π)) := inr (i ⋅ OApp' ⦇ ! ▶ₐ v ▶ₐ π ⦈) ;
  eval_step (Cut (Val (Lam t)) (K2 v π)) := inl (Cut (t /[ v ]) π) .

Definition ulc_eval {Γ : t_ctx} : state Γ -> delay (nf Γ)
  := iter_delay (ret_delay ∘ eval_step).
(*|
Properties
----------

We now tackle the basic syntactic lemmas on renaming and substitution. See you in 400 lines.
|*)
Scheme term_mut := Induction for term Sort Prop
   with val_mut := Induction for val Sort Prop .

Record syn_ind_args (P_t : forall Γ, term Γ -> Prop)
                    (P_v : forall Γ, val Γ -> Prop)
                    (P_e : forall Γ, ev_ctx Γ -> Prop) :=
  {
    ind_val {Γ} v (_ : P_v Γ v) : P_t Γ (Val v) ;
    ind_app {Γ} t1 (_ : P_t Γ t1) t2 (_ : P_t Γ t2) : P_t Γ (App t1 t2) ;
    ind_var {Γ} i : P_v Γ (Var i) ;
    ind_lam {Γ} t (_ : P_t _ t) : P_v Γ (Lam t) ;
    ind_kvar {Γ} i : P_e Γ (K0 i) ;
    ind_kfun {Γ} t (_ : P_t Γ t) π (_ : P_e Γ π) : P_e Γ (K1 t π) ;
    ind_karg {Γ} v (_ : P_v Γ v) π (_ : P_e Γ π) : P_e Γ (K2 v π)
  } .

Lemma term_ind_mut P_t P_v P_e (H : syn_ind_args P_t P_v P_e) Γ t : P_t Γ t .
  destruct H; now apply (term_mut P_t P_v).
Qed.

Lemma val_ind_mut P_t P_v P_e (H : syn_ind_args P_t P_v P_e) Γ v : P_v Γ v .
  destruct H; now apply (val_mut P_t P_v).
Qed.

Lemma ctx_ind_mut P_t P_v P_e (H : syn_ind_args P_t P_v P_e) Γ π : P_e Γ π .
  induction π.
  - apply (ind_kvar _ _ _ H).
  - apply (ind_kfun _ _ _ H); auto; apply (term_ind_mut _ _ _ H).
  - apply (ind_karg _ _ _ H); auto; apply (val_ind_mut _ _ _ H).
Qed.
(*|
Renaming respects pointwise equality of assignments.
|*)
Definition t_ren_proper_P Γ (t : term Γ) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> t ₜ⊛ᵣ f1 = t ₜ⊛ᵣ f2 .
Definition v_ren_proper_P Γ (v : val Γ) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> v ᵥ⊛ᵣ f1 = v ᵥ⊛ᵣ f2 .
Definition e_ren_proper_P Γ (π : ev_ctx Γ) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> π ₑ⊛ᵣ f1 = π ₑ⊛ᵣ f2 .
Lemma ren_proper_prf : syn_ind_args t_ren_proper_P v_ren_proper_P e_ren_proper_P.
  econstructor.
  all: unfold t_ren_proper_P, v_ren_proper_P, e_ren_proper_P.
  all: intros; cbn; f_equal; auto.
  all: apply H.
  now apply r_shift1_eq.
Qed.

#[global] Instance t_ren_eq {Γ Δ}
  : Proper (asgn_eq _ _ ==> eq ==> eq) (@t_rename Γ Δ).
  intros f1 f2 H1 x y ->; now apply (term_ind_mut _ _ _ ren_proper_prf).
Qed.
#[global] Instance v_ren_eq {Γ Δ}
  : Proper (asgn_eq _ _ ==> eq ==> eq) (@v_rename Γ Δ).
  intros f1 f2 H1 x y ->; now apply (val_ind_mut _ _ _ ren_proper_prf).
Qed.
#[global] Instance e_ren_eq {Γ Δ}
  : Proper (asgn_eq _ _ ==> eq ==> eq) (@e_rename Γ Δ).
  intros f1 f2 H1 x y ->; now apply (ctx_ind_mut _ _ _ ren_proper_prf).
Qed.
#[global] Instance m_ren_eq {Γ Δ}
  : Proper (asgn_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@m_rename Γ Δ).
  intros ? ? H1 [] _ ? ->; cbn in *; now rewrite H1.
Qed.
#[global] Instance s_ren_eq {Γ Δ}
  : Proper (asgn_eq _ _ ==> eq ==> eq) (@s_rename Γ Δ).
  intros ? ? H1 _ x ->; destruct x; cbn; now rewrite H1.
Qed.
#[global] Instance a_ren_eq {Γ1 Γ2 Γ3}
  : Proper (asgn_eq _ _ ==> asgn_eq _ _ ==> asgn_eq _ _) (@a_ren Γ1 Γ2 Γ3).
  intros ?? H1 ?? H2 ??; apply (m_ren_eq _ _ H2), H1.
Qed.
#[global] Instance a_shift_eq {Γ Δ x} : Proper (asgn_eq _ _ ==> asgn_eq _ _) (@a_shift1 Γ Δ x).
  intros ? ? H ? h; dependent elimination h; cbn; auto.
  now rewrite H.
Qed.
(*|
Renaming-renaming assocativity.
|*)
Definition t_ren_ren_P Γ1 (t : term Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 ⊆ Γ3),
    (t ₜ⊛ᵣ f1) ₜ⊛ᵣ f2 = t ₜ⊛ᵣ (f1 ᵣ⊛ f2)  .
Definition v_ren_ren_P Γ1 (v : val Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 ⊆ Γ3),
    (v ᵥ⊛ᵣ f1) ᵥ⊛ᵣ f2 = v ᵥ⊛ᵣ (f1 ᵣ⊛ f2)  .
Definition e_ren_ren_P Γ1 (π : ev_ctx Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 ⊆ Γ3),
    (π ₑ⊛ᵣ f1) ₑ⊛ᵣ f2 = π ₑ⊛ᵣ (f1 ᵣ⊛ f2)  .

Lemma ren_ren_prf : syn_ind_args t_ren_ren_P v_ren_ren_P e_ren_ren_P .
  econstructor.
  all: unfold t_ren_ren_P, v_ren_ren_P, e_ren_ren_P.
  all: intros; cbn; f_equal; auto.
  rewrite H; apply t_ren_eq; auto.
  intros ? h; dependent elimination h; auto.
Qed.

Lemma t_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 ⊆ Γ3) (t : term Γ1)
  : (t ₜ⊛ᵣ f1) ₜ⊛ᵣ f2 = t ₜ⊛ᵣ (f1 ᵣ⊛ f2)  .
  now apply (term_ind_mut _ _ _ ren_ren_prf).
Qed.
Lemma v_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 ⊆ Γ3) (v : val Γ1)
  : (v ᵥ⊛ᵣ f1) ᵥ⊛ᵣ f2 = v ᵥ⊛ᵣ (f1 ᵣ⊛ f2)  .
  now apply (val_ind_mut _ _ _ ren_ren_prf).
Qed.
Lemma e_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 ⊆ Γ3) (π : ev_ctx Γ1)
  : (π ₑ⊛ᵣ f1) ₑ⊛ᵣ f2 = π ₑ⊛ᵣ (f1 ᵣ⊛ f2)  .
  now apply (ctx_ind_mut _ _ _ ren_ren_prf).
Qed.
Lemma m_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 ⊆ Γ3) a (v : val_m Γ1 a)
  : (v ₘ⊛ᵣ f1) ₘ⊛ᵣ f2 = v ₘ⊛ᵣ (f1 ᵣ⊛ f2)  .
  destruct a; [ now apply v_ren_ren | now apply e_ren_ren ].
Qed.
Lemma s_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 ⊆ Γ3) (s : state Γ1)
  : (s ₛ⊛ᵣ f1) ₛ⊛ᵣ f2 = s ₛ⊛ᵣ (f1 ᵣ⊛ f2)  .
  destruct s; apply (f_equal2 Cut); [ now apply t_ren_ren | now apply e_ren_ren ].
Qed.
(*|
Left identity law of renaming.
|*)
Definition t_ren_id_l_P Γ (t : term Γ) : Prop := t ₜ⊛ᵣ r_id = t .
Definition v_ren_id_l_P Γ (v : val Γ) : Prop := v ᵥ⊛ᵣ r_id = v .
Definition e_ren_id_l_P Γ (π : ev_ctx Γ) : Prop := π ₑ⊛ᵣ r_id = π .
Lemma ren_id_l_prf : syn_ind_args t_ren_id_l_P v_ren_id_l_P e_ren_id_l_P .
  econstructor.
  all: unfold t_ren_id_l_P, v_ren_id_l_P, e_ren_id_l_P.
  all: intros; cbn; f_equal; auto.
  rewrite <- H at 2; apply t_ren_eq; auto.
  intros ? h; dependent elimination h; auto.
Qed.

Lemma t_ren_id_l {Γ} (t : term Γ) : t ₜ⊛ᵣ r_id = t.
  now apply (term_ind_mut _ _ _ ren_id_l_prf).
Qed.
Lemma v_ren_id_l {Γ} (v : val Γ) : v ᵥ⊛ᵣ r_id = v .
  now apply (val_ind_mut _ _ _ ren_id_l_prf).
Qed.
Lemma e_ren_id_l {Γ} (π : ev_ctx Γ) : π ₑ⊛ᵣ r_id = π.
  now apply (ctx_ind_mut _ _ _ ren_id_l_prf).
Qed.
Lemma m_ren_id_l {Γ a} (v : val_m Γ a) : v ₘ⊛ᵣ r_id = v .
  destruct a; [ now apply v_ren_id_l | now apply e_ren_id_l ].
Qed.
Lemma s_ren_id_l {Γ} (s : state Γ) : s ₛ⊛ᵣ r_id = s .
  destruct s; apply (f_equal2 Cut); [ now apply t_ren_id_l | now apply e_ren_id_l ].
Qed.

Lemma m_ren_id_r {Γ Δ} (f : Γ ⊆ Δ) {a} (i : Γ ∋ a) : a_id _ i ₘ⊛ᵣ f = a_id _ (f _ i) .
  now destruct a.
Qed.

Lemma a_ren_id_r {Γ Δ} (f : Γ ⊆ Δ) : a_id ⊛ᵣ f ≡ₐ f ᵣ⊛ a_id .
  intros ??; now apply m_ren_id_r.
Qed.
Lemma a_shift_id {Γ x} : @a_shift1 Γ Γ x a_id ≡ₐ a_id.
  intros ? v; dependent elimination v; auto.
  exact (m_ren_id_r _ _).
Qed.
(*|
Lemma 5: shifting assigments commutes with left and right renaming.
|*)
Lemma a_shift1_s_ren {Γ1 Γ2 Γ3 a} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val_m]> Γ3)
  : @a_shift1 _ _ a (f1 ᵣ⊛ f2) ≡ₐ r_shift1 f1 ᵣ⊛ a_shift1 f2 .
  intros ? v; dependent elimination v; auto.
Qed.
Lemma a_shift1_a_ren {Γ1 Γ2 Γ3 a} (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 ⊆ Γ3)
      : @a_shift1 _ _ a (f1 ⊛ᵣ f2) ≡ₐ a_shift1 f1 ⊛ᵣ r_shift1 f2 .
  intros ? v.
  dependent elimination v.
  cbn; now rewrite m_ren_id_r.
  cbn; unfold m_shift1, r_shift1; now rewrite 2 m_ren_ren.
Qed.
(*|
Lemma 6: substitution respects pointwise equality of assigments.
|*)
Definition t_sub_proper_P Γ (t : term Γ) : Prop :=
  forall Δ (f1 f2 : Γ =[val_m]> Δ), f1 ≡ₐ f2 -> t `ₜ⊛ f1 = t `ₜ⊛ f2 .
Definition v_sub_proper_P Γ (v : val Γ) : Prop :=
  forall Δ (f1 f2 : Γ =[val_m]> Δ), f1 ≡ₐ f2 -> v `ᵥ⊛ f1 = v `ᵥ⊛ f2 .
Definition e_sub_proper_P Γ (π : ev_ctx Γ) : Prop :=
  forall Δ (f1 f2 : Γ =[val_m]> Δ), f1 ≡ₐ f2 -> π `ₑ⊛ f1 = π `ₑ⊛ f2.
Lemma sub_proper_prf : syn_ind_args t_sub_proper_P v_sub_proper_P e_sub_proper_P.
  econstructor.
  all: unfold t_sub_proper_P, v_sub_proper_P, e_sub_proper_P.
  all: intros; cbn; f_equal; auto.
  now apply H, a_shift_eq.
Qed.

#[global] Instance t_sub_eq {Γ Δ}
  : Proper (asgn_eq _ _ ==> eq ==> eq) (@t_subst Γ Δ).
  intros ? ? H1 _ ? ->; now apply (term_ind_mut _ _ _ sub_proper_prf).
Qed.
#[global] Instance v_sub_eq {Γ Δ}
  : Proper (asgn_eq _ _ ==> eq ==> eq) (@v_subst Γ Δ).
  intros ? ? H1 _ ? ->; now apply (val_ind_mut _ _ _ sub_proper_prf).
Qed.
#[global] Instance e_sub_eq {Γ Δ}
  : Proper (asgn_eq _ _ ==> eq ==> eq) (@e_subst Γ Δ).
  intros ? ? H1 _ ? ->; now apply (ctx_ind_mut _ _ _ sub_proper_prf).
Qed.
#[global] Instance m_sub_eq
  : Proper (∀ₕ Γ, ∀ₕ _, eq ==> ∀ₕ Δ, asgn_eq Γ Δ ==> eq) m_subst.
  intros ? [] ?? -> ??? H1; cbn in *; now rewrite H1.
Qed.
#[global] Instance s_sub_eq
  : Proper (∀ₕ Γ, eq ==> ∀ₕ Δ, asgn_eq Γ Δ ==> eq) s_subst.
  intros ??[] -> ??? H1; cbn; now rewrite H1.
Qed.
(*
#[global] Instance a_comp_eq {Γ1 Γ2 Γ3} : Proper (ass_eq _ _ ==> ass_eq _ _ ==> ass_eq _ _) (@a_comp Γ1 Γ2 Γ3).
  intros ? ? H1 ? ? H2 ? ?; unfold a_comp, s_map; now rewrite H1, H2.
Qed.
*)
(*|
Lemma 7: renaming-substitution "associativity".
|*)
Definition t_ren_sub_P Γ1 (t : term Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 ⊆ Γ3) ,
    (t `ₜ⊛ f1) ₜ⊛ᵣ f2 = t `ₜ⊛ (f1 ⊛ᵣ f2) .
Definition v_ren_sub_P Γ1 (v : val Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 ⊆ Γ3) ,
    (v `ᵥ⊛ f1) ᵥ⊛ᵣ f2 = v `ᵥ⊛ (f1 ⊛ᵣ f2) .
Definition e_ren_sub_P Γ1 (π : ev_ctx Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 ⊆ Γ3) ,
    (π `ₑ⊛ f1) ₑ⊛ᵣ f2 = π `ₑ⊛ (f1 ⊛ᵣ f2) .
Lemma ren_sub_prf : syn_ind_args t_ren_sub_P v_ren_sub_P e_ren_sub_P.
  econstructor.
  all: unfold t_ren_sub_P, v_ren_sub_P, e_ren_sub_P.
  all: intros; cbn; f_equal; auto.
  change (a_shift1 (fun x => _)) with (a_shift1 (a:=⊕) (f1 ⊛ᵣ f2)); now rewrite a_shift1_a_ren.
Qed.

Lemma t_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 ⊆ Γ3) (t : term Γ1)
  : (t `ₜ⊛ f1) ₜ⊛ᵣ f2 = t `ₜ⊛ (f1 ⊛ᵣ f2) .
  now apply (term_ind_mut _ _ _ ren_sub_prf).
Qed.
Lemma v_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 ⊆ Γ3) (v : val Γ1)
  : (v `ᵥ⊛ f1) ᵥ⊛ᵣ f2 = v `ᵥ⊛ (f1 ⊛ᵣ f2) .
  now apply (val_ind_mut _ _ _ ren_sub_prf).
Qed.
Lemma e_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 ⊆ Γ3) (π : ev_ctx Γ1)
  : (π `ₑ⊛ f1) ₑ⊛ᵣ f2 = π `ₑ⊛ (f1 ⊛ᵣ f2) .
  now apply (ctx_ind_mut _ _ _ ren_sub_prf).
Qed.
Lemma m_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 ⊆ Γ3) a (v : val_m Γ1 a)
  : (v ᵥ⊛ f1) ₘ⊛ᵣ f2 = v ᵥ⊛ (f1 ⊛ᵣ f2) .
  destruct a; [ now apply v_ren_sub | now apply e_ren_sub ].
Qed.
Lemma s_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 ⊆ Γ3) (s : state Γ1)
  : (s ₜ⊛ f1) ₛ⊛ᵣ f2 = s ₜ⊛ (f1 ⊛ᵣ f2) .
  destruct s; cbn; now rewrite t_ren_sub, e_ren_sub.
Qed.
(*|
Lemma 8: substitution-renaming "associativity".
|*)
Definition t_sub_ren_P Γ1 (t : term Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val_m]> Γ3) ,
  (t ₜ⊛ᵣ f1) `ₜ⊛ f2 = t `ₜ⊛ (f1 ᵣ⊛ f2) .
Definition v_sub_ren_P Γ1 (v : val Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val_m]> Γ3) ,
  (v ᵥ⊛ᵣ f1) `ᵥ⊛ f2 = v `ᵥ⊛ (f1 ᵣ⊛ f2) .
Definition e_sub_ren_P Γ1 (π : ev_ctx Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val_m]> Γ3) ,
  (π ₑ⊛ᵣ f1) `ₑ⊛ f2 = π `ₑ⊛ (f1 ᵣ⊛ f2) .
Lemma sub_ren_prf : syn_ind_args t_sub_ren_P v_sub_ren_P e_sub_ren_P.
  econstructor.
  all: unfold t_sub_ren_P, v_sub_ren_P, e_sub_ren_P.
  all: intros; cbn; f_equal; auto.
  now rewrite a_shift1_s_ren.
Qed.

Lemma t_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val_m]> Γ3) (t : term Γ1)
  : (t ₜ⊛ᵣ f1) `ₜ⊛ f2 = t `ₜ⊛ (f1 ᵣ⊛ f2) .
  now apply (term_ind_mut _ _ _ sub_ren_prf).
Qed.
Lemma v_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val_m]> Γ3) (v : val Γ1)
  : (v ᵥ⊛ᵣ f1) `ᵥ⊛ f2 = v `ᵥ⊛ (f1 ᵣ⊛ f2) .
  now apply (val_ind_mut _ _ _ sub_ren_prf).
Qed.
Lemma e_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val_m]> Γ3) (π : ev_ctx Γ1)
  : (π ₑ⊛ᵣ f1) `ₑ⊛ f2 = π `ₑ⊛ (f1 ᵣ⊛ f2) .
  now apply (ctx_ind_mut _ _ _ sub_ren_prf).
Qed.
Lemma m_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val_m]> Γ3) a (v : val_m Γ1 a)
  : (v ₘ⊛ᵣ f1) ᵥ⊛ f2 = v ᵥ⊛ (f1 ᵣ⊛ f2) .
  destruct a; [ now apply v_sub_ren | now apply e_sub_ren ].
Qed.
Lemma s_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val_m]> Γ3) (s : state Γ1)
  : (s ₛ⊛ᵣ f1) ₜ⊛ f2 = s ₜ⊛ (f1 ᵣ⊛ f2) .
  destruct s; cbn; now rewrite t_sub_ren, e_sub_ren.
Qed.
(*|
Lemma 9: left identity law of substitution.
|*)
Definition t_sub_id_l_P Γ (t : term Γ) : Prop := t `ₜ⊛ a_id = t .
Definition v_sub_id_l_P Γ (v : val Γ) : Prop := v `ᵥ⊛ a_id = v .
Definition e_sub_id_l_P Γ (π : ev_ctx Γ) : Prop := π `ₑ⊛ a_id = π .
Lemma sub_id_l_prf : syn_ind_args t_sub_id_l_P v_sub_id_l_P e_sub_id_l_P.
  econstructor.
  all: unfold t_sub_id_l_P, v_sub_id_l_P, e_sub_id_l_P.
  all: intros; cbn; f_equal; auto.
  now rewrite a_shift_id.
Qed.

Lemma t_sub_id_l {Γ} (t : term Γ) : t `ₜ⊛ a_id = t .
  now apply (term_ind_mut _ _ _ sub_id_l_prf).
Qed.
Lemma v_sub_id_l {Γ} (v : val Γ) : v `ᵥ⊛ a_id = v .
  now apply (val_ind_mut _ _ _ sub_id_l_prf).
Qed.
Lemma e_sub_id_l {Γ} (π : ev_ctx Γ) : π `ₑ⊛ a_id = π .
  now apply (ctx_ind_mut _ _ _ sub_id_l_prf).
Qed.
Lemma m_sub_id_l {Γ} a (v : val_m Γ a) : v ᵥ⊛ a_id = v .
  destruct a; [ now apply v_sub_id_l | now apply e_sub_id_l ].
Qed.
Lemma s_sub_id_l {Γ} (s : state Γ) : s ₜ⊛ a_id = s .
  destruct s; cbn; now rewrite t_sub_id_l, e_sub_id_l.
Qed.
(*|
Lemma 9: right identity law of substitution. As for renaming, this one is
mostly by definition.
|*)
Lemma m_sub_id_r {Γ1 Γ2} {a} (i : Γ1 ∋ a) (f : Γ1 =[val_m]> Γ2) : a_id a i ᵥ⊛ f = f a i.
  now destruct a.
Qed.
(*|
Lemma 10: shifting assigments respects composition.
|*)
Lemma a_shift1_comp {Γ1 Γ2 Γ3 a} (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 =[val_m]> Γ3) 
  : @a_shift1 _ _ a (f1 ⊛ f2) ≡ₐ a_shift1 f1 ⊛ a_shift1 f2 .
  intros ? v; dependent elimination v; cbn.
  now rewrite m_sub_id_r.
  unfold m_shift1; now rewrite m_ren_sub, m_sub_ren.
Qed.
(*|
Lemma 11: substitution-substitution associativity, ie composition law.
|*)
Definition t_sub_sub_P Γ1 (t : term Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 =[val_m]> Γ3) ,
  t `ₜ⊛ (f1 ⊛ f2) = (t `ₜ⊛ f1) `ₜ⊛ f2 .
Definition v_sub_sub_P Γ1 (v : val Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 =[val_m]> Γ3) ,
  v `ᵥ⊛ (f1 ⊛ f2) = (v `ᵥ⊛ f1) `ᵥ⊛ f2 .
Definition e_sub_sub_P Γ1 (π : ev_ctx Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 =[val_m]> Γ3) ,
  π `ₑ⊛ (f1 ⊛ f2) = (π `ₑ⊛ f1) `ₑ⊛ f2 .
Lemma sub_sub_prf : syn_ind_args t_sub_sub_P v_sub_sub_P e_sub_sub_P.
  econstructor.
  all: unfold t_sub_sub_P, v_sub_sub_P, e_sub_sub_P.
  all: intros; cbn; f_equal; auto.
  now rewrite a_shift1_comp.
Qed.

Lemma t_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 =[val_m]> Γ3) (t : term Γ1)
  : t `ₜ⊛ (f1 ⊛ f2) = (t `ₜ⊛ f1) `ₜ⊛ f2 .
  now apply (term_ind_mut _ _ _ sub_sub_prf).
Qed.
Lemma v_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 =[val_m]> Γ3) (v : val Γ1)
  : v `ᵥ⊛ (f1 ⊛ f2) = (v `ᵥ⊛ f1) `ᵥ⊛ f2 .
  now apply (val_ind_mut _ _ _ sub_sub_prf).
Qed.
Lemma e_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 =[val_m]> Γ3) (π : ev_ctx Γ1)
  : π `ₑ⊛ (f1 ⊛ f2) = (π `ₑ⊛ f1) `ₑ⊛ f2 .
  now apply (ctx_ind_mut _ _ _ sub_sub_prf).
Qed.
Lemma m_sub_sub {Γ1 Γ2 Γ3} a (v : val_m Γ1 a) (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 =[val_m]> Γ3)
  : v ᵥ⊛ (f1 ⊛ f2) = (v ᵥ⊛ f1) ᵥ⊛ f2 .
  destruct a; [ now apply v_sub_sub | now apply e_sub_sub ].
Qed.
Lemma s_sub_sub {Γ1 Γ2 Γ3} (s : state Γ1) (f1 : Γ1 =[val_m]> Γ2) (f2 : Γ2 =[val_m]> Γ3) 
  : s ₜ⊛ (f1 ⊛ f2) = (s ₜ⊛ f1) ₜ⊛ f2 .
  destruct s; cbn; now rewrite t_sub_sub, e_sub_sub.
Qed.
Lemma a_sub1_sub {Γ Δ a} (f : Γ =[val_m]> Δ) (v : val_m Γ a)
  : a_shift1 f ⊛ assign1 (v ᵥ⊛ f) ≡ₐ (assign1 v) ⊛ f .
  intros ? i; dependent elimination i; cbn.
  now rewrite m_sub_id_r.
  unfold m_shift1; rewrite m_sub_ren, m_sub_id_r; now apply m_sub_id_l.
Qed.
Lemma t_sub1_sub {Γ Δ x} (f : Γ =[val_m]> Δ) (t : term (Γ ▶ₓ x)) v
  : (t `ₜ⊛ a_shift1 f) /[ v ᵥ⊛ f ] = (t /[ v ]) `ₜ⊛ f.
  unfold t_subst1; now rewrite <- 2 t_sub_sub, a_sub1_sub.
Qed.
(*|
The Actual Instance
-------------------

We can now instanciate the generic OGS construction.
|*)
#[global] Instance ulc_val_laws : subst_monoid_laws val_m :=
  {| v_sub_proper := @m_sub_eq ;
     v_sub_var := @m_sub_id_r ;
     v_var_sub := @m_sub_id_l ;
     Subst.v_sub_sub := @m_sub_sub |} .

#[global] Instance ulc_conf_laws : subst_module_laws val_m state :=
  {| c_sub_proper := @s_sub_eq ;
     c_var_sub := @s_sub_id_l ;
     c_sub_sub := @s_sub_sub |} .

#[global] Instance ulc_var_laws : var_assumptions val_m.
  econstructor.
  - intros ? [] ?? H; now dependent destruction H.
  - intros ? [] []; try now apply Yes; exact (Vvar _).
    all: apply No; intro H; dependent destruction H.
  - intros ?? [] v r H; induction v; dependent destruction H; exact (Vvar _).
Qed.

#[global] Instance ulc_machine : machine val_m state obs_op :=
  {| eval := @ulc_eval ;
     oapp := @obs_app |} .

From Coinduction Require Import coinduction lattice rel tactics.
From OGS.ITree Require Import Eq.

Ltac refold_eval :=
  change (Structure.iter _ _ ?a) with (ulc_eval a);
  change (Structure.subst (fun pat : T1 => let 'T1_0 := pat in ?f) T1_0 ?u)
    with (bind_delay' u f).

#[global] Instance ulc_machine_law : machine_laws val_m state obs_op.
  econstructor; cbn; intros.
  - intros ?? H1; dependent elimination o; cbn; repeat (f_equal; auto).
  - destruct x; dependent elimination o; cbn; f_equal.
  - revert c a; unfold comp_eq, it_eq; coinduction R CIH; intros c e.
    cbn; funelim (eval_step c); cbn.
    + destruct (e (⊖) i); auto.
      remember (v `ᵥ⊛ e) as v'; clear H v Heqv'.
      dependent elimination v'; cbn; auto.
    + econstructor; refold_eval; apply CIH.
    + remember (e (⊕) i) as vv; clear H i Heqvv.
      dependent elimination vv; cbn; auto.
    + econstructor;
       refold_eval;
       change (?v `ᵥ⊛ ?a) with ((v : val_m _ (⊕)) ᵥ⊛ a).
      rewrite t_sub1_sub.
      apply CIH.
    + econstructor; refold_eval; apply CIH.
  - destruct u as [ a i [ p γ ] ]; cbn.
    dependent elimination p; cbn.
    all: unfold comp_eq; apply it_eq_unstep; cbn; econstructor.
    all: econstructor; intros ? v; do 3 (dependent elimination v; auto).
  - intros [ x p ].
    destruct x; dependent elimination p; econstructor.
    * intros [ z p ] H.
      dependent elimination p; dependent elimination H.
      all: dependent elimination v; try now destruct (t0 (Vvar _)).
      all: apply it_eq_step in i0; now inversion i0.
    * intros [ z p ] H.
      dependent elimination p; dependent elimination H; cbn in *.
      dependent elimination v; try now destruct (t0 (Vvar _)).
      + apply it_eq_step in i0; now inversion i0.
      + remember (a _ Ctx.top) as vv; clear a Heqvv.
        dependent elimination vv;
          apply it_eq_step in i0; cbn in i0; dependent elimination i0.
        inversion r_rel.
      + econstructor; intros [ z p ] H.
        dependent elimination p; dependent elimination H.
        all: dependent elimination v0; try now destruct (t1 (Vvar _)).
        all: apply it_eq_step in i2; now inversion i2.
Qed.
(*|
Concrete soundness theorem
--------------------------
|*)
Definition subst_eq Δ {Γ} : relation (state Γ) :=
  fun u v => forall σ : Γ =[val_m]> Δ, evalₒ (u ₜ⊛ σ) ≈ evalₒ (v ₜ⊛ σ) .
Notation "x ≈⟦sub Δ ⟧≈ y" := (subst_eq Δ x y) (at level 10).

Theorem ulc_subst_correct Δ {Γ} (x y : state Γ)
  : x ≈⟦ogs Δ⟧≈ y -> x ≈⟦sub Δ⟧≈ y .
  exact (ogs_correction Δ x y).
Qed.
(*|
Recovering CIU-equivalence
^^^^^^^^^^^^^^^^^^^^^^^^^^
|*)
Definition ciu_eq Δ {Γ} : relation (term Γ) :=
  fun u v => forall (σ : Γ =[val_m]> Δ) (π : ev_ctx Δ),
      evalₒ (Cut (u `ₜ⊛ σ) π) ≈ evalₒ (Cut (v `ₜ⊛ σ) π) .
Notation "x ≈⟦ciu Δ ⟧≈ y" := (ciu_eq Δ x y) (at level 10).

Definition c_init {Γ} (t : term Γ) : state (Γ ▶ₓ ⊖)
  := Cut (t_shift1 t) (K0 Ctx.top) .

Definition a_of_sk {Γ Δ} (σ : Γ =[val_m]> Δ) (π : ev_ctx Δ)
  : (Γ ▶ₓ ⊖) =[val_m]> Δ := σ ▶ₐ (π : val_m _ (⊖)) .

Lemma sub_init {Γ Δ} (t : term Γ) (σ : Γ =[val_m]> Δ) (π : ev_ctx Δ)
  : Cut (t `ₜ⊛ σ) π = c_init t ₜ⊛ a_of_sk σ π  .
  cbn; unfold t_shift1; now rewrite t_sub_ren.
Qed.
(*|
We can now obtain a correctness theorem with respect to standard
CIU-equivalence by embedding terms into states. Proving that CIU-equivalence
entails our substitution equivalence is left to the reader!
|*)
Theorem stlc_ciu_correct Δ {Γ} (x y : term Γ)
  : c_init x ≈⟦ogs Δ⟧≈ c_init y -> x ≈⟦ciu Δ⟧≈ y .
  intros H σ k; rewrite 2 sub_init.
  now apply ulc_subst_correct.
Qed.

(*|
Example terms
-------------

Following a trick by Conor McBride we provide a cool notation for writing terms
without any DeBruijn indices, instead leveraging Coq's binders. For this we need
a bit of infrastructure, for manipulating terms that only have term variables.
|*)
Equations n_ctx : nat -> t_ctx :=
  n_ctx O     := ∅ ;
  n_ctx (S n) := n_ctx n ▶ₓ ⊕ .

Notation var' n := (n_ctx n ∋ ⊕).
Notation term' n := (term (n_ctx n)).

Equations v_emb (n : nat) : var' (S n) :=
  v_emb O     := Ctx.top ;
  v_emb (S n) := pop (v_emb n) .

Equations v_lift {n} : var' n -> var' (S n) :=
  @v_lift (S _) Ctx.top     := Ctx.top ;
  @v_lift (S _) (pop i) := pop (v_lift i) .
(*|
Here starts the magic.
|*)
Equations mk_var (m : nat) : forall n, var' (m + S n) :=
  mk_var O     := v_emb ;
  mk_var (S m) := v_lift ∘ mk_var m .

Definition mk_lam {m : nat} (f : (forall n, term' (m + S n)) -> term' (S m)) : term' m
  := Val (Lam (f (Val ∘ Var ∘ mk_var m))).
Arguments mk_lam {_} & _ .
(*|
Now a bit of syntactic sugar.
|*)
Declare Custom Entry lambda.
Notation "✨ e ✨" := (e : term' 0) (e custom lambda at level 2).
Notation "x" := (x _) (in custom lambda at level 0, x ident).
Notation "( x )" := x (in custom lambda at level 0, x at level 2).
Notation "x y" := (App x y)
  (in custom lambda at level 1, left associativity).
Notation "'λ' x .. y ⇒ U" :=
  (mk_lam (fun x => .. (mk_lam (fun y => U)) ..))
  (in custom lambda at level 1, x binder, y binder, U at level 2).
(*|
Aren't these beautiful?
|*)
Definition Delta := ✨ (λ x ⇒ x x) ✨ .
Definition Omega := ✨ (λ x ⇒ x x) (λ x ⇒ x x) ✨ .
Definition Upsilon := ✨ λ f ⇒ (λ x ⇒ f (x x)) (λ x ⇒ f (x x)) ✨.
Definition Theta := ✨ (λ x f ⇒ f (x x f)) (λ x f ⇒ f (x x f)) ✨.
(*|
You can check the actual lambda-term they unwrap to
by running eg:

.. coq::

  Eval cbv in Upsilon.
|*)
