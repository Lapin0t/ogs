(*|
Un(i)typed Call-by-value Lambda Calculus
========================================

This file follows very closely its sibling `CBVTyped.v`. It is recommended to read that one first:
the comments on this one will be quite more terse and focus on the differences.

.. coq:: none
|*)
From OGS Require Import Prelude .
From OGS.Utils Require Import Psh Rel Ctx .
From OGS.ITree Require Import ITree Delay .
Declare Scope ty_scope .
From OGS.OGS Require Import Soundness.
Set Warnings "-notation-overridden".
Set Warnings "-parsing".

(*|
Syntax
------

As our framework is "well-typed well-scoped", when we mean untyped, we really mean unityped,
i.e., we will take the single element set as set of types. Although, the typing rules will not
be as uninteresting as it would seem. Indeed, as we adopt a single-sided sequent-calculus
style of presentation, we do give types to continuations (formally negated types), and we thus
have not one type, but two: the type of terms `⊕` and the type of continuations `⊖`.

Typing contexts, terms, values, evaluation contexts and configurations work straightforwardly.
|*)
Variant ty : Type :=
| Tpro : ty
| Tkon : ty
.
Notation "⊕" := (Tpro) (at level 20) : ty_scope .
Notation "⊖" := (Tkon) (at level 20) : ty_scope .

Derive NoConfusion for ty .
Bind Scope ty_scope with ty .
Open Scope ty_scope .

Definition t_ctx : Type := Ctx.ctx ty .
Bind Scope ctx_scope with t_ctx .
(*|
Note that is is the proper pure untyped lambda calculus: in constrast with our ULC example,
the lambda is not recursive and there is no unit value, only functions.
|*)
Inductive term (Γ : t_ctx) : Type :=
| Val : val Γ -> term Γ
| App : term Γ -> term Γ -> term Γ
with val (Γ : t_ctx) : Type :=
| Var : Γ ∋ ⊕ -> val Γ
| Lam : term (Γ ▶ ⊕) -> val Γ
.
Arguments Val {Γ} v .
Arguments App {Γ} t1 t2 .
Arguments Var {Γ} i .
Arguments Lam {Γ} t .

Inductive ev_ctx (Γ : t_ctx) : Type :=
| K0 : Γ ∋ ⊖ -> ev_ctx Γ
| K1 : term Γ -> ev_ctx Γ -> ev_ctx Γ
| K2 : val Γ -> ev_ctx Γ -> ev_ctx Γ
.
Arguments K0 {Γ} i .
Arguments K1 {Γ} t π .
Arguments K2 {Γ} v π .

Variant state (Γ : t_ctx) : Type :=
| Cut : term Γ -> ev_ctx Γ -> state Γ
.
Arguments Cut {Γ} t π.

(*|
The sorted family of generalized values.
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
  v_rename f (Lam t) := Lam (t_rename (r_shift f) t) .

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
Definition a_ren {Γ1 Γ2 Γ3} : Γ2 ⊆ Γ3 -> Γ1 =[val_m]> Γ2 -> Γ1 =[val_m]> Γ3 :=
  fun f g _ i => m_rename f _ (g _ i) .
(*|
The following bunch of notations will help us to keep the code readable:
|*)
Notation "f ᵣ⊛ₜ t" := (t_rename f t).
Notation "f ᵣ⊛ᵥ v" := (v_rename f v).
Notation "f ᵣ⊛ₑ π" := (e_rename f π) (at level 30, right associativity).
Notation "f ᵣ⊛ₘ v" := (m_rename f _ v) (at level 30, right associativity).
Notation "f ᵣ⊛ₛ s" := (s_rename f s) (at level 30, right associativity).
Notation "f ᵣ⊛ g" := (a_ren f g).
(*|
The weakenings we will need for substitution..
|*)
Definition t_shift {Γ a} := @t_rename Γ (Γ ▶ a) r_pop.
Definition m_shift {Γ a} := @m_rename Γ (Γ ▶ a) r_pop.
Definition a_shift {Γ Δ a} (f : Γ =[val_m]> Δ) :=
  s_map m_shift f ▶ₐ a_id a top .
(*|
Substitutions
^^^^^^^^^^^^^
|*)
Equations t_subst {Γ Δ} : Γ =[val_m]> Δ -> term Γ -> term Δ :=
  t_subst f (Val v)     := Val (v_subst f v) ;
  t_subst f (App t1 t2) := App (t_subst f t1) (t_subst f t2) ;
with v_subst {Γ Δ} : Γ =[val_m]> Δ -> val Γ -> val Δ :=
  v_subst f (Var i) := f _ i ;
  v_subst f (Lam t) := Lam (t_subst (a_shift f) t) .

Equations e_subst {Γ Δ} : Γ =[val_m]> Δ -> ev_ctx Γ -> ev_ctx Δ :=
  e_subst f (K0 i)   := f _ i ;
  e_subst f (K1 t π) := K1 (t_subst f t) (e_subst f π) ;
  e_subst f (K2 v π) := K2 (v_subst f v) (e_subst f π) .

Equations s_subst {Γ Δ} : Γ =[val_m]> Δ -> state Γ -> state Δ :=
  s_subst f (Cut t π) := Cut (t_subst f t) (e_subst f π).

Equations m_subst {Γ Δ} : Γ =[val_m]> Δ -> val_m Γ ⇒ᵢ val_m Δ :=
  m_subst f (⊕) v := v_subst f v ;
  m_subst f (⊖) π := e_subst f π .
(*|
Like renaming, substitution is recast as composition of assigments.
|*)
Definition a_comp {Γ1 Γ2 Γ3} (f : Γ2 =[val_m]> Γ3) (g : Γ1 =[val_m]> Γ2)
  : Γ1 =[val_m]> Γ3 := s_map (m_subst f) g .
(*|
A couple more notations.
|*)
Notation "f ⊛ₜ t" := (t_subst f t).
Notation "f ⊛ᵥ v" := (v_subst f v).
Notation "f ⊛ₑ π" := (e_subst f π) (at level 30, right associativity).
Notation "f ⊛ₘ v" := (m_subst f _ v) (at level 30, right associativity).
Notation "f ⊛ₛ s" := (s_subst f s) (at level 30, right associativity).
Notation "f ⊛ g" := (a_comp f g).
(*|
Single-variable substitution.
|*)
Definition assign1 {Γ a} v : (Γ ▶ a) =[val_m]> Γ := a_id ▶ₐ v .
Definition t_subst1 {Γ a} (t : term _) v := @assign1 Γ a v ⊛ₜ t.
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
  obs_dom (@ORet) := ∅ ▶ ⊕ ;
  obs_dom (@OApp) := ∅ ▶ ⊕ ▶ ⊖ .
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
Definition nf  (Γ : t_ctx) : Type := { a : ty & (Γ ∋ a) × { o : obs a & obs_dom o =[val_m]> Γ } } .
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
  eval_step (Cut (Val v)       (K0 i))   := inr (_ ,' (i, (ORet ,' (∅ₐ ▶ₐ v)))) ;
  eval_step (Cut (Val v)       (K1 t π)) := inl (Cut t (K2 v π)) ;
  eval_step (Cut (Val (Var i)) (K2 v π)) := inr (_,' (i, (OApp ,' (∅ₐ ▶ₐ v ▶ₐ π)))) ;
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
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> f1 ᵣ⊛ₜ t = f2 ᵣ⊛ₜ t .
Definition v_ren_proper_P Γ (v : val Γ) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> f1 ᵣ⊛ᵥ v = f2 ᵣ⊛ᵥ v .
Definition e_ren_proper_P Γ (π : ev_ctx Γ) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> f1 ᵣ⊛ₑ π = f2 ᵣ⊛ₑ π .
Lemma ren_proper_prf : syn_ind_args t_ren_proper_P v_ren_proper_P e_ren_proper_P.
  econstructor.
  all: unfold t_ren_proper_P, v_ren_proper_P, e_ren_proper_P.
  all: intros; cbn; f_equal; auto.
  all: apply H.
  now apply r_shift_eq.
Qed.

#[global] Instance t_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> eq ==> eq) (@t_rename Γ Δ).
  intros f1 f2 H1 x y ->; now apply (term_ind_mut _ _ _ ren_proper_prf).
Qed.
#[global] Instance v_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> eq ==> eq) (@v_rename Γ Δ).
  intros f1 f2 H1 x y ->; now apply (val_ind_mut _ _ _ ren_proper_prf).
Qed.
#[global] Instance e_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> eq ==> eq) (@e_rename Γ Δ).
  intros f1 f2 H1 x y ->; now apply (ctx_ind_mut _ _ _ ren_proper_prf).
Qed.
#[global] Instance m_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@m_rename Γ Δ).
  intros ? ? H1 [] _ ? ->; cbn in *; now rewrite H1.
Qed.
#[global] Instance s_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> eq ==> eq) (@s_rename Γ Δ).
  intros ? ? H1 _ x ->; destruct x; cbn; now rewrite H1.
Qed.
#[global] Instance a_ren_eq {Γ1 Γ2 Γ3}
  : Proper (ass_eq _ _ ==> ass_eq _ _ ==> ass_eq _ _) (@a_ren Γ1 Γ2 Γ3).
  intros ? ? H1 ? ? H2 ? ?; apply (m_ren_eq _ _ H1), H2.
Qed.
#[global] Instance a_shift_eq {Γ Δ x} : Proper (ass_eq _ _ ==> ass_eq _ _) (@a_shift Γ Δ x).
  intros ? ? H ? h.
  dependent elimination h; cbn; auto.
  unfold s_map; now rewrite H.
Qed.
(*|
Renaming-renaming assocativity.
|*)
Definition t_ren_ren_P Γ1 (t : term Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2),
    f1 ᵣ⊛ₜ (f2 ᵣ⊛ₜ t) = (f1 ⊛ᵣ f2) ᵣ⊛ₜ t .
Definition v_ren_ren_P Γ1 (v : val Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2),
    f1 ᵣ⊛ᵥ (f2 ᵣ⊛ᵥ v) = (f1 ⊛ᵣ f2) ᵣ⊛ᵥ v .
Definition e_ren_ren_P Γ1 (π : ev_ctx Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2),
    f1 ᵣ⊛ₑ (f2 ᵣ⊛ₑ π) = (f1 ⊛ᵣ f2) ᵣ⊛ₑ π .

Lemma ren_ren_prf : syn_ind_args t_ren_ren_P v_ren_ren_P e_ren_ren_P .
  econstructor.
  all: unfold t_ren_ren_P, v_ren_ren_P, e_ren_ren_P.
  all: intros; cbn; f_equal; auto.
  all: now repeat rewrite r_shift_comp.
Qed.

Lemma t_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) (t : term Γ1)
  : f1 ᵣ⊛ₜ (f2 ᵣ⊛ₜ t) = (f1 ⊛ᵣ f2) ᵣ⊛ₜ t .
  now apply (term_ind_mut _ _ _ ren_ren_prf).
Qed.
Lemma v_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) (v : val Γ1)
  : f1 ᵣ⊛ᵥ (f2 ᵣ⊛ᵥ v) = (f1 ⊛ᵣ f2) ᵣ⊛ᵥ v .
  now apply (val_ind_mut _ _ _ ren_ren_prf).
Qed.
Lemma e_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) (π : ev_ctx Γ1)
  : f1 ᵣ⊛ₑ (f2 ᵣ⊛ₑ π) = (f1 ⊛ᵣ f2) ᵣ⊛ₑ π .
  now apply (ctx_ind_mut _ _ _ ren_ren_prf).
Qed.
Lemma m_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) a (v : val_m Γ1 a)
  : f1 ᵣ⊛ₘ (f2 ᵣ⊛ₘ v) = (f1 ⊛ᵣ f2) ᵣ⊛ₘ v .
  destruct a; [ now apply v_ren_ren | now apply e_ren_ren ].
Qed.
Lemma s_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) (s : state Γ1)
  : f1 ᵣ⊛ₛ (f2 ᵣ⊛ₛ s) = (f1 ⊛ᵣ f2) ᵣ⊛ₛ s .
  destruct s; apply (f_equal2 Cut); [ now apply t_ren_ren | now apply e_ren_ren ].
Qed.
(*|
Left identity law of renaming.
|*)
Definition t_ren_id_l_P Γ (t : term Γ) : Prop := r_id ᵣ⊛ₜ t = t .
Definition v_ren_id_l_P Γ (v : val Γ) : Prop := r_id ᵣ⊛ᵥ v = v .
Definition e_ren_id_l_P Γ (π : ev_ctx Γ) : Prop := r_id ᵣ⊛ₑ π = π .
Lemma ren_id_l_prf : syn_ind_args t_ren_id_l_P v_ren_id_l_P e_ren_id_l_P .
  econstructor.
  all: unfold t_ren_id_l_P, v_ren_id_l_P, e_ren_id_l_P.
  all: intros; cbn; f_equal; auto.
  now repeat rewrite r_shift_id.
Qed.

Lemma t_ren_id_l {Γ} (t : term Γ) : r_id ᵣ⊛ₜ t = t .
  now apply (term_ind_mut _ _ _ ren_id_l_prf).
Qed.
Lemma v_ren_id_l {Γ} (v : val Γ) : r_id ᵣ⊛ᵥ v = v .
  now apply (val_ind_mut _ _ _ ren_id_l_prf).
Qed.
Lemma e_ren_id_l {Γ} (π : ev_ctx Γ) : r_id ᵣ⊛ₑ π = π .
  now apply (ctx_ind_mut _ _ _ ren_id_l_prf).
Qed.
Lemma m_ren_id_l {Γ a} (v : val_m Γ a) : r_id ᵣ⊛ₘ v = v .
  destruct a; [ now apply v_ren_id_l | now apply e_ren_id_l ].
Qed.
Lemma s_ren_id_l {Γ} (s : state Γ) : r_id ᵣ⊛ₛ s = s .
  destruct s; apply (f_equal2 Cut); [ now apply t_ren_id_l | now apply e_ren_id_l ].
Qed.
(*|
Right identity law of renaming.
|*)
Lemma m_ren_id_r {Γ Δ} (f : Γ ⊆ Δ) {a} (i : Γ ∋ a) : f ᵣ⊛ₘ a_id a i = a_id a (f a i) .
  now destruct a.
Qed.
Lemma a_ren_id_r {Γ Δ} (f : Γ ⊆ Δ) : f ᵣ⊛ a_id ≡ₐ a_id ⊛ᵣ f .
  intros ? ?; now apply m_ren_id_r.
Qed.
Lemma a_shift_id {Γ x} : @a_shift Γ Γ x a_id ≡ₐ a_id.
  unfold a_shift, m_shift; intros ? h.
  dependent elimination h; cbn; auto.
  exact (m_ren_id_r _ _).
Qed.
(*|
Shifting assigments commutes with left and right renaming.
|*)
Lemma a_shift_s_ren {Γ1 Γ2 Γ3 a} (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 ⊆ Γ2)
  : @a_shift _ _ a (f1 ⊛ᵣ f2) ≡ₐ a_shift f1 ⊛ᵣ r_shift f2 .
  intros ? h; dependent elimination h; auto.
Qed.
Lemma a_shift_a_ren {Γ1 Γ2 Γ3 a} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val_m]> Γ2)
      : @a_shift _ _ a (f1 ᵣ⊛ f2) ≡ₐ r_shift f1 ᵣ⊛ a_shift f2 .
  unfold r_shift, r_shift, a_shift, m_shift, a_ren; intros ? h.
  dependent elimination h; cbn; [ symmetry; exact (a_ren_id_r _ _ _) | ].
  unfold s_map; now rewrite 2 m_ren_ren.
Qed.
(*|
Substitution respects pointwise equality of assigments.
|*)
Definition t_sub_proper_P Γ (t : term Γ) : Prop :=
  forall Δ (f1 f2 : Γ =[val_m]> Δ), f1 ≡ₐ f2 -> f1 ⊛ₜ t = f2 ⊛ₜ t .
Definition v_sub_proper_P Γ (v : val Γ) : Prop :=
  forall Δ (f1 f2 : Γ =[val_m]> Δ), f1 ≡ₐ f2 -> f1 ⊛ᵥ v = f2 ⊛ᵥ v .
Definition e_sub_proper_P Γ (π : ev_ctx Γ) : Prop :=
  forall Δ (f1 f2 : Γ =[val_m]> Δ), f1 ≡ₐ f2 -> f1 ⊛ₑ π = f2 ⊛ₑ π .
Lemma sub_proper_prf : syn_ind_args t_sub_proper_P v_sub_proper_P e_sub_proper_P.
  econstructor.
  all: unfold t_sub_proper_P, v_sub_proper_P, e_sub_proper_P.
  all: intros; cbn; f_equal; auto.
  now apply H, a_shift_eq.
Qed.

#[global] Instance t_sub_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> eq ==> eq) (@t_subst Γ Δ).
  intros ? ? H1 _ ? ->; now apply (term_ind_mut _ _ _ sub_proper_prf).
Qed.
#[global] Instance v_sub_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> eq ==> eq) (@v_subst Γ Δ).
  intros ? ? H1 _ ? ->; now apply (val_ind_mut _ _ _ sub_proper_prf).
Qed.
#[global] Instance e_sub_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> eq ==> eq) (@e_subst Γ Δ).
  intros ? ? H1 _ ? ->; now apply (ctx_ind_mut _ _ _ sub_proper_prf).
Qed.
#[global] Instance m_sub_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@m_subst Γ Δ).
  intros ? ? H1 [] _ ? ->; cbn in *; now rewrite H1.
Qed.
#[global] Instance s_sub_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> eq ==> eq) (@s_subst Γ Δ).
  intros ? ? H1 _ x ->; destruct x; cbn; now rewrite H1.
Qed.
#[global] Instance a_comp_eq {Γ1 Γ2 Γ3} : Proper (ass_eq _ _ ==> ass_eq _ _ ==> ass_eq _ _) (@a_comp Γ1 Γ2 Γ3).
  intros ? ? H1 ? ? H2 ? ?; unfold a_comp, s_map; now rewrite H1, H2.
Qed.
(*|
Renaming-substitution "associativity".
|*)
Definition t_ren_sub_P Γ1 (t : term Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val_m]> Γ2),
    f1 ᵣ⊛ₜ (f2 ⊛ₜ t) = (f1 ᵣ⊛ f2) ⊛ₜ t .
Definition v_ren_sub_P Γ1 (v : val Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val_m]> Γ2),
    f1 ᵣ⊛ᵥ (f2 ⊛ᵥ v) = (f1 ᵣ⊛ f2) ⊛ᵥ v .
Definition e_ren_sub_P Γ1 (π : ev_ctx Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val_m]> Γ2),
    f1 ᵣ⊛ₑ (f2 ⊛ₑ π) = (f1 ᵣ⊛ f2) ⊛ₑ π .
Lemma ren_sub_prf : syn_ind_args t_ren_sub_P v_ren_sub_P e_ren_sub_P.
  econstructor.
  all: unfold t_ren_sub_P, v_ren_sub_P, e_ren_sub_P.
  all: intros; cbn; f_equal.
  all: try rewrite a_shift_a_ren; auto.
Qed.

Lemma t_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val_m]> Γ2) (t : term Γ1)
  : f1 ᵣ⊛ₜ (f2 ⊛ₜ t) = (f1 ᵣ⊛ f2) ⊛ₜ t .
  now apply (term_ind_mut _ _ _ ren_sub_prf).
Qed.
Lemma v_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val_m]> Γ2) (v : val Γ1)
  : f1 ᵣ⊛ᵥ (f2 ⊛ᵥ v) = (f1 ᵣ⊛ f2) ⊛ᵥ v .
  now apply (val_ind_mut _ _ _ ren_sub_prf).
Qed.
Lemma e_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val_m]> Γ2) (π : ev_ctx Γ1)
  : f1 ᵣ⊛ₑ (f2 ⊛ₑ π) = (f1 ᵣ⊛ f2) ⊛ₑ π .
  now apply (ctx_ind_mut _ _ _ ren_sub_prf).
Qed.
Lemma m_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val_m]> Γ2) a (v : val_m Γ1 a)
  : f1 ᵣ⊛ₘ (f2 ⊛ₘ v) = (f1 ᵣ⊛ f2) ⊛ₘ v .
  destruct a; [ now apply v_ren_sub | now apply e_ren_sub ].
Qed.
Lemma s_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val_m]> Γ2) (s : state Γ1)
  : f1 ᵣ⊛ₛ (f2 ⊛ₛ s) = (f1 ᵣ⊛ f2) ⊛ₛ s .
  destruct s; cbn; now rewrite t_ren_sub, e_ren_sub.
Qed.
(*|
Substitution-renaming "associativity".
|*)
Definition t_sub_ren_P Γ1 (t : term Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 ⊆ Γ2),
  f1 ⊛ₜ (f2 ᵣ⊛ₜ t) = (f1 ⊛ᵣ f2) ⊛ₜ t .
Definition v_sub_ren_P Γ1 (v : val Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 ⊆ Γ2),
  f1 ⊛ᵥ (f2 ᵣ⊛ᵥ v) = (f1 ⊛ᵣ f2) ⊛ᵥ v .
Definition e_sub_ren_P Γ1 (π : ev_ctx Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 ⊆ Γ2),
  f1 ⊛ₑ (f2 ᵣ⊛ₑ π) = (f1 ⊛ᵣ f2) ⊛ₑ π .
Lemma sub_ren_prf : syn_ind_args t_sub_ren_P v_sub_ren_P e_sub_ren_P.
  econstructor.
  all: unfold t_sub_ren_P, v_sub_ren_P, e_sub_ren_P.
  all: intros; cbn; f_equal.
  all: try rewrite a_shift_s_ren; auto.
Qed.

Lemma t_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 ⊆ Γ2) (t : term Γ1)
  : f1 ⊛ₜ (f2 ᵣ⊛ₜ t) = (f1 ⊛ᵣ f2) ⊛ₜ t .
  now apply (term_ind_mut _ _ _ sub_ren_prf).
Qed.
Lemma v_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 ⊆ Γ2) (v : val Γ1)
  : f1 ⊛ᵥ (f2 ᵣ⊛ᵥ v) = (f1 ⊛ᵣ f2) ⊛ᵥ v .
  now apply (val_ind_mut _ _ _ sub_ren_prf).
Qed.
Lemma e_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 ⊆ Γ2) (π : ev_ctx Γ1)
  : f1 ⊛ₑ (f2 ᵣ⊛ₑ π) = (f1 ⊛ᵣ f2) ⊛ₑ π .
  now apply (ctx_ind_mut _ _ _ sub_ren_prf).
Qed.
Lemma m_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 ⊆ Γ2) a (v : val_m Γ1 a)
  : f1 ⊛ₘ (f2 ᵣ⊛ₘ v) = (f1 ⊛ᵣ f2) ⊛ₘ v .
  destruct a; [ now apply v_sub_ren | now apply e_sub_ren ].
Qed.
Lemma s_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 ⊆ Γ2) (s : state Γ1)
  : f1 ⊛ₛ (f2 ᵣ⊛ₛ s) = (f1 ⊛ᵣ f2) ⊛ₛ s .
  destruct s; cbn; now rewrite t_sub_ren, e_sub_ren.
Qed.
(*|
Left identity law of substitution.
|*)
Definition t_sub_id_l_P Γ (t : term Γ) : Prop := a_id ⊛ₜ t = t .
Definition v_sub_id_l_P Γ (v : val Γ) : Prop := a_id ⊛ᵥ v = v .
Definition e_sub_id_l_P Γ (π : ev_ctx Γ) : Prop := a_id ⊛ₑ π = π .
Lemma sub_id_l_prf : syn_ind_args t_sub_id_l_P v_sub_id_l_P e_sub_id_l_P.
  econstructor.
  all: unfold t_sub_id_l_P, v_sub_id_l_P, e_sub_id_l_P.
  all: intros; cbn; f_equal; auto.
  all: try rewrite a_shift_id; auto.
Qed.

Lemma t_sub_id_l {Γ} (t : term Γ) : a_id ⊛ₜ t = t .
  now apply (term_ind_mut _ _ _ sub_id_l_prf).
Qed.
Lemma v_sub_id_l {Γ} (v : val Γ) : a_id ⊛ᵥ v = v .
  now apply (val_ind_mut _ _ _ sub_id_l_prf).
Qed.
Lemma e_sub_id_l {Γ} (π : ev_ctx Γ) : a_id ⊛ₑ π = π .
  now apply (ctx_ind_mut _ _ _ sub_id_l_prf).
Qed.
Lemma m_sub_id_l {Γ} a (v : val_m Γ a) : a_id ⊛ₘ v = v.
  destruct a; [ now apply v_sub_id_l | now apply e_sub_id_l ].
Qed.
Lemma s_sub_id_l {Γ} (s : state Γ) : a_id ⊛ₛ s = s.
  destruct s; cbn; now rewrite t_sub_id_l, e_sub_id_l.
Qed.
Lemma a_comp_id_l {Γ1 Γ2} (a : Γ1 =[val_m]> Γ2) : a_id ⊛ a ≡ₐ a .
  intros ? ?; now apply m_sub_id_l.
Qed.
(*|
Right identity law of substitution.
|*)
Lemma m_sub_id_r {Γ1 Γ2} (f : Γ1 =[val_m]> Γ2) {a} (i : Γ1 ∋ a) : f ⊛ₘ a_id a i = f a i.
  now destruct a.
Qed.
Lemma a_comp_id_r {Γ1 Γ2} (f : Γ1 =[val_m]> Γ2) : f ⊛ a_id ≡ₐ f .
  intros a ?; now apply m_sub_id_r.
Qed.
(*|
Shifting assigments respects composition.
|*)
Lemma a_shift_comp {Γ1 Γ2 Γ3 a} (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 =[val_m]> Γ2)
  : @a_shift _ _ a (f1 ⊛ f2) ≡ₐ a_shift f1 ⊛ a_shift f2 .
  unfold a_shift, m_shift, a_comp, s_map; intros ? h.
  dependent elimination h; [ symmetry; exact (a_comp_id_r _ _ _) | cbn ].
  now rewrite m_ren_sub, m_sub_ren.
Qed.
(*|
Substitution-substitution associativity.
|*)
Definition t_sub_sub_P Γ1 (t : term Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 =[val_m]> Γ2),
    f1 ⊛ₜ (f2 ⊛ₜ t) = (f1 ⊛ f2) ⊛ₜ t.
Definition v_sub_sub_P Γ1 (v : val Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 =[val_m]> Γ2),
    f1 ⊛ᵥ (f2 ⊛ᵥ v) = (f1 ⊛ f2) ⊛ᵥ v.
Definition e_sub_sub_P Γ1 (π : ev_ctx Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 =[val_m]> Γ2),
    f1 ⊛ₑ (f2 ⊛ₑ π) = (f1 ⊛ f2) ⊛ₑ π.
Lemma sub_sub_prf : syn_ind_args t_sub_sub_P v_sub_sub_P e_sub_sub_P.
  econstructor.
  all: unfold t_sub_sub_P, v_sub_sub_P, e_sub_sub_P.
  all: intros; cbn; f_equal.
  all: try rewrite a_shift_comp; auto.
Qed.

Lemma t_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 =[val_m]> Γ2) (t : term Γ1)
  : f1 ⊛ₜ (f2 ⊛ₜ t) = (f1 ⊛ f2) ⊛ₜ t.
  now apply (term_ind_mut _ _ _ sub_sub_prf).
Qed.
Lemma v_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 =[val_m]> Γ2) (v : val Γ1)
  : f1 ⊛ᵥ (f2 ⊛ᵥ v) = (f1 ⊛ f2) ⊛ᵥ v.
  now apply (val_ind_mut _ _ _ sub_sub_prf).
Qed.
Lemma e_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 =[val_m]> Γ2) (π : ev_ctx Γ1)
  : f1 ⊛ₑ (f2 ⊛ₑ π) = (f1 ⊛ f2) ⊛ₑ π.
  now apply (ctx_ind_mut _ _ _ sub_sub_prf).
Qed.
Lemma m_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 =[val_m]> Γ2) a (v : val_m Γ1 a)
  : f1 ⊛ₘ (f2 ⊛ₘ v) = (f1 ⊛ f2) ⊛ₘ v.
  destruct a; [ now apply v_sub_sub | now apply e_sub_sub ].
Qed.
Lemma s_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ2 =[val_m]> Γ3) (f2 : Γ1 =[val_m]> Γ2) (s : state Γ1)
  : f1 ⊛ₛ (f2 ⊛ₛ s) = (f1 ⊛ f2) ⊛ₛ s.
  destruct s; cbn; now rewrite t_sub_sub, e_sub_sub.
Qed.
Lemma a_comp_assoc {Γ1 Γ2 Γ3 Γ4} (u : Γ3 =[val_m]> Γ4) (v : Γ2 =[val_m]> Γ3) (w : Γ1 =[val_m]> Γ2)
           : u ⊛ (v ⊛ w) ≡ₐ (u ⊛ v) ⊛ w .
  intros ? ?; unfold a_comp; now apply m_sub_sub.
Qed.
Lemma a_sub1_sub {Γ Δ a} (f : Γ =[val_m]> Δ) (v : val_m Γ a)
  : assign1 (f ⊛ₘ v) ⊛ a_shift f ≡ₐ f ⊛ (assign1 v).

  intros ? h; unfold a_comp, s_map.
  dependent elimination h; [ cbn; now rewrite m_sub_id_r | ].
  cbn; unfold s_map, m_shift; rewrite m_sub_ren, m_sub_id_r.
  now apply m_sub_id_l.
Qed.
Lemma t_sub1_sub {Γ Δ x} (f : Γ =[val_m]> Δ) (t : term (Γ ▶ x)) v
  : t_subst (a_shift f) t /[ m_subst f _ v ] = t_subst f (t /[ v ]) .
  unfold t_subst1; now rewrite 2 t_sub_sub, a_sub1_sub.
Qed.
(*|
The Actual Instance
-------------------

We can now instanciate our framework with untyped lambda calculus.
|*)
#[local] Instance ulc_typ  : baseT := {| typ := ty |}.

#[local] Instance ulc_spec : observation_structure :=
  {| Obs.obs := obs ;
     dom := @obs_dom |} .

#[local] Instance ulc_val  : baseV :=
  {| Subst.val := val_m |}.
#[local] Instance ulc_val_mon : subst_monoid _ :=
  {| v_var := @a_id ;
     v_sub := @m_subst |} .
#[local] Instance ulc_val_laws : subst_monoid_laws :=
  {| v_sub_proper := @m_sub_eq ;
     v_sub_var := @a_comp_id_r ;
     v_var_sub := @a_comp_id_l ;
     Subst.v_sub_sub := @a_comp_assoc |} .

#[local] Instance ulc_conf : baseC :=
  {| Subst.conf := state |}.
#[local] Instance ulc_conf_mod : subst_module _ _ :=
  {| c_sub := @s_subst |} .
#[local] Instance ulc_conf_laws : subst_module_laws :=
  {| c_sub_proper := @s_sub_eq ;
     c_var_sub := @s_sub_id_l ;
     c_sub_sub := @s_sub_sub |} .

#[local] Instance ulc_var_laws : var_assumptions.
  econstructor; intros.
  - destruct x; now dependent induction H.
  - destruct x; induction v; try (apply inr; intros [ i H ]; now inversion H).
    all: apply inl; econstructor; auto.
  - destruct X as [ i H ].
    destruct x; induction v; try now inversion H.
    all: refine (h ,' eq_refl).
Defined.

#[local] Instance ulc_machine : machine :=
  {| eval := @ulc_eval ;
     app := @obs_app |} .

(*|
We now prove the remaining hypotheses of the machine.
We pull in some tooling for coinductive reasoning on the delay monad.
|*)
From Coinduction Require Import coinduction lattice rel tactics.
From OGS.ITree Require Import Eq.

#[local] Instance ulc_machine_law : machine_laws.
  econstructor; intros; unfold ulc_spec, ulc_val in *; cbn in *.
(*|
Applying an observation respects pointwise equality of assigments.
|*)
  - intros ? ? H1; dependent elimination m; cbn; repeat (f_equal; auto).
(*|
Applying an observation commutes with renamings.
|*)
  - destruct x; dependent elimination m; cbn; f_equal.
(*|
Evaluation respects substitution.
|*)
  - revert c e; unfold comp_eq, it_eq; coinduction R CIH; intros c e.
    destruct c. cbn in e0.
    dependent elimination t.
    * dependent elimination e0.
      + unfold ulc_eval at 2; cbn - [ ulc_eval ];
          change (it_eqF _ ?a ?b T1_0 (observe ?x) (_observe ?y)) with (it_eq_bt _ a R T1_0 x y).
        refine (gfp_bt (it_eq_map _ _) R T1_0 _ _ _); reflexivity.
      + cbn; econstructor;
          change (Structure.iter _ _ ?a) with (ulc_eval a);
          change (Structure.subst (fun pat : T1 => let 'T1_0 := pat in ?f) T1_0 ?u) with (bind_delay' u f).
        exact (CIH (Cut t0 (K2 v e0)) e).
      + dependent elimination v.
        ++ unfold ulc_eval at 2; cbn - [ ulc_eval ];
             change (it_eqF _ ?a _ T1_0 (observe ?x) (_observe ?y)) with (it_eq_bt _ a R T1_0 x y).
           refine (gfp_bt (it_eq_map _ _) R T1_0 _ _ _); reflexivity.
        ++ cbn; econstructor;
           change (v_subst e ?a) with (m_subst e (⊕) a); rewrite t_sub1_sub.
           exact (CIH (Cut (t0 /[ v0 ]) e1) e).
    * cbn; econstructor.
      exact (CIH (Cut t1 (K1 t0 e0)) e).
(*|
Evaluating a normal form yields the same normal form instantly.
|*)
  - destruct u as [ a [ i [ p γ ] ]].
    unfold nf'_ty, nf'_var, nf'_val, a_id; cbn in *.
    destruct a; dependent elimination p; cbn in *.
    all: unfold comp_eq; apply it_eq_unstep; cbn; econstructor.
    all: do 3 (unshelve econstructor; auto; cbn).
    all: intros ? h; do 3 (dependent elimination h; auto).
(*|
The language "has finite redexes" (wellfoundedness of the head instanciation relation).
|*)
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
        pose (vv :=e (⊕) Ctx.top); change (e (⊕) Ctx.top) with vv in i0; remember vv; clear vv Heqv0 e.
        dependent elimination v; try now destruct (p (_ ,' eq_refl)).
        apply it_eq_step in i0; now inversion i0.
        dependent elimination v0; apply it_eq_step in i0; cbn in i0; dependent elimination i0.
        unfold obs'_of_nf' in r_rel; cbn in r_rel.
        inversion_sigma r_rel; dependent elimination r_rel1; clear .
        econstructor; intros [ z p ] H.
        destruct z; dependent elimination p; dependent elimination H.
        ++ dependent elimination v; try now destruct (p (_ ,' eq_refl)).
           apply it_eq_step in i0; now inversion i0.
        ++ dependent elimination v; try now destruct (p (_ ,' eq_refl)).
           apply it_eq_step in i0; now inversion i0.
      + cbn in *.
        pose (vv :=e (⊕) Ctx.top); change (e (⊕) Ctx.top) with vv in i0; remember vv; clear vv Heqv0 e.
        dependent elimination v; try now destruct (p (_ ,' eq_refl)).
        apply it_eq_step in i0; now inversion i0.
        dependent elimination v0; apply it_eq_step in i0; cbn in i0; dependent elimination i0.
        unfold obs'_of_nf' in r_rel; cbn in r_rel.
        inversion_sigma r_rel; inversion r_rel1.
Qed.
(*|
And this is it. Lets instanciate the notions to enjoy a nice readable type for our theorem.
|*)
Definition subst_eq Δ {Γ} : relation (state Γ) :=
  fun u v => forall σ : Γ =[val_m]> Δ, eval_to_obs (σ ⊛ₛ u) ≈ eval_to_obs (σ ⊛ₛ v) .
Notation "x ≈[sub Δ ]≈ y" := (subst_eq Δ x y) (at level 10).
(*|
Our semantic objects live in what is defined in the generic construction as
`ogs_act`, that is active strategies for the OGS game. They come with their
own notion of equivalence, weak bisimilarity and we get to interpret states
into semantic objects.
|*)
Definition sem_act Δ Γ := ogs_act Δ (∅ ▶ Γ) .

Definition ogs_weq_act Δ {Γ} : relation (sem_act Δ Γ) := fun u v => u ≈ v .
Notation "u ≈[ogs Δ ]≈ v" := (ogs_weq_act Δ u v) (at level 40).

Definition interp_act_s Δ {Γ} (c : state Γ) : sem_act Δ Γ := m_strat (∅ ▶ Γ) (inj_init_act Δ c) .
Notation "⟦ t ⟧ₛ" := (interp_act_s _ t) .
(*|
We can now obtain our instance of the correctness result!
|*)
Theorem ulc_subst_correct Δ {Γ} (x y : state Γ)
  : ⟦ x ⟧ₛ ≈[ogs Δ ]≈ ⟦ y ⟧ₛ -> x ≈[sub Δ ]≈ y .
  exact (ogs_correction Δ x y).
Qed.
(*|
Recovering CIU-equivalence
^^^^^^^^^^^^^^^^^^^^^^^^^^
|*)
Definition ciu_eq Δ {Γ} : relation (term Γ) :=
  fun u v => forall (σ : Γ =[val_m]> Δ) (π : ev_ctx Δ),
      eval_to_obs (Cut (σ ⊛ₜ u) π) ≈ eval_to_obs (Cut (σ ⊛ₜ v) π) .
Notation "x ≈[ciu Δ ]≈ y" := (ciu_eq Δ x y) (at level 10).
(*|
Embedding terms into states.
|*)
Definition c_init {Γ} (t : term Γ) : state (Γ ▶ ⊖)
  := Cut (t_shift t) (K0 Ctx.top) .
Notation "⟦ t ⟧ₜ" := (⟦ c_init t ⟧ₛ) .
(*|
Embedding evaluation context and assignment into generalized assignments.
|*)
Definition a_of_sk {Γ Δ} (σ : Γ =[val_m]> Δ) (π : ev_ctx Δ)
  : (Γ ▶ ⊖) =[val_m]> Δ := σ ▶ₐ (π : val_m _ (⊖)) .
(*|
Relating the two previous embeddings with substitution.
|*)
Lemma sub_init {Γ Δ} (t : term Γ) (σ : Γ =[val_m]> Δ) (π : ev_ctx Δ)
  : Cut (σ ⊛ₜ t) π = a_of_sk σ π ⊛ₛ c_init t .
  cbn; unfold t_shift; now rewrite t_sub_ren.
Qed.
(*|
The more standard CIU statement for terms.
|*)
Theorem ulc_ciu_correct Δ {Γ} (x y : term Γ)
  : ⟦ x ⟧ₜ ≈[ogs Δ ]≈ ⟦ y ⟧ₜ -> x ≈[ciu Δ ]≈ y .
  intros H σ k; rewrite 2 sub_init.
  now apply ulc_subst_correct.
Qed.
(*|
Some bonus example terms.
|*)
Module ExampleTerms.
(*|
λx.xx
|*)
Definition t_self_app : term ∅ := Val (Lam (App (Val (Var Ctx.top)) (Val (Var Ctx.top)))) .
(*|
`Ω = (λx.xx)(λx.xx)
|*)
Definition t_omega : term ∅ := App t_self_app t_self_app .
End ExampleTerms.
