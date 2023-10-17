From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel Ctx.
From OGS.Game Require Import Event.
From OGS.ITree Require Import ITree Eq Delay Structure Properties.
Set Equations Transparent.

Inductive ty0 : Type :=
| ι : ty0
| Arr : ty0 -> ty0 -> ty0
.

Derive NoConfusion for ty0.
Declare Scope ty_scope.
Delimit Scope ty_scope with ty.
Bind Scope ty_scope with ty0.

Notation "A → B" := (Arr A B) (at level 40) : ty_scope .

Variant ty : Type :=
| VTy : ty0 -> ty
| KTy : ty0 -> ty
.
Derive NoConfusion for ty.
Bind Scope ty_scope with ty.
Notation "'t+' t" := (VTy t) (at level 20) : ty_scope .
Notation "'t-' t" := (KTy t) (at level 20) : ty_scope .
Open Scope ty_scope.

Equations t_neg : ty -> ty :=
  t_neg (t+ a) := t- a ;
  t_neg (t- a) := t+ a .

Definition t_ctx : Type := Ctx.ctx ty.
Bind Scope ctx_scope with t_ctx.

Inductive term : t_ctx -> ty -> Type :=
| Val {Γ a}      : val Γ a -> term Γ a
| App {Γ a b}    : term Γ (t+ (a → b)) -> term Γ (t+ a) -> term Γ (t+ b)
with val : t_ctx -> ty -> Type :=
| Var {Γ a}      : Γ ∋ a -> val Γ a
| LamRec {Γ a b} : term (Γ ▶ t+ (a → b) ▶ t+ a) (t+ b) -> val Γ (t+ (a → b))
| KFun {Γ a b}   : term Γ (t+ (a → b)) -> val Γ (t- b) -> val Γ (t- a)
| KArg {Γ a b}   : val  Γ (t+ a) -> val Γ (t- b) -> val Γ (t- (a → b))
.

Variant state : t_ctx -> Type :=
| Cut {Γ a} : term Γ (t+ a) -> val Γ (t- a) -> state Γ
.

Definition a_id {Γ} : has Γ ⇒ᵢ val Γ := fun _ => Var.

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

Definition a_ren {Γ1 Γ2 Γ3} : Γ2 ⊆ Γ3 -> Γ1 =[val]> Γ2 -> Γ1 =[val]> Γ3 :=
  fun f g _ i => v_rename f _ (g _ i) .

Definition t_shift  {Γ} [y] : term Γ ⇒ᵢ term (Γ ▶ y)  := @t_rename _ _ s_pop.
Definition s_shift  {Γ} [y] : state Γ -> state (Γ ▶ y) := @s_rename _ _ s_pop.
Definition v_shift  {Γ} [y] : val Γ ⇒ᵢ val (Γ ▶ y)    := @v_rename _ _ s_pop.
Definition v_shift2  {Γ} [y z] : val Γ ⇒ᵢ val (Γ ▶ y ▶ z)  := @v_rename _ _ (s_pop ⊛ᵣ s_pop).

Definition a_shift {Γ Δ} [y] (a : Γ =[val]> Δ) : (Γ ▶ y) =[val]> (Δ ▶ y) :=
  s_append (fun _ i => v_shift _ (a _ i)) (Var top).

Definition a_shift2 {Γ Δ} [x y] (a : Γ =[val]> Δ) : (Γ ▶ x ▶ y) =[val]> (Δ ▶ x ▶ y) :=
  s_append (s_append (fun _ i => v_shift2 _ (a _ i))
              (Var (pop top)))
    (Var top).

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

(* In essence,
 Definition pat : ty -> Type := fun _ => unit.
 Definition pat_dom {a} : pat a -> neg_ctx := fun a => ∅ ▶ a.
 Definition v_of_p {a} (p : pat a) : val (pat_dom p) a := Var p.
 Definition p_of_v {Γ : neg_ctx} a : val Γ a -> pat (t+ a) := fun _ => tt.
 Definition p_dom_of_v {Γ : neg_ctx} a (v : val Γ a) : pat_dom (p_of_v0 a v) =[val]> Γ := s_append s_empty v
 *)

Definition nf0 (Γ : t_ctx) (a : ty) : Type := val Γ (t_neg a).
(* a producer type: "⟨ x | π ⟩"
   a consumer type: "⟨ v | x ⟩"
 *)
Definition nf  (Γ : t_ctx) : Type :=
  { a : ty & (Γ ∋ a * nf0 Γ a)%type } .

Equations eval_aux {Γ : t_ctx} : state Γ -> (state Γ + nf Γ) :=
  {
    eval_aux (Cut (Val v) (KFun t π))          :=
      inl (Cut t (KArg v π));
    eval_aux (Cut (Val v) (Var i))             :=
      inr (t-_ ,' (i,v));

    eval_aux (Cut (Val (Var i))    π)          :=
      inr (t+_,' (i,π));

    eval_aux (Cut (Val (LamRec t)) (KArg v π)) :=
      inl (Cut (t/ₜ[LamRec t , v]) π);

    eval_aux (Cut (App t1 t2)    π)            :=
      inl (Cut t2 (KFun t1 π))
  }.
Definition eval {Γ : t_ctx} : state Γ -> delay (nf Γ)
  := iter_delay (fun c => Ret' (eval_aux c)).
Notation play := eval.

