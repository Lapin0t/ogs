From OGS Require Import Prelude.
From OGS.Utils Require Import Ctx.
From OGS.Game Require Import Event.
From OGS.ITree Require Import ITree Monad Delay.

Inductive ty0 : Type :=
| Zer : ty0
| One : ty0
| Prod : ty0 -> ty0 -> ty0
| Sum : ty0 -> ty0 -> ty0
| Arr : ty0 -> ty0 -> ty0
.

(*| .. coq:: none |*)
Derive NoConfusion for ty0.
Declare Scope ty_scope.
Delimit Scope ty_scope with ty.
Bind Scope ty_scope with ty0.

(*||*)
Notation "A × B" := (Prod A B) (at level 40) : ty_scope.
Notation "A + B" := (Sum A B) : ty_scope.
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

(* changer la syntaxe: valeurs uniquement pour les constructeurs + *)
Inductive term : t_ctx -> ty -> Type :=
(* terms *)
| Mu {Γ a} : state (Γ ▶ t- a) -> term Γ (t+ a)
| Val {Γ a} : val0 Γ a -> term Γ (t+ a)
(* co-terms *)
| VarN {Γ a} : Γ ∋ t- a -> term Γ (t- a)
| Mu' {Γ a} : state (Γ ▶ t+ a) -> term Γ (t- a)
| ZerK {Γ} : term Γ (t- Zer)
| App {Γ a b} : val0 Γ a -> term Γ (t- b) -> term Γ (t- (a → b))
| Fst {Γ a b} : term Γ (t- a) -> term Γ (t- (a × b))
| Snd {Γ a b} : term Γ (t- b) -> term Γ (t- (a × b))
| Match {Γ a b} : state (Γ ▶ t+ a) -> state (Γ ▶ t+ b) -> term Γ (t- (a + b))
with val0 : t_ctx -> ty0 -> Type :=
| VarP {Γ a} : Γ ∋ t+ a -> val0 Γ a
| Inl {Γ a b} : val0 Γ a -> val0 Γ (a + b)
| Inr {Γ a b} : val0 Γ b -> val0 Γ (a + b)
| OneI {Γ} : val0 Γ One
| LamRec {Γ a b} : term (Γ ▶ t+ (a → b) ▶ t+ a) (t+ b) -> val0 Γ (a → b)
| Pair {Γ a b} : term Γ (t+ a) -> term Γ (t+ b) -> val0 Γ (a × b)
with state : t_ctx -> Type :=
| Cut {Γ a} : term Γ (t+ a) -> term Γ (t- a) -> state Γ
.

Equations val : t_ctx -> ty -> Type :=
  val Γ (t+ a) := val0 Γ a ;
  val Γ (t- a) := term Γ (t- a) .

Equations t_rename_aux {Γ Δ} ts : Γ ⊆ Δ -> term (Γ +▶ ts) ⇒ᵢ term (Δ +▶ ts) :=
  t_rename_aux ts f _ (Mu c)    := Mu (s_rename_aux (ts ▶ _) f c) ;
  t_rename_aux ts f _ (Val v)   := Val (v0_rename_aux ts f _ v) ;
  t_rename_aux ts f _ (VarN i)  := VarN (r_shift_n ts f _ i) ;
  t_rename_aux ts f _ (Mu' c)   := Mu' (s_rename_aux (ts ▶ _) f c) ;
  t_rename_aux ts f _ (ZerK)    := ZerK ;
  t_rename_aux ts f _ (App u k) := App (v0_rename_aux ts f _ u) (t_rename_aux ts f _ k) ;
  t_rename_aux ts f _ (Fst k)   := Fst (t_rename_aux ts f _ k) ;
  t_rename_aux ts f _ (Snd k)   := Snd (t_rename_aux ts f _ k) ;
  t_rename_aux ts f _ (Match c1 c2) :=
    Match (s_rename_aux (ts ▶ _) f c1)
          (s_rename_aux (ts ▶ _) f c2)
with v0_rename_aux {Γ Δ} ts : Γ ⊆ Δ -> val0 (Γ +▶ ts) ⇒ᵢ val0 (Δ +▶ ts) :=
  v0_rename_aux ts f _ (VarP i)   := VarP (r_shift_n ts f _ i) ;
  v0_rename_aux ts f _ (OneI)     := OneI ;
  v0_rename_aux ts f _ (LamRec u) := LamRec (t_rename_aux (ts ▶ _ ▶ _) f _ u) ;
  v0_rename_aux ts f _ (Pair u v) := Pair (t_rename_aux ts f _ u) (t_rename_aux ts f _ v) ;
  v0_rename_aux ts f _ (Inl u)    := Inl (v0_rename_aux ts f _ u) ;
  v0_rename_aux ts f _ (Inr u)    := Inr (v0_rename_aux ts f _ u)
with s_rename_aux {Γ Δ} ts : Γ ⊆ Δ -> state (Γ +▶ ts) -> state (Δ +▶ ts) :=
   s_rename_aux ts f (Cut v k) := Cut (t_rename_aux ts f _ v) (t_rename_aux ts f _ k) .

Equations v_rename_aux {Γ Δ} ts : Γ ⊆ Δ -> val (Γ +▶ ts) ⇒ᵢ val (Δ +▶ ts) :=
  v_rename_aux ts f (t+ _) v := v0_rename_aux ts f _ v ;
  v_rename_aux ts f (t- _) k := t_rename_aux ts f _ k .

Equations Var {Γ} : has Γ ⇒ᵢ val Γ :=
  Var (t+ _) i := VarP i ;
  Var (t- _) i := VarN i .

Definition t_rename  {Γ Δ} (f : Γ ⊆ Δ) := @t_rename_aux Γ Δ ∅ f.
Definition v0_rename {Γ Δ} (f : Γ ⊆ Δ) := @v0_rename_aux Γ Δ ∅ f.
Definition s_rename  {Γ Δ} (f : Γ ⊆ Δ) := @s_rename_aux Γ Δ ∅ f.
Definition v_rename  {Γ Δ} (f : Γ ⊆ Δ) := @v_rename_aux Γ Δ ∅ f.

Definition t_shift  {Γ} [y] : term Γ ⇒ᵢ term (Γ ▶ y)  := @t_rename _ _ s_pop.
Definition v0_shift {Γ} [y] : val0 Γ ⇒ᵢ val0 (Γ ▶ y)  := @v0_rename _ _ s_pop.
Definition s_shift  {Γ} [y] : state Γ -> state (Γ ▶ y) := @s_rename _ _ s_pop.
Definition v_shift  {Γ} [y] : val Γ ⇒ᵢ val (Γ ▶ y)    := @v_rename _ _ s_pop.

Equations t_of_v {Γ} : val Γ ⇒ᵢ term Γ :=
  t_of_v (t+ _) v := Val v ;
  t_of_v (t- _) k := k .

Equations a_shift_n {Γ Δ} ts : Γ =[val]> Δ -> (Γ +▶ ts) =[val]> (Δ +▶ ts) :=
  a_shift_n ts f _ i with cat_split i :=
    { | CLeftV j := v_rename r_concat_l _ (f _ j) ;
      | CRightV j := Var _ (r_concat_r _ j) } .

Equations t_subst_aux {Γ Δ} ts : Γ =[val]> Δ -> term (Γ +▶ ts) ⇒ᵢ term (Δ +▶ ts) :=
  t_subst_aux ts f _ (Mu c)    := Mu (s_subst_aux (ts ▶ _) f c) ;
  t_subst_aux ts f _ (Val v)   := Val (v0_subst_aux ts f _ v) ;
  t_subst_aux ts f _ (VarN i)  := a_shift_n ts f _ i ;
  t_subst_aux ts f _ (Mu' c)   := Mu' (s_subst_aux (ts ▶ _) f c) ;
  t_subst_aux ts f _ (ZerK)    := ZerK ;
  t_subst_aux ts f _ (App u k) := App (v0_subst_aux ts f _ u) (t_subst_aux ts f _ k) ;
  t_subst_aux ts f _ (Fst k)   := Fst (t_subst_aux ts f _ k) ;
  t_subst_aux ts f _ (Snd k)   := Snd (t_subst_aux ts f _ k) ;
  t_subst_aux ts f _ (Match c1 c2) :=
    Match (s_subst_aux (ts ▶ _) f c1)
          (s_subst_aux (ts ▶ _) f c2)
with v0_subst_aux {Γ Δ} ts : Γ =[val]> Δ -> val0 (Γ +▶ ts) ⇒ᵢ val0 (Δ +▶ ts) :=
  v0_subst_aux ts f _ (VarP i)   := a_shift_n ts f _ i ;
  v0_subst_aux ts f _ (OneI)     := OneI ;
  v0_subst_aux ts f _ (LamRec u) := LamRec (t_subst_aux (ts ▶ _ ▶ _) f _ u) ;
  v0_subst_aux ts f _ (Pair u v) := Pair (t_subst_aux ts f _ u) (t_subst_aux ts f _ v) ;
  v0_subst_aux ts f _ (Inl u)    := Inl (v0_subst_aux ts f _ u) ;
  v0_subst_aux ts f _ (Inr u)    := Inr (v0_subst_aux ts f _ u)
with s_subst_aux {Γ Δ} ts : Γ =[val]> Δ -> state (Γ +▶ ts) -> state (Δ +▶ ts) :=
   s_subst_aux ts f (Cut v k) := Cut (t_subst_aux ts f _ v) (t_subst_aux ts f _ k) .

Equations v_subst_aux {Γ Δ} ts : Γ =[val]> Δ -> val (Γ +▶ ts) ⇒ᵢ val (Δ +▶ ts) :=
  v_subst_aux ts f (t+ _) v := v0_subst_aux ts f _ v ;
  v_subst_aux ts f (t- _) k := t_subst_aux ts f _ k .

Definition t_subst  {Γ Δ} (f : Γ =[val]> Δ) := @t_subst_aux Γ Δ ∅ f.
Definition v0_subst {Γ Δ} (f : Γ =[val]> Δ) := @v0_subst_aux Γ Δ ∅ f.
Definition s_subst  {Γ Δ} (f : Γ =[val]> Δ) := @s_subst_aux Γ Δ ∅ f.
Definition v_subst  {Γ Δ} (f : Γ =[val]> Δ) := @v_subst_aux Γ Δ ∅ f.

Definition ass1 {Γ a} (v : val Γ a) : (Γ ▶ a) =[val]> Γ := s_append Var v .

Definition t_subst1  {Γ a b} (u : term (Γ ▶ a) b) v := t_subst (ass1 v) _ u.
Definition v0_subst1 {Γ a b} (u : val0 (Γ ▶ a) b) v := v0_subst (ass1 v) _ u.
Definition v_subst1  {Γ a b} (u : val (Γ ▶ a) b)  v := v_subst (ass1 v) _ u.
Definition s_subst1  {Γ a}   (u : state (Γ ▶ a))  v := s_subst (ass1 v) u.

Notation "u /ₜ v" := (t_subst1 u v) (at level 50, left associativity).
Notation "u /ᵥ v" := (v_subst1 u v) (at level 50, left associativity).
Notation "u /ₛ v" := (s_subst1 u v) (at level 50, left associativity).

Variant nf (Γ : t_ctx) : Type :=
| NF {x} : Γ ∋ x -> val Γ (t_neg x) -> nf Γ .
Arguments NF {Γ x}.

Equations eval_aux {Γ} : state Γ -> (state Γ + nf Γ) :=
  eval_aux (Cut (Mu c) k) := inl (c /ₛ k) ;
  eval_aux (Cut (Val v) (Mu' c)) := inl (c /ₛ v) ;
  eval_aux (Cut (Val v) (VarN i)) := inr (NF i v) ;
  eval_aux (Cut (Val (VarP i)) k) := inr (NF i k) ;

  eval_aux (Cut (Val (LamRec u)) (App v k)) := inl (Cut (u /ₜ v0_shift _ v /ₜ LamRec u) k) ;
  eval_aux (Cut (Val (Pair u v)) (Fst k)) := inl (Cut u k) ;
  eval_aux (Cut (Val (Pair u v)) (Snd k)) := inl (Cut v k) ;
  eval_aux (Cut (Val (Inl u)) (Match c1 c2)) := inl (c1 /ₛ u) ;
  eval_aux (Cut (Val (Inr u)) (Match c1 c2)) := inl (c2 /ₛ u) .

Definition eval {Γ} : state Γ -> delay (nf Γ) := iter_delay (fun c => Ret' (eval_aux c)).
