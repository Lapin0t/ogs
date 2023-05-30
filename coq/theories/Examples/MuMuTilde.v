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

Definition t_ctx : Type := Ctx.ctx ty.
Bind Scope ctx_scope with t_ctx.

Variant cut (F : t_ctx -> ty -> Type) (Γ : t_ctx) : Type :=
| Cut {a} (focus : F Γ (t+ a)) (cont : F Γ (t- a)).
Arguments Cut {F Γ a}.

Inductive term : t_ctx -> ty -> Type :=
(* variables *)
| Var {Γ a} : Γ ∋ a -> term Γ a

(* terms *)
| Mu {Γ a} : cut term (Γ ▶ t- a) -> term Γ (t+ a)
| OneI {Γ} : term Γ (t+ One)
| LamRec {Γ a b} : term (Γ ▶ t+ (a → b) ▶ t+ a) (t+ b) -> term Γ (t+ (a → b))
| Pair {Γ a b} : term Γ (t+ a) -> term Γ (t+ b) -> term Γ (t+ (a × b))
| Inl {Γ a b} : term Γ (t+ a) -> term Γ (t+ (a + b))
| Inr {Γ a b} : term Γ (t+ b) -> term Γ (t+ (a + b))

(* co-terms *)
| Mu' {Γ a} : cut term (Γ ▶ t+ a) -> term Γ (t- a)
| ZerK {Γ} : term Γ (t- Zer)
| App {Γ a b} : term Γ (t+ a) -> term Γ (t- b) -> term Γ (t- (a → b))
| Fst {Γ a b} : term Γ (t- a) -> term Γ (t- (a × b))
| Snd {Γ a b} : term Γ (t- b) -> term Γ (t- (a × b))
| Match {Γ a b} : cut term (Γ ▶ t+ a) -> cut term (Γ ▶ t+ b) -> term Γ (t- (a + b))
.

Notation state := (cut term).
Notation "term+ Γ a" := (term Γ (t+ a)) (at level 30).
Notation "term- Γ a" := (term Γ (t- a)) (at level 30).

Equations t_rename_aux {Γ Δ} (ts : t_ctx) (f : Γ ⊆ Δ)
  : term (Γ +▶ ts) ⇒ᵢ term (Δ +▶ ts) :=
  t_rename_aux ts f _ (Var i)       := Var (r_shift_n ts f _ i) ;
  t_rename_aux ts f _ (Mu (Cut u k)) := Mu (Cut (t_rename_aux (ts ▶ _) f _ u)
                                              (t_rename_aux (ts ▶ _) f _ k)) ;
  t_rename_aux ts f _ (OneI)        := OneI ;
  t_rename_aux ts f _ (LamRec u)    := LamRec (t_rename_aux (ts ▶ _ ▶ _) f _ u) ;
  t_rename_aux ts f _ (Pair u v)    := Pair (t_rename_aux ts f _ u) (t_rename_aux ts f _ v) ;
  t_rename_aux ts f _ (Inl u)       := Inl (t_rename_aux ts f _ u) ;
  t_rename_aux ts f _ (Inr u)       := Inr (t_rename_aux ts f _ u) ;
  t_rename_aux ts f _ (Mu' (Cut u k)) := Mu' (Cut (t_rename_aux (ts ▶ _) f _ u)
                                                (t_rename_aux (ts ▶ _) f _ k)) ;
  t_rename_aux ts f _ (ZerK)        := ZerK ;
  t_rename_aux ts f _ (App u k)     := App (t_rename_aux ts f _ u) (t_rename_aux ts f _ k) ;
  t_rename_aux ts f _ (Fst k)       := Fst (t_rename_aux ts f _ k) ;
  t_rename_aux ts f _ (Snd k)       := Snd (t_rename_aux ts f _ k) ;
  t_rename_aux ts f _ (Match (Cut u1 k1) (Cut u2 k2)) :=
    Match (Cut (t_rename_aux (ts ▶ _) f _ u1) (t_rename_aux (ts ▶ _) f _ k1))
          (Cut (t_rename_aux (ts ▶ _) f _ u2) (t_rename_aux (ts ▶ _) f _ k2)) .

Definition t_rename {Γ Δ} (f : Γ ⊆ Δ) := @t_rename_aux Γ Δ ∅ f.

Equations t_rename_c {Γ Δ} (f : Γ ⊆ Δ) : state Γ -> state Δ :=
  t_rename_c f (Cut u k) := Cut (t_rename f _ u) (t_rename f _ k) .

Definition t_shift {Γ} [y x] : term Γ x -> term (Γ ▶ y) x :=
  @t_rename _ _ s_pop _.

Equations s_shift_n {Γ Δ} (ts : t_ctx) (f : Γ =[term]> Δ)
          : (Γ +▶ ts) =[term]> (Δ +▶ ts) :=
  s_shift_n ts f _ i with cat_split i :=
    { | CLeftV j := t_rename r_concat_l _ (f _ j) ;
      | CRightV j := Var (r_concat_r _ j) } .

Equations t_subst_aux {Γ Δ} (ts : t_ctx) (f : Γ =[term]> Δ)
  : term (Γ +▶ ts) ⇒ᵢ term (Δ +▶ ts) :=
  t_subst_aux ts f _ (Var i)       := s_shift_n ts f _ i ;
  t_subst_aux ts f _ (Mu (Cut u k)) := Mu (Cut (t_subst_aux (ts ▶ _) f _ u)
                                             (t_subst_aux (ts ▶ _) f _ k)) ;
  t_subst_aux ts f _ (OneI)        := OneI ;
  t_subst_aux ts f _ (LamRec u)    := LamRec (t_subst_aux (ts ▶ _ ▶ _) f _ u) ;
  t_subst_aux ts f _ (Pair u v)    := Pair (t_subst_aux ts f _ u) (t_subst_aux ts f _ v) ;
  t_subst_aux ts f _ (Inl u)       := Inl (t_subst_aux ts f _ u) ;
  t_subst_aux ts f _ (Inr u)       := Inr (t_subst_aux ts f _ u) ;
  t_subst_aux ts f _ (Mu' (Cut u k)) := Mu' (Cut (t_subst_aux (ts ▶ _) f _ u)
                                               (t_subst_aux (ts ▶ _) f _ k)) ;
  t_subst_aux ts f _ (ZerK)        := ZerK ;
  t_subst_aux ts f _ (App u k)     := App (t_subst_aux ts f _ u) (t_subst_aux ts f _ k) ;
  t_subst_aux ts f _ (Fst k)       := Fst (t_subst_aux ts f _ k) ;
  t_subst_aux ts f _ (Snd k)       := Snd (t_subst_aux ts f _ k) ;
  t_subst_aux ts f _ (Match (Cut u1 k1) (Cut u2 k2)) :=
    Match (Cut (t_subst_aux (ts ▶ _) f _ u1) (t_subst_aux (ts ▶ _) f _ k1))
          (Cut (t_subst_aux (ts ▶ _) f _ u2) (t_subst_aux (ts ▶ _) f _ k2)) .

Definition t_subst {Γ Δ} (f : Γ =[term]> Δ) := @t_subst_aux Γ Δ ∅ f.

Definition t_subst1 {Γ a b} (u : term (Γ ▶ a) b) (v : term Γ a) : term Γ b :=
  t_subst (s_append (@Var _) v) _ u .

Notation "u /ₛ v" := (t_subst1 u v) (at level 50, left associativity).

Inductive val : t_ctx -> ty -> Type :=
| VVar {Γ a} : Γ ∋ (t+ a) -> val Γ (t+ a)

| VOneI {Γ} : val Γ (t+ One)
| VInl {Γ a b} : val Γ (t+ a) -> val Γ (t+ (a + b))
| VInr {Γ a b} : val Γ (t+ b) -> val Γ (t+ (a + b))

| VLamRec {Γ a b} : term (Γ ▶ t+ (a → b) ▶ t+ a) (t+ b) -> val Γ (t+ (a → b))
| VPair {Γ a b} : term Γ (t+ a) -> term Γ (t+ b) -> val Γ (t+ (a × b))

| VKont {Γ a} : term Γ (t- a) -> val Γ (t- a)
.

Equations vvar' {Γ} : has Γ ⇒ᵢ val Γ :=
  vvar' (t+ _) i := VVar i ;
  vvar' (t- _) i := VKont (Var i) .

Equations t_of_val {Γ} : val Γ ⇒ᵢ term Γ :=
  t_of_val _ (VVar i)    := Var i ;
  t_of_val _ (VOneI)     := OneI ;
  t_of_val _ (VInl u)    := Inl (t_of_val _ u) ;
  t_of_val _ (VInr u)    := Inr (t_of_val _ u) ;
  t_of_val _ (VLamRec u) := LamRec u ;
  t_of_val _ (VPair u v) := Pair u v ;
  t_of_val _ (VKont k)   := k .

Equations v_rename_aux {Γ Δ} ts (f : Γ ⊆ Δ) : val (Γ +▶ ts) ⇒ᵢ val (Δ +▶ ts) :=
  v_rename_aux ts f _ (VVar i)    := VVar (r_shift_n ts f _ i) ;
  v_rename_aux ts f _ (VOneI)     := VOneI ;
  v_rename_aux ts f _ (VInl u)    := VInl (v_rename_aux ts f _ u) ;
  v_rename_aux ts f _ (VInr u)    := VInr (v_rename_aux ts f _ u) ;
  v_rename_aux ts f _ (VLamRec u) := VLamRec (t_rename_aux (ts ▶ _ ▶ _) f _ u) ;
  v_rename_aux ts f _ (VPair u v) := VPair (t_rename_aux ts f _ u) (t_rename_aux ts f _ v) ;
  v_rename_aux ts f _ (VKont k)   := VKont (t_rename_aux ts f _ k) .

Definition v_rename {Γ Δ} (f : Γ ⊆ Δ) := @v_rename_aux Γ Δ ∅ f.

Definition v_shift {Γ} [y] : val Γ ⇒ᵢ val (Γ ▶ y) :=
  @v_rename _ _ s_pop.

Equations v_shift_n {Γ Δ} (ts : t_ctx) (f : Γ =[val]> Δ)
          : (Γ +▶ ts) =[val]> (Δ +▶ ts) :=
  v_shift_n ts f _ i with cat_split i :=
    { | CLeftV j := v_rename r_concat_l _ (f _ j) ;
      | CRightV j := vvar' _ (r_concat_r _ j) } .

Definition s_t_of_val {Γ Δ} : Γ =[val]> Δ -> Γ =[ term ]> Δ := s_map t_of_val.  

Equations v_subst_aux {Γ Δ} ts (f : Γ =[val]> Δ) : val (Γ +▶ ts) ⇒ᵢ val (Δ +▶ ts) :=
  v_subst_aux ts f _ (VVar i)    := v_shift_n ts f _ i ;
  v_subst_aux ts f _ (VOneI)     := VOneI ;
  v_subst_aux ts f _ (VInl u)    := VInl (v_subst_aux ts f _ u) ;
  v_subst_aux ts f _ (VInr u)    := VInr (v_subst_aux ts f _ u) ;
  v_subst_aux ts f _ (VLamRec u) := VLamRec (t_subst_aux (ts ▶ _ ▶ _) (s_t_of_val f) _ u) ;
  v_subst_aux ts f _ (VPair u v) := VPair (t_subst_aux ts (s_t_of_val f) _ u) (t_subst_aux ts (s_t_of_val f) _ v) ;
  v_subst_aux ts f _ (VKont k)   := VKont (t_subst_aux ts (s_t_of_val f) _ k) .

Definition v_subst {Γ Δ} (f : Γ =[val]> Δ) := @v_subst_aux Γ Δ ∅ f.

Variant whnf (Γ : t_ctx) : Type :=
| NVal {x} : val Γ (t+ x) -> has Γ (t- x) -> whnf Γ
| NRed {x} : has Γ (t+ x) -> term Γ (t- x) -> whnf Γ
.
Arguments NVal {Γ x}.
Arguments NRed {Γ x}.

Equations eval_aux {Γ} : state Γ -> (state Γ + whnf Γ) :=
  eval_aux (Cut (Var i) k) := inr (NRed i k) ;
  eval_aux (Cut (Mu (Cut u k1)) k) := _ ;
  eval_aux (Cut (OneI) k) := _ ;
  eval_aux (Cut (LamRec u) k) := _ ;
  eval_aux (Cut (Pair u v) k) := _ ;
  eval_aux (Cut (Inl u) k) := _ ;
  eval_aux (Cut (Inr v) k) := _ .
