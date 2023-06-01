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

Variant forcing0 (Γ : t_ctx) : ty0 -> Type :=
| FZerK : forcing0 Γ Zer
| FApp {a b} : val0 Γ a -> term Γ (t- b) -> forcing0 Γ (a → b)
| FFst {a b} : term Γ (t- a) -> forcing0 Γ (a × b)
| FSnd {a b} : term Γ (t- b) -> forcing0 Γ (a × b)
| FMatch {a b} : state (Γ ▶ t+ a) -> state (Γ ▶ t+ b) -> forcing0 Γ (a + b)
.
Arguments FZerK {Γ}.
Arguments FApp {Γ a b}.
Arguments FFst {Γ a b}.
Arguments FSnd {Γ a b}.
Arguments FMatch {Γ a b}.

Equations forcing : t_ctx -> ty -> Type :=
  forcing Γ (t+ a) := val0 Γ a ;
  forcing Γ (t- a) := forcing0 Γ a .

Definition nf (Γ : t_ctx) : Type := { a : ty & (Γ ∋ a * forcing Γ (t_neg a))%type }.

Equations eval_aux {Γ} : state Γ -> (state Γ + nf Γ) :=
  eval_aux (Cut (Mu c) k) := inl (c /ₛ k) ;
  eval_aux (Cut (Val v) (Mu' c)) := inl (c /ₛ v) ;
  eval_aux (Cut (Val v) (VarN i)) := inr (_ ,' (i , v)) ;
  eval_aux (Cut (Val (VarP i)) (ZerK)) := inr (_ ,' (i , FZerK)) ;
  eval_aux (Cut (Val (VarP i)) (App v k)) := inr (_ ,' (i , FApp v k)) ;
  eval_aux (Cut (Val (VarP i)) (Fst k)) := inr (_ ,' (i , FFst k)) ;
  eval_aux (Cut (Val (VarP i)) (Snd k)) := inr (_ ,' (i , FSnd k)) ;
  eval_aux (Cut (Val (VarP i)) (Match c1 c2)) := inr (_ ,' (i , FMatch c1 c2)) ;

  eval_aux (Cut (Val (LamRec u)) (App v k)) := inl (Cut (u /ₜ v0_shift _ v /ₜ LamRec u) k) ;
  eval_aux (Cut (Val (Pair u v)) (Fst k)) := inl (Cut u k) ;
  eval_aux (Cut (Val (Pair u v)) (Snd k)) := inl (Cut v k) ;
  eval_aux (Cut (Val (Inl u)) (Match c1 c2)) := inl (c1 /ₛ u) ;
  eval_aux (Cut (Val (Inr u)) (Match c1 c2)) := inl (c2 /ₛ u) .

Definition eval {Γ} : state Γ -> delay (nf Γ) := iter_delay (fun c => Ret' (eval_aux c)).

Equations is_neg0 : ty0 -> SProp :=
  is_neg0 (a → b) := sUnit ;
  is_neg0 (a × b) := sUnit ;
  is_neg0 _       := sEmpty .

Equations is_neg : ty -> SProp :=
  is_neg (t+ a) := is_neg0 a ;
  is_neg (t- a) := sUnit .

Definition neg_ty : Type := sigS is_neg.
Definition neg_coe : neg_ty -> ty := sub_elt.
Global Coercion neg_coe : neg_ty >-> ty.

Definition neg_ctx : Type := ctx_s is_neg.
Definition neg_c_coe : neg_ctx -> ctx ty := sub_elt.
Global Coercion neg_c_coe : neg_ctx >-> ctx.

Bind Scope ctx_scope with neg_ctx.
Bind Scope ctx_scope with ctx.

(*
Inductive a_val : ty0 -> Type :=
| AInl {a b} : a_val a -> a_val (a + b)
| AInr {a b} : a_val b -> a_val (a + b)
| AOneI : a_val One
| ALam {a b} : a_val (a → b)
| APair {a b} : a_val (a × b)
.

Equations a_dom {t} : a_val t -> neg_ctx :=
  a_dom (AInl u) := a_dom u ;
  a_dom (AInr u) := a_dom u ;
  a_dom (AOneI) := ∅ₛ ;
  a_dom (@ALam a b) := ∅ₛ ▶ₛ {| sub_elt := t+ (a → b) ; sub_prf := stt |} ;
  a_dom (@APair a b) := ∅ₛ ▶ₛ {| sub_elt := t+ (a × b) ; sub_prf := stt |} .

Equations a_of_v0 {Γ : neg_ctx} a : val0 Γ a -> a_val a :=
  a_of_v0 (Zer)   (VarP i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  a_of_v0 (a + b) (VarP i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  a_of_v0 (a + b) (Inl v) := AInl (a_of_v0 _ v) ;
  a_of_v0 (a + b) (Inr v) := AInr (a_of_v0 _ v) ;
  a_of_v0 (One)   _ := AOneI ;
  a_of_v0 (a → b) _ := ALam ;
  a_of_v0 (a × b) _ := APair .
*)

Inductive pat : ty -> Type :=
| PInl {a b} : pat (t+ a) -> pat (t+ (a + b))
| PInr {a b} : pat (t+ b) -> pat (t+ (a + b))
| POneI : pat (t+ One)
| PLam {a b} : pat (t+ (a → b))
| PPair {a b} : pat (t+ (a × b))

| PApp {a b} : pat (t+ a) -> pat (t- (a → b))
| PFst {a b} : pat (t- (a × b))
| PSnd {a b} : pat (t- (a × b))
.

Equations pat_dom {t} : pat t -> neg_ctx :=
  pat_dom (PInl u) := pat_dom u ;
  pat_dom (PInr u) := pat_dom u ;
  pat_dom (POneI) := ∅ₛ ;
  pat_dom (@PLam a b) := ∅ₛ ▶ₛ {| sub_elt := t+ (a → b) ; sub_prf := stt |} ;
  pat_dom (@PPair a b) := ∅ₛ ▶ₛ {| sub_elt := t+ (a × b) ; sub_prf := stt |} ;
  pat_dom (@PApp a b v) := pat_dom v ▶ₛ {| sub_elt := t- b ; sub_prf := stt |} ;
  pat_dom (@PFst a b) := ∅ₛ ▶ₛ {| sub_elt := t- a ; sub_prf := stt |} ;
  pat_dom (@PSnd a b) := ∅ₛ ▶ₛ {| sub_elt := t- b ; sub_prf := stt |} .

Definition pat' (Γ : t_ctx) : Type := { a : ty & (Γ ∋ a * pat (t_neg a))%type }.
Definition pat_dom' Γ : pat' Γ -> neg_ctx := fun p => pat_dom (snd (projT2 p)).

Equations t_of_p {a} (p : pat a) : val (pat_dom p) a :=
  t_of_p (PInl u) := Inl (t_of_p u) ;
  t_of_p (PInr u) := Inr (t_of_p u) ;
  t_of_p (POneI) := OneI ;
  t_of_p (PLam) := VarP top ;
  t_of_p (PPair) := VarP top ;
  t_of_p (PApp v) := App (v_shift _ (t_of_p v)) (VarN top) ;
  t_of_p (PFst) := Fst (VarN top) ;
  t_of_p (PSnd) := Snd (VarN top) .

Equations p_of_v0 {Γ : neg_ctx} a : val0 Γ a -> pat (t+ a) :=
  p_of_v0 (Zer)   (VarP i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_of_v0 (a + b) (VarP i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_of_v0 (a + b) (Inl v) := PInl (p_of_v0 _ v) ;
  p_of_v0 (a + b) (Inr v) := PInr (p_of_v0 _ v) ;
  p_of_v0 (One)   _ := POneI ;
  p_of_v0 (a → b) _ := PLam ;
  p_of_v0 (a × b) _ := PPair .

Definition p_dom_of_v0 {Γ : neg_ctx} a (v : val0 Γ a)
           : pat_dom (p_of_v0 a v) =[val]> Γ .
  induction a.
  + dependent elimination v.
    pose(nope := (s_elt_upg h).(sub_prf)); dependent elimination nope.
  + dependent elimination v.
    pose(nope := (s_elt_upg h).(sub_prf)); dependent elimination nope.
    exact s_empty.
  + refine (s_append s_empty v).
  + dependent elimination v.
    pose(nope := (s_elt_upg h).(sub_prf)); dependent elimination nope.
    - apply IHa1.
    - apply IHa2.
  + refine (s_append s_empty v).
Defined.

Equations p_of_k0 {Γ : neg_ctx} a : is_neg0 a -> forcing0 Γ a -> pat (t- a) :=
  p_of_k0 (a → b) _ (FApp v k) := PApp (p_of_v0 _ v) ;
  p_of_k0 (a × b) _ (FFst k)   := PFst ;
  p_of_k0 (a × b) _ (FSnd k)   := PSnd .

Definition p_dom_of_k0 {Γ : neg_ctx} a (p : is_neg0 a) (k : forcing0 Γ a)
           : pat_dom (p_of_k0 a p k) =[val]> Γ .
  induction a; try inversion p; dependent elimination k.
  - exact (s_append s_empty t0).
  - exact (s_append s_empty t1).
  - exact (s_append (p_dom_of_v0 a v) (t : val _ (t- _))).
Defined.

Equations p_of_f {Γ : neg_ctx} a (_ : is_neg a) : forcing Γ (t_neg a) -> pat (t_neg a) :=
  p_of_f (t+ a) p v := p_of_k0 a p v ;
  p_of_f (t- a) _ v := p_of_v0 a v.

Equations p_dom_of_f {Γ : neg_ctx} a (p : is_neg a) (v : forcing Γ (t_neg a))
  : pat_dom (p_of_f a p v) =[val]> Γ :=
  p_dom_of_f (t+ a) p v := p_dom_of_k0 a p v ;
  p_dom_of_f (t- a) _ v := p_dom_of_v0 a v .

Definition p_of_nf {Γ : neg_ctx} : nf Γ -> pat' Γ.
  intros [ a [ i f ] ].
  refine (a ,' (i , p_of_f a (s_elt_upg i).(sub_prf) f)).
Defined.

Definition p_dom_of_nf {Γ : neg_ctx} : forall n : nf Γ, pat_dom' Γ (p_of_nf n) =[val]> Γ.
  intros [ a [ i f ] ].
  refine (p_dom_of_f a (s_elt_upg i).(sub_prf) f).
Defined.

Definition play {Γ : neg_ctx} (c : state Γ)
  : delay ({ m : pat' Γ & pat_dom' Γ m =[val]> Γ })
  := bind_delay (eval c) (fun n => Ret' (p_of_nf n ,' p_dom_of_nf n)).

Definition emb {Γ} (m : pat' Γ) : state (Γ +▶ pat_dom' Γ m) .
  destruct m as [a [i v]]; cbn in *.
  destruct a.
  - refine (Cut _ _).
    + refine (Val (VarP (r_concat_l _ i))).
    + refine (t_rename r_concat_r _ (t_of_p v)).
  - refine (Cut _ _).
    + refine (Val (v_rename r_concat_r _ (t_of_p v))).
    + refine (VarN (r_concat_l _ i)).
Defined.

From OGS.OGS Require Spec.

Definition mu_spec : Spec.interaction_spec :=
  {| Spec.typ := neg_ty ;
     Spec.msg := fun t => pat (t_neg t) ;
     Spec.dom := fun t p => ctx_s_to_ctx (pat_dom p) |}
.

Definition ctx_allS (Γ : ctx neg_ty) : allS is_neg (c_map sub_elt Γ).
  induction Γ; intros ? i; cbn in *.
  - remember ∅%ctx as Γ; destruct i; inversion HeqΓ.
  - remember (_ ▶ _)%ctx as Γ' in i; destruct i; inversion HeqΓ'.
    + exact x.(sub_prf).
    + rewrite <- H0 in IHΓ; exact (IHΓ _ i).
Defined.

Definition ctx_to_s (Γ : ctx neg_ty) : neg_ctx := {| sub_elt := c_map sub_elt Γ ; sub_prf := ctx_allS Γ |}.

Program Definition mu_machine : Spec.machine mu_spec :=
  {| Spec.conf := fun Γ => state (ctx_to_s Γ) ;
     Spec.val := fun Γ t => val (ctx_to_s Γ) t.(sub_elt) |} .
Next Obligation.
  refine (fmap_delay _ (@play (ctx_to_s Γ) X)).
  intros [ [ a [ i m ] ] s ]; cbn in *.
  destruct (view_has_map sub_elt Γ i); cbn in *.
  unshelve refine ((x ,' (i , m)) ,' _). cbn.
  intros ? j.
  destruct (view_s_has_map _ _ j); cbn in *.
  exact (s _ i0).
Defined.
Next Obligation.
  destruct m as [ a [ i m ]].
  rewrite map_cat, <- ctx_s_to_ctx_eq.
  exact (emb (_ ,' (map_has _ _ i , m))).
Defined.
Next Obligation.
  exact (Var _ (map_has _ _ X)).
Defined.
Next Obligation.
  refine (v_subst _ _ X0).
  intros ? j.
  destruct (view_has_map _ _ j); exact (X _ i0).
Defined.
Next Obligation.
  refine (s_subst _ X0).
  intros ? j.
  destruct (view_has_map _ _ j); exact (X _ i).
Defined.
