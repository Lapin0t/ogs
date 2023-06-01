From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel Ctx.
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
Scheme term_mut := Induction for term Sort Prop
with val0_mut := Induction for val0 Sort Prop
with state_mut := Induction for state Sort Prop.
Check state_mut.
Check val0_mut.

Record syn_ind_args (P : forall (t : t_ctx) (t0 : ty), term t t0 -> Prop)
                    (P0 : forall (t : t_ctx) (t0 : ty0), val0 t t0 -> Prop)
                    (P1 : forall t : t_ctx, state t -> Prop) :=
  {
    ind_s_mu : forall (Γ : ctx ty) (a : ty0) (s : state (Γ ▶ t- a)), P1 (Γ ▶ t- a)%ctx s -> P Γ (t+ a) (Mu s) ;
    ind_s_val : forall (Γ : t_ctx) (a : ty0) (v : val0 Γ a), P0 Γ a v -> P Γ (t+ a) (Val v) ;
    ind_s_varn : forall (Γ : ctx ty) (a : ty0) (h : Γ ∋ t- a), P Γ (t- a) (VarN h) ;
    ind_s_mu' : forall (Γ : ctx ty) (a : ty0) (s : state (Γ ▶ t+ a)), P1 (Γ ▶ t+ a)%ctx s -> P Γ (t- a) (Mu' s) ;
    ind_s_zer : forall Γ : t_ctx, P Γ (t- Zer) ZerK ;
    ind_s_app : forall (Γ : t_ctx) (a b : ty0) (v : val0 Γ a),
        P0 Γ a v -> forall t : term Γ (t- b), P Γ (t- b) t -> P Γ (t- (a → b)) (App v t) ;
    ind_s_fst : forall (Γ : t_ctx) (a b : ty0) (t : term Γ (t- a)),
        P Γ (t- a) t -> P Γ (t- (a × b)) (Fst t) ;
    ind_s_snd : forall (Γ : t_ctx) (a b : ty0) (t : term Γ (t- b)),
        P Γ (t- b) t -> P Γ (t- (a × b)) (Snd t) ;
    ind_s_match : forall (Γ : ctx ty) (a b : ty0) (s : state (Γ ▶ t+ a)),
        P1 (Γ ▶ t+ a)%ctx s ->
        forall s0 : state (Γ ▶ t+ b),
        P1 (Γ ▶ t+ b)%ctx s0 -> P Γ (t- (a + b)) (Match s s0) ;
    ind_s_varp : forall (Γ : ctx ty) (a : ty0) (h : Γ ∋ t+ a), P0 Γ a (VarP h) ;
    ind_s_inl : forall (Γ : t_ctx) (a b : ty0) (v : val0 Γ a), P0 Γ a v -> P0 Γ (a + b) (Inl v) ;
    ind_s_inr : forall (Γ : t_ctx) (a b : ty0) (v : val0 Γ b), P0 Γ b v -> P0 Γ (a + b) (Inr v) ;
    ind_s_onei : forall Γ : t_ctx, P0 Γ One OneI ;
    ind_s_lam : forall (Γ : ctx ty) (a b : ty0) (t : term (Γ ▶ t+ (a → b) ▶ t+ a) (t+ b)),
        P (Γ ▶ t+ (a → b) ▶ t+ a)%ctx (t+ b) t -> P0 Γ (a → b) (LamRec t) ;
    ind_s_pair : forall (Γ : t_ctx) (a b : ty0) (t : term Γ (t+ a)),
        P Γ (t+ a) t ->
        forall t0 : term Γ (t+ b), P Γ (t+ b) t0 -> P0 Γ (a × b) (Pair t t0) ;
    ind_s_cut : forall (Γ : t_ctx) (a : ty0) (t : term Γ (t+ a)),
      P Γ (t+ a) t -> forall t0 : term Γ (t- a), P Γ (t- a) t0 -> P1 Γ (Cut t t0)
} .

Lemma term_ind_mut P0 P1 P2 (arg : syn_ind_args P0 P1 P2)
                   (t : t_ctx) (t0 : ty) (x : term t t0) : P0 t t0 x .
  destruct arg; now apply (term_mut P0 P1 P2).
Qed.

Lemma val0_ind_mut P0 P1 P2 (arg : syn_ind_args P0 P1 P2)
                   (t : t_ctx) (t0 : ty0) (x : val0 t t0) : P1 t t0 x .
  destruct arg; now apply (val0_mut P0 P1 P2).
Qed.

Lemma state_ind_mut P0 P1 P2 (arg : syn_ind_args P0 P1 P2)
                   (t : t_ctx) (x : state t) : P2 t x .
  destruct arg; now apply (state_mut P0 P1 P2).
Qed.

Equations val : t_ctx -> ty -> Type :=
  val Γ (t+ a) := val0 Γ a ;
  val Γ (t- a) := term Γ (t- a) .

Equations t_rename {Γ Δ} : Γ ⊆ Δ -> term Γ ⇒ᵢ term Δ :=
  t_rename f _ (Mu c)    := Mu (s_rename (r_shift f) c) ;
  t_rename f _ (Val v)   := Val (v0_rename f _ v) ;
  t_rename f _ (VarN i)  := VarN (f _ i) ;
  t_rename f _ (Mu' c)   := Mu' (s_rename (r_shift f) c) ;
  t_rename f _ (ZerK)    := ZerK ;
  t_rename f _ (App u k) := App (v0_rename f _ u) (t_rename f _ k) ;
  t_rename f _ (Fst k)   := Fst (t_rename f _ k) ;
  t_rename f _ (Snd k)   := Snd (t_rename f _ k) ;
  t_rename f _ (Match c1 c2) :=
    Match (s_rename (r_shift f) c1)
          (s_rename (r_shift f) c2)
with v0_rename {Γ Δ} : Γ ⊆ Δ -> val0 Γ ⇒ᵢ val0 Δ :=
  v0_rename f _ (VarP i)   := VarP (f _ i) ;
  v0_rename f _ (OneI)     := OneI ;
  v0_rename f _ (LamRec u) := LamRec (t_rename (r_shift2 f) _ u) ;
  v0_rename f _ (Pair u v) := Pair (t_rename f _ u) (t_rename f _ v) ;
  v0_rename f _ (Inl u)    := Inl (v0_rename f _ u) ;
  v0_rename f _ (Inr u)    := Inr (v0_rename f _ u)
with s_rename {Γ Δ} : Γ ⊆ Δ -> state Γ -> state Δ :=
   s_rename f (Cut v k) := Cut (t_rename f _ v) (t_rename f _ k) .

Equations v_rename {Γ Δ} : Γ ⊆ Δ -> val Γ ⇒ᵢ val Δ :=
  v_rename f (t+ _) v := v0_rename f _ v ;
  v_rename f (t- _) k := t_rename f _ k .

Equations Var {Γ} : has Γ ⇒ᵢ val Γ :=
  Var (t+ _) i := VarP i ;
  Var (t- _) i := VarN i .

Definition t_shift  {Γ} [y] : term Γ ⇒ᵢ term (Γ ▶ y)  := @t_rename _ _ s_pop.
Definition v0_shift {Γ} [y] : val0 Γ ⇒ᵢ val0 (Γ ▶ y)  := @v0_rename _ _ s_pop.
Definition s_shift  {Γ} [y] : state Γ -> state (Γ ▶ y) := @s_rename _ _ s_pop.
Definition v_shift  {Γ} [y] : val Γ ⇒ᵢ val (Γ ▶ y)    := @v_rename _ _ s_pop.

Definition a_shift {Γ Δ} [y] (a : Γ =[val]> Δ) : (Γ ▶ y) =[val]> (Δ ▶ y) :=
  s_append (fun _ i => v_shift _ (a _ i)) (Var _ top).

Definition a_shift2 {Γ Δ} [y z] (a : Γ =[val]> Δ) : (Γ ▶ y ▶ z) =[val]> (Δ ▶ y ▶ z) :=
  a_shift (a_shift a).

Equations t_of_v {Γ} : val Γ ⇒ᵢ term Γ :=
  t_of_v (t+ _) v := Val v ;
  t_of_v (t- _) k := k .

Equations t_subst {Γ Δ} : Γ =[val]> Δ -> term Γ ⇒ᵢ term Δ :=
  t_subst f _ (Mu c)    := Mu (s_subst (a_shift f) c) ;
  t_subst f _ (Val v)   := Val (v0_subst f _ v) ;
  t_subst f _ (VarN i)  := f _ i ;
  t_subst f _ (Mu' c)   := Mu' (s_subst (a_shift f) c) ;
  t_subst f _ (ZerK)    := ZerK ;
  t_subst f _ (App u k) := App (v0_subst f _ u) (t_subst f _ k) ;
  t_subst f _ (Fst k)   := Fst (t_subst f _ k) ;
  t_subst f _ (Snd k)   := Snd (t_subst f _ k) ;
  t_subst f _ (Match c1 c2) :=
    Match (s_subst (a_shift f) c1)
          (s_subst (a_shift f) c2)
with v0_subst {Γ Δ} : Γ =[val]> Δ -> val0 Γ ⇒ᵢ val0 Δ :=
  v0_subst f _ (VarP i)   := f _ i ;
  v0_subst f _ (OneI)     := OneI ;
  v0_subst f _ (LamRec u) := LamRec (t_subst (a_shift2 f) _ u) ;
  v0_subst f _ (Pair u v) := Pair (t_subst f _ u) (t_subst f _ v) ;
  v0_subst f _ (Inl u)    := Inl (v0_subst f _ u) ;
  v0_subst f _ (Inr u)    := Inr (v0_subst f _ u)
with s_subst {Γ Δ} : Γ =[val]> Δ -> state Γ -> state Δ :=
   s_subst f (Cut v k) := Cut (t_subst f _ v) (t_subst f _ k) .

Equations v_subst {Γ Δ} : Γ =[val]> Δ -> val Γ ⇒ᵢ val Δ :=
  v_subst f (t+ _) v := v0_subst f _ v ;
  v_subst f (t- _) k := t_subst f _ k .

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

Equations f0_subst {Γ Δ} : Γ =[val]> Δ -> forcing0 Γ ⇒ᵢ forcing0 Δ :=
  f0_subst f a (FZerK)        := FZerK ;
  f0_subst f a (FApp v k)     := FApp (v0_subst f _ v) (t_subst f _ k) ;
  f0_subst f a (FFst k)       := FFst (t_subst f _ k) ;
  f0_subst f a (FSnd k)       := FSnd (t_subst f _ k) ;
  f0_subst f a (FMatch s1 s2) := FMatch (s_subst (a_shift f) s1) (s_subst (a_shift f) s2) .

Equations forcing : t_ctx -> ty -> Type :=
  forcing Γ (t+ a) := val0 Γ a ;
  forcing Γ (t- a) := forcing0 Γ a .

Equations f_subst {Γ Δ} : Γ =[val]> Δ -> forcing Γ ⇒ᵢ forcing Δ :=
  f_subst s (t+ a) v := v0_subst s a v ;
  f_subst s (t- a) f := f0_subst s a f .

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
  := fmap_delay (fun n => (p_of_nf n ,' p_dom_of_nf n)) (eval c).

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

Definition a_comp {Γ1 Γ2 Γ3} : Γ2 =[val]> Γ3 -> Γ1 =[val]> Γ2 -> Γ1 =[val]> Γ3 :=
  fun f g _ i => v_subst f _ (g _ i) .

(*
Definition s_subst_aux_assoc {Γ1 Γ2 Γ3}
  (f : Γ2 =[val]> Γ3) (g : Γ1 =[val]> Γ2)
  ts (x : state (Γ1 +▶ ts))
  : s_subst_aux ts f (s_subst_aux ts g x)
  = s_subst_aux ts (a_comp f g) x .

*)
Search "rename".

(*
Definition t_rename_aux_assoc {Γ1 Γ2 Γ3} ts (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2)
  a (t : term (Γ1 +▶ ts) a)
  : t_rename_aux ts f1 a (t_rename_aux ts f2 a t)
    = t_rename_aux ts (s_ren f1 f2) a t.
dependent induction t.
- cbn; f_equal.
  induction t.
*)
About f_equal.

Lemma f_equal2 [A B C : Type] (f : A -> B -> C) [x1 x2 : A] [y1 y2 : B]
  : x1 = x2 -> y1 = y2 -> f x1 y1 = f x2 y2.
  intros H1 H2.
  rewrite H1, H2; reflexivity.
Qed.

Axiom HOLE : forall X : Prop, X .

(* TODO: move to Utils/Ctx.v*)
Lemma r_shift_n_assoc {Γ1 Γ2 Γ3 : t_ctx} ts (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2)
  a (i : (Γ1 +▶ ts) ∋ a)
  : r_shift_n ts f1 a (r_shift_n ts f2 a i)
    = r_shift_n ts (s_ren f1 f2) a i.
  induction ts.
  - reflexivity.
  - dependent elimination i.
    + reflexivity.
    + cbn; unfold s_pop, s_ren; f_equal; apply IHts.
Qed.

Definition t_ren_proper_P Γ a (t : term Γ a) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> t_rename f1 a t = t_rename f2 a t .
Definition v0_ren_proper_P Γ a (v : val0 Γ a) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> v0_rename f1 a v = v0_rename f2 a v .
Definition s_ren_proper_P Γ (s : state Γ) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> s_rename f1 s = s_rename f2 s .
Lemma ren_proper_prf : syn_ind_args t_ren_proper_P v0_ren_proper_P s_ren_proper_P.
  econstructor.
  all: unfold t_ren_proper_P, v0_ren_proper_P, s_ren_proper_P.
  all: intros; cbn; auto; f_equal; auto; unfold r_shift2.
  all: try apply H; try apply H0; try rewrite H0; try rewrite H1; try reflexivity.
Qed.

#[global] Instance t_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> dpointwise_relation (fun a => eq ==> eq)) (@t_rename Γ Δ).
intros f1 f2 H1 a x y ->; now apply (term_ind_mut _ _ _ ren_proper_prf).
Qed.

#[global] Instance v0_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> dpointwise_relation (fun a => eq ==> eq)) (@v0_rename Γ Δ).
intros f1 f2 H1 a x y ->; now apply (val0_ind_mut _ _ _ ren_proper_prf).
Qed.

#[global] Instance s_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> eq ==> eq) (@s_rename Γ Δ).
intros f1 f2 H1 x y ->; now apply (state_ind_mut _ _ _ ren_proper_prf).
Qed.

Definition t_ren_assoc_P Γ1 a (t : term Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2),
    t_rename f1 a (t_rename f2 a t) = t_rename (s_ren f1 f2) a t.
Definition v0_ren_assoc_P Γ1 a (v : val0 Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2),
    v0_rename f1 a (v0_rename f2 a v) = v0_rename (s_ren f1 f2) a v.
Definition s_ren_assoc_P Γ1 (s : state Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2),
    s_rename f1 (s_rename f2 s) = s_rename (s_ren f1 f2) s.

Lemma ren_assoc_prf : syn_ind_args t_ren_assoc_P v0_ren_assoc_P s_ren_assoc_P.
  econstructor.
  all: unfold t_ren_assoc_P, v0_ren_assoc_P, s_ren_assoc_P.
  all: intros; cbn; (try reflexivity); f_equal; eauto; unfold r_shift2.
  all: repeat rewrite r_shift_comp; eauto.
  etransitivity.
  apply H.
  apply t_ren_eq; auto.
  rewrite 2 r_shift_comp.
  reflexivity.
Qed.

Lemma t_rename_assoc {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) a (t : term Γ1 a)
  : t_rename f1 a (t_rename f2 a t) = t_rename (s_ren f1 f2) a t.
now apply (term_ind_mut _ _ _ ren_assoc_prf). Qed.
Lemma v0_rename_assoc {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) a (v : val0 Γ1 a)
  : v0_rename f1 a (v0_rename f2 a v) = v0_rename (s_ren f1 f2) a v.
now apply (val0_ind_mut _ _ _ ren_assoc_prf). Qed.
Lemma s_rename_assoc {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) (s : state Γ1)
  : s_rename f1 (s_rename f2 s) = s_rename (s_ren f1 f2) s.
now apply (state_ind_mut _ _ _ ren_assoc_prf). Qed.

Definition t_ren_id_l_P Γ a (t : term Γ a) : Prop := t_rename r_id a t = t.
Definition v0_ren_id_l_P Γ a (v : val0 Γ a) : Prop := v0_rename r_id a v = v.
Definition s_ren_id_l_P Γ (s : state Γ) : Prop := s_rename r_id s = s.

Lemma ren_id_l_prf : syn_ind_args t_ren_id_l_P v0_ren_id_l_P s_ren_id_l_P.
  econstructor.
  all: unfold t_ren_id_l_P, v0_ren_id_l_P, s_ren_id_l_P.
  all: intros; cbn; (try reflexivity); f_equal; eauto; unfold r_shift2.
  all: try rewrite r_shift_id; eauto.
  rewrite <- H.
  apply t_ren_eq; auto.
  rewrite 2 r_shift_id; auto.
Qed.

Lemma t_ren_id_l {Γ} a (t : term Γ a) : t_rename r_id a t = t.
now apply (term_ind_mut _ _ _ ren_id_l_prf). Qed.
Lemma v0_ren_id_l {Γ} a (v : val0 Γ a) : v0_rename r_id a v = v.
now apply (val0_ind_mut _ _ _ ren_id_l_prf). Qed.
Lemma s_ren_id_l {Γ} (s : state Γ) : s_rename r_id s = s.
now apply (state_ind_mut _ _ _ ren_id_l_prf). Qed.

Lemma v_ren_id_r {Γ Δ} (f : Γ ⊆ Δ) a (i : Γ ∋ a) : v_rename f a (Var _ i) = Var _ (f _ i).
destruct a; auto. Qed.
  
Definition t_sub_proper_P Γ a (t : term Γ a) : Prop :=
  forall Δ (f1 f2 : Γ =[val]> Δ), f1 ≡ₐ f2 -> t_subst f1 a t = t_subst f2 a t .
Definition v0_sub_proper_P Γ a (v : val0 Γ a) : Prop :=
  forall Δ (f1 f2 : Γ =[val]> Δ), f1 ≡ₐ f2 -> v0_subst f1 a v = v0_subst f2 a v .
Definition s_sub_proper_P Γ (s : state Γ) : Prop :=
  forall Δ (f1 f2 : Γ =[val]> Δ), f1 ≡ₐ f2 -> s_subst f1 s = s_subst f2 s .
Lemma sub_proper_prf : syn_ind_args t_sub_proper_P v0_sub_proper_P s_sub_proper_P.
  econstructor.
  all: unfold t_sub_proper_P, v0_sub_proper_P, s_sub_proper_P.
  all: intros; cbn; auto; f_equal; auto; unfold a_shift2, a_shift.
  all: try apply H; try apply H0; try rewrite H0; try rewrite H1; try reflexivity.
  all: apply s_append_eq; auto.
  all: intros ? i; try f_equal; try rewrite H0; try rewrite H1; auto.
  apply s_append_eq; auto; intros ? i'; rewrite H0; auto.
Qed.

#[global] Instance t_sub_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> dpointwise_relation (fun a => eq ==> eq)) (@t_subst Γ Δ).
intros f1 f2 H1 a x y ->; now apply (term_ind_mut _ _ _ sub_proper_prf).
Qed.

#[global] Instance v0_sub_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> dpointwise_relation (fun a => eq ==> eq)) (@v0_subst Γ Δ).
intros f1 f2 H1 a x y ->; now apply (val0_ind_mut _ _ _ sub_proper_prf).
Qed.

#[global] Instance s_sub_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> eq ==> eq) (@s_subst Γ Δ).
intros f1 f2 H1 x y ->; now apply (state_ind_mut _ _ _ sub_proper_prf).
Qed.

(*
Definition t_sub_assoc_P Γ1 a (t : term Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2),
    t_subst f1 a (t_subst f2 a t) = t_subst (a_comp f1 f2) a t.
Definition v0_sub_assoc_P Γ1 a (v : val0 Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2),
    v0_subst f1 a (v0_subst f2 a v) = v0_subst (a_comp f1 f2) a v.
Definition s_sub_assoc_P Γ1 (s : state Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2),
    s_subst f1 (s_subst f2 s) = s_subst (a_comp f1 f2) s.

Lemma ren_assoc_prf : syn_ind_args t_ren_assoc_P v0_ren_assoc_P s_ren_assoc_P.
  econstructor.
  all: unfold t_ren_assoc_P, v0_ren_assoc_P, s_ren_assoc_P.
  all: intros; cbn; (try reflexivity); f_equal; eauto; unfold r_shift2.
  all: repeat rewrite r_shift_comp; eauto.
  etransitivity.
  apply H.
  apply t_ren_eq; auto.
  rewrite 2 r_shift_comp.
  reflexivity.
Qed.




    v0_rename f1 a (v0_rename f2 a v) = v0_rename (s_ren f1 f2) a v.
Definition s_ren_assoc_P Γ1 (s : state Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2),
    s_rename f1 (s_rename f2 s) = s_rename (s_ren f1 f2) s.
*)


From Coinduction Require Import coinduction lattice rel tactics.
From OGS.Utils Require Import Psh Rel.
From OGS.ITree Require Import ITree Eq Monad.

Definition play_split {Γ Δ : neg_ctx} (e : Γ =[val]> Δ)
  (p : { m : pat' (Δ +▶ Γ) & pat_dom' (Δ +▶ Γ) m =[val]> (Δ +▶ Γ) })
           : delay ({ m : pat' Δ & pat_dom' Δ m =[val]> Δ }).
  destruct (cat_split (fst (projT2 (projT1 p)))).
  - refine (Ret' ((_ ,' (i , snd (projT2 (projT1 p)))) ,' a_comp ([Var,e]) (projT2 p))).
  - refine (Tau' _).
    refine (play _).
    refine (s_subst _ (emb (projT1 p))).
    refine ([[Var,e], (a_comp ([Var,e]) (projT2 p))]).
Defined.


Definition clean_hyp {Γ Δ : neg_ctx} (c : state (Δ +▶ₛ Γ)) (e : Γ =[val]> Δ) :
  play (s_subst ([Var,e]) c) ≊ bind_delay' (play c) (play_split e).
  unfold play, bind_delay', iter_delay, fmap_delay, it_eq.
  rewrite fmap_bind_com.
  unfold bind.
  revert Γ c e; coinduction R CIH; intros Γ c e.
  dependent elimination c.
  unfold s_subst.
  remember ([Var,e]) as e'.
  Admitted.

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

Definition state' (Γ : ctx neg_ty) : Type := state (ctx_to_s Γ).
Definition val' (Γ : ctx neg_ty) (a : neg_ty) : Type := val (ctx_to_s Γ) a.(sub_elt).

Definition ugly_ass_1 {Γ} {x : neg_ty} (m : pat (t_neg (sub_elt x)))
          (s : pat_dom m =[ val ]> ctx_to_s Γ)
          : Spec.dom mu_spec m =[ val' ]> Γ .
  intros ? j; destruct (view_s_has_map _ _ j); exact (s _ i).
Defined.

Definition ugly_ass_2 {Γ Δ : ctx neg_ty} (s : Γ =[ val' ]> Δ)
  : ctx_to_s Γ =[ val ]> ctx_to_s Δ.
  intros ? j.
  destruct (view_has_map _ _ j); exact (s _ i).
Defined.

Definition ugly_play {Γ}
  (u : { m : pat' (ctx_to_s Γ) & pat_dom' _ m =[val]> ctx_to_s Γ })
  : {m : Spec.msg' mu_spec Γ & Spec.dom' mu_spec m =[val']> Γ }.
  destruct u as [ [ a [ i m ] ] s ].
  destruct (view_has_map sub_elt Γ i).
  unshelve refine ((x ,' (i , m)) ,' ugly_ass_1 m s).
Defined.

Definition ugly_emb Γ (m : Spec.msg' mu_spec Γ)
  : state' (Γ +▶ Spec.dom' mu_spec m).
  destruct m as [ a [ i m ]].
  unfold state'; cbn -[ctx_s_map].
  rewrite map_cat, <- ctx_s_to_ctx_eq.
  exact (emb (_ ,' (map_has _ _ i , m))).
Defined.

Program Definition mu_machine : Spec.machine mu_spec :=
  {| Spec.conf := state' ;
     Spec.val := val' ;
     Spec.eval := fun Γ c => fmap_delay ugly_play (@play (ctx_to_s Γ) c) ;
     Spec.emb := ugly_emb ;
     Spec.v_var := fun _ _ i => Var _ (map_has _ _ i) ;
     Spec.v_sub := fun _ _ a _ v => v_subst (ugly_ass_2 a) _ v ;
     Spec.c_sub := fun _ _ a s => s_subst (ugly_ass_2 a) s ;
  |}.

Lemma the_hyp {Γ Δ}
  (c : @Spec.conf _ mu_machine (Δ +▶ Γ)%ctx)
  (e : Γ =[@Spec.val _ mu_machine]> Δ)
  : @Spec.eval_sub_1 _ mu_machine Γ Δ c e ≊ @Spec.eval_sub_2 _ mu_machine Γ Δ c e.
Admitted.
