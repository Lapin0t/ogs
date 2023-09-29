From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel Ctx.
From OGS.Game Require Import Event.
From OGS.ITree Require Import ITree Eq Delay Structure Properties.
Set Equations Transparent.

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

Inductive term : t_ctx -> ty -> Type :=
| Mu {Γ a} : state (Γ ▶ t- a) -> term Γ (t+ a)
| Val {Γ a} : val0 Γ a -> term Γ (t+ a)
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

Equations Var {Γ} : has Γ ⇒ᵢ val Γ :=
  Var (t+ _) i := VarP i ;
  Var (t- _) i := VarN i .

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

Definition a_ren {Γ1 Γ2 Γ3} : Γ2 ⊆ Γ3 -> Γ1 =[val]> Γ2 -> Γ1 =[val]> Γ3 :=
  fun f g _ i => v_rename f _ (g _ i) .

Definition t_shift  {Γ} [y] : term Γ ⇒ᵢ term (Γ ▶ y)  := @t_rename _ _ s_pop.
Definition v0_shift {Γ} [y] : val0 Γ ⇒ᵢ val0 (Γ ▶ y)  := @v0_rename _ _ s_pop.
Definition s_shift  {Γ} [y] : state Γ -> state (Γ ▶ y) := @s_rename _ _ s_pop.
Definition v_shift  {Γ} [y] : val Γ ⇒ᵢ val (Γ ▶ y)    := @v_rename _ _ s_pop.

Definition a_shift {Γ Δ} [y] (a : Γ =[val]> Δ) : (Γ ▶ y) =[val]> (Δ ▶ y) :=
  s_append (fun _ i => v_shift _ (a _ i)) (Var _ top).

Definition a_shift2 {Γ Δ} [y z] (a : Γ =[val]> Δ) : (Γ ▶ y ▶ z) =[val]> (Δ ▶ y ▶ z) :=
  a_shift (a_shift a).


(*
Definition t_shift_n {Γ} ts : term Γ ⇒ᵢ term (Γ +▶ ts).
  induction ts; intros ? t; [ exact t | exact (t_shift _ (IHts _ t)) ].
Defined.

Definition v0_shift_n {Γ} ts : val0 Γ ⇒ᵢ val0 (Γ +▶ ts).
  induction ts; intros ? v; [ exact v | exact (v0_shift _ (IHts _ v)) ].
Defined.

Definition s_shift_n {Γ} ts : state Γ -> state (Γ +▶ ts).
  induction ts; intros s; [ exact s | exact (s_shift (IHts s)) ].
Defined.

Definition a_shift_n {Γ Δ} ts (a : Γ =[val]> Δ) : (Γ +▶ ts) =[val]> (Δ +▶ ts).
  induction ts; [ exact a | exact (a_shift (IHts)) ].
Defined.
*)

Equations t_of_v {Γ} : val Γ ⇒ᵢ term Γ :=
  t_of_v (t+ _) v := Val v ;
  t_of_v (t- _) k := k .

(*  μx. ⟨ inr ( λy. μz. ⟨ inl z | x ⟩ ) | x ⟩    *)
Definition LEM {a} : term ∅ (t+ (a + (a → Zer))) :=
  Mu (Cut (Val (Inr (LamRec (Mu (Cut (Val (Inl (VarP (pop top))))
                                     (VarN (pop (pop (pop top)))))))))
           (VarN top)) .

Definition App' {Γ a b} (f : term Γ (t+ (a → b))) (x : val0 Γ a) : term Γ (t+ b) :=
  Mu (Cut (t_shift _ f) (App (v_shift (t+ _) x) (VarN top))) .

(*
Definition App'' {Γ a b} (f : term Γ (t+ (a → b))) (x : term Γ (t+ a)) : state Γ .
  refine (Cut x (Mu' (Cut (t_shift _ f) (App (VarP top) _)))).
*)

(*  λ fun arg => μα.⟨ arg ∥ μ`x. ⟨ fun ∥ app x α ⟩ ⟩ *)
Definition App'' {Γ a b} (f : term Γ (t+ (a → b))) (x : term Γ (t+ a)) : term Γ (t+ b) :=
  Mu (Cut (t_shift _ x) (Mu' (Cut (t_shift _ (t_shift _ f)) (App (VarP top) (VarN (pop top)))))) .

Definition Lam' {Γ a b} (u : term (Γ ▶ t+ a) (t+ b)) : val0 Γ (a → b) :=
  LamRec (t_rename (r_shift s_pop) (t+ _) u) . 

Definition ty_nat (a : ty0) : ty0 := (a → ((a → a) → a)) .
Definition nat_ze {a} : term ∅ (t+ ty_nat a) :=
  Val (LamRec (Val (LamRec (Val (VarP (pop (pop top))))))) .
Definition nat_su {a} : term ∅ (t+ ty_nat a) :=
  Val (Lam' (Val (Lam' (App' (Val (VarP top)) (VarP (pop top)))))).

Definition nat_sum {a} : term ∅ (t+ (ty_nat a → (ty_nat a → ty_nat a))) .
  do 4 refine (Val (Lam' _)).
  refine (App' _ (VarP (top))).
  refine (App'' (Val (VarP (pop (pop (pop top))))) _).
  refine (App' _ (VarP (top))).
  refine (App' (Val (VarP (pop (pop top)))) _).
  exact (VarP (pop top)).
Defined.

(* λ f n => (f ((f n) n)) n *)
Definition example1 {a} : term ∅ (t+ ((ty_nat a → (ty_nat a → ty_nat a))
                                      → (ty_nat a → ty_nat a))) .
  do 2 refine (Val (Lam' _)).
  epose (f := Val (VarP (pop top))).
  epose (n := VarP top).
  exact (App' (App'' f (App' (App' f n) n)) n).
Defined.

(* λ f n => ((f n) ((f n) n)) *)  
Definition example2 {a} : term ∅ (t+ ((ty_nat a → (ty_nat a → ty_nat a))
                                      → (ty_nat a → ty_nat a))) .
  do 2 refine (Val (Lam' _)).
  epose (f := Val (VarP (pop top))).
  epose (n := VarP top).
  exact (App'' (App' f n) (App' (App' f n) n)) .
Defined.

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

Definition a_comp {Γ1 Γ2 Γ3} : Γ2 =[val]> Γ3 -> Γ1 =[val]> Γ2 -> Γ1 =[val]> Γ3 :=
  fun f g _ i => v_subst f _ (g _ i) .

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

Equations is_neg0 : ty0 -> SProp :=
  is_neg0 One     := sUnit ;
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
  pat_dom (POneI) := ∅ₛ ▶ₛ {| sub_elt := t+ One ; sub_prf := stt |} ;
  pat_dom (@PLam a b) := ∅ₛ ▶ₛ {| sub_elt := t+ (a → b) ; sub_prf := stt |} ;
  pat_dom (@PPair a b) := ∅ₛ ▶ₛ {| sub_elt := t+ (a × b) ; sub_prf := stt |} ;
  pat_dom (@PApp a b v) := pat_dom v ▶ₛ {| sub_elt := t- b ; sub_prf := stt |} ;
  pat_dom (@PFst a b) := ∅ₛ ▶ₛ {| sub_elt := t- a ; sub_prf := stt |} ;
  pat_dom (@PSnd a b) := ∅ₛ ▶ₛ {| sub_elt := t- b ; sub_prf := stt |} .

Definition pat' (Γ : t_ctx) : Type := { a : ty & (Γ ∋ a * pat (t_neg a))%type }.
Definition pat_dom' Γ : pat' Γ -> neg_ctx := fun p => pat_dom (snd (projT2 p)).

Equations v_of_p {a} (p : pat a) : val (pat_dom p) a :=
  v_of_p (PInl u) := Inl (v_of_p u) ;
  v_of_p (PInr u) := Inr (v_of_p u) ;
  v_of_p (POneI) := VarP top ;
  v_of_p (PLam) := VarP top ;
  v_of_p (PPair) := VarP top ;
  v_of_p (PApp v) := App (v_shift _ (v_of_p v)) (VarN top) ;
  v_of_p (PFst) := Fst (VarN top) ;
  v_of_p (PSnd) := Snd (VarN top) .

Equations p_of_v0 {Γ : neg_ctx} a : val0 Γ a -> pat (t+ a) :=
  p_of_v0 (Zer)   (VarP i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_of_v0 (a + b) (VarP i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_of_v0 (a + b) (Inl v) := PInl (p_of_v0 _ v) ;
  p_of_v0 (a + b) (Inr v) := PInr (p_of_v0 _ v) ;
  p_of_v0 (One)   _ := POneI ;
  p_of_v0 (a → b) _ := PLam ;
  p_of_v0 (a × b) _ := PPair .

Equations p_dom_of_v0 {Γ : neg_ctx} a (v : val0 Γ a) : pat_dom (p_of_v0 a v) =[val]> Γ :=
  p_dom_of_v0 (Zer)   (VarP i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_dom_of_v0 (a + b) (VarP i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_dom_of_v0 (a + b) (Inl v) := p_dom_of_v0 a v ;
  p_dom_of_v0 (a + b) (Inr v) := p_dom_of_v0 b v ;
  p_dom_of_v0 (One)    v := s_append s_empty v ;
  p_dom_of_v0 (a → b) v := s_append s_empty v ;
  p_dom_of_v0 (a × b)  v := s_append s_empty v .

Definition nf0 (Γ : neg_ctx) (a : ty) : Type := { p : pat (t_neg a) & pat_dom p =[val]> Γ } .
Definition nf (Γ : neg_ctx) : Type := { a : ty & (Γ ∋ a * nf0 Γ a)%type } .

Definition n_rename {Γ Δ : neg_ctx} : Γ ⊆ Δ -> nf Γ -> nf Δ :=
  fun r u => (projT1 u ,' (r _ (fst (projT2 u)) , (projT1 (snd (projT2 u)) ,' a_ren r (projT2 (snd (projT2 u)))))) . 

Definition nf0_eq {Γ a} : relation (nf0 Γ a) :=
  fun a b => exists H : projT1 a = projT1 b, rew H in projT2 a ≡ₐ projT2 b .

Definition nf_eq {Γ} : relation (nf Γ) :=
  fun a b => exists H : projT1 a = projT1 b,
      (rew H in fst (projT2 a) = fst (projT2 b)) /\ (nf0_eq (rew H in snd (projT2 a)) (snd (projT2 b))).

#[global] Instance nf0_eq_rfl {Γ t} : Reflexive (@nf0_eq Γ t) .
  intros [ m a ]; unshelve econstructor; auto.
Qed.

#[global] Instance nf0_eq_sym {Γ t} : Symmetric (@nf0_eq Γ t) .
  intros [ m1 a1 ] [ m2 a2 ] [ p q ]; unshelve econstructor; cbn in *.
  - now symmetry.
  - revert a1 q ; rewrite p; intros a1 q.
    now symmetry.
Qed.

#[global] Instance nf0_eq_tra {Γ t} : Transitive (@nf0_eq Γ t) .
  intros [ m1 a1 ] [ m2 a2 ] [ m3 a3 ] [ p1 q1 ] [ p2 q2 ]; unshelve econstructor; cbn in *.
  - now transitivity m2.
  - transitivity (rew [fun p : pat (t_neg t) => pat_dom p =[ val ]> Γ] p2 in a2); auto.
    now rewrite <- p2.
Qed.

#[global] Instance nf_eq_rfl {Γ} : Reflexiveᵢ (fun _ : T1 => @nf_eq Γ) .
  intros _ [ x [ i n ] ].
  unshelve econstructor; auto.
Qed.

#[global] Instance nf_eq_sym {Γ} : Symmetricᵢ (fun _ : T1 => @nf_eq Γ) .
  intros _ [ x1 [ i1 n1 ] ] [ x2 [ i2 n2 ] ] [ p [ q1 q2 ] ].
  unshelve econstructor; [ | split ]; cbn in *.
  - now symmetry.
  - revert i1 q1; rewrite p; intros i1 q1; now symmetry.
  - revert n1 q2; rewrite p; intros n1 q2; now symmetry.
Qed.

#[global] Instance nf_eq_tra {Γ} : Transitiveᵢ (fun _ : T1 => @nf_eq Γ) .
  intros _ [ x1 [ i1 n1 ] ] [ x2 [ i2 n2 ] ] [ x3 [ i3 n3 ] ] [ p1 [ q1 r1 ] ] [ p2 [ q2 r2 ] ].
  unshelve econstructor; [ | split ]; cbn in *.
  - now transitivity x2.
  - transitivity (rew [has Γ] p2 in i2); auto.
    now rewrite <- p2.
  - transitivity (rew [nf0 Γ] p2 in n2); auto.
    now rewrite <- p2.
Qed.

Definition comp_eq {Γ} : relation (delay (nf Γ)) :=
  it_eq (fun _ : T1 => nf_eq) (i := T1_0) .
Notation "u ≋ v" := (comp_eq u v) (at level 40) .

Definition pat_of_nf : nf ⇒ᵢ pat' :=
  fun Γ u => (projT1 u ,' (fst (projT2 u) , projT1 (snd (projT2 u)))) .

(*
Definition pat_eq (Γ : neg_ctx) : relation (pat' Γ) :=
    fun v1 v2 => exists p : projT1 v1 = projT1 v2 , rew p in projT2 v1 = projT2 v2 .
#[global] Instance pat_eq_rfl {Γ} : Reflexiveᵢ (fun _ : T1 => pat_eq Γ) .
  intros _ v1; unshelve econstructor; auto.
Qed.

#[global] Instance pat_eq_tra {Γ} : Transitiveᵢ (fun _ : T1 => pat_eq Γ) .
  intros _ [ a1 p1 ] [ a2 p2 ] [ a3 p3 ] [ H1 H2 ] [ H3 H4 ]; cbn in *.
  destruct H1; cbn in H2.
  destruct H3; cbn in H4.
  unshelve econstructor; auto.
  now transitivity p2.
Qed.

#[global] Instance pat_eq_sym {Γ} : Symmetricᵢ (fun _ : T1 => pat_eq Γ) .
  intros _ [ a1 p1 ] [ a2 p2 ] [ H1 H2 ]; cbn in *.
  destruct H1; cbn in H2.
  unshelve econstructor; auto.
Qed.
*)

(*Definition pre_redex (Γ : neg_ctx) : Type := { x : ty & val Γ x * pat x }%type.*)

Equations eval_aux {Γ : neg_ctx} : state Γ -> (state Γ + nf Γ) :=
  eval_aux (Cut (Mu c)           (k))     := inl (c /ₛ k) ;
  eval_aux (Cut (Val v)          (Mu' c)) := inl (c /ₛ v) ;

  eval_aux (Cut (Val v)          (VarN i)) :=
    inr (_ ,' (i , (p_of_v0 _ v ,' p_dom_of_v0 _ v))) ;

  eval_aux (Cut (Val (VarP i))   (ZerK))
    with (s_elt_upg i).(sub_prf) := { | (!) } ;

  eval_aux (Cut (Val (VarP i))   (App v k)) :=
    inr (_ ,' (i , (PApp (p_of_v0 _ v) ,'
         s_append (p_dom_of_v0 _ v) (k : val _ (t- _))))) ;

  eval_aux (Cut (Val (VarP i))   (Fst k)) :=
    inr (_ ,' (i , (PFst ,' s_append s_empty k))) ;

  eval_aux (Cut (Val (VarP i))   (Snd k)) :=
    inr (_ ,' (i , (PSnd ,' s_append s_empty k))) ;

  eval_aux (Cut (Val (VarP i))   (Match c1 c2))
    with (s_elt_upg i).(sub_prf) := { | (!) } ;

  eval_aux (Cut (Val (LamRec u)) (App v k))     := inl (Cut (u /ₜ v0_shift _ v /ₜ LamRec u) k) ;
  eval_aux (Cut (Val (Pair u v)) (Fst k))       := inl (Cut u k) ;
  eval_aux (Cut (Val (Pair u v)) (Snd k))       := inl (Cut v k) ;
  eval_aux (Cut (Val (Inl u))    (Match c1 c2)) := inl (c1 /ₛ u) ;
  eval_aux (Cut (Val (Inr u))    (Match c1 c2)) := inl (c2 /ₛ u) .

Definition eval {Γ : neg_ctx} : state Γ -> delay (nf Γ)
  := iter_delay (fun c => Ret' (eval_aux c)).
Notation play := eval.

Definition Cut' {Γ a} (x : term Γ a) (y : term Γ (t_neg a)) : state Γ.
destruct a.
- exact (Cut x y).
- exact (Cut y x).
Defined.

(*
Definition p_app {Γ : neg_ctx} {a} (v : val Γ a) (m : pat (t_neg a)) : state (Γ +▶ pat_dom m) .
  eapply Cut'.
  - apply t_of_v.
    exact (v_rename r_concat_l _ v).
  destruct a; cbn in m.
  - refine (eval_aux (Cut _ _)).
    + refine (Val (v0_rename r_concat_l _ v)).
    + refine (t_rename r_concat_r _ (v_of_p m)).
  - refine (eval_aux (Cut _ _)).
    + refine (Val (v0_rename r_concat_r _ (v_of_p m))).
    + refine (t_of_v _ (v_rename r_concat_l _ v)).
Defined.
*)

Definition refold {Γ : neg_ctx} (p : nf Γ)
  : (Γ ∋ (projT1 p) * val Γ (t_neg (projT1 p)))%type.
destruct p as [x [i [ p s ]]]; cbn in *.
exact (i , v_subst s _ (v_of_p p)).
Defined.

Definition p_app {Γ x} (v : val Γ x) (m : pat (t_neg x)) (e : pat_dom m =[val]> Γ) : state Γ .
  destruct x; cbn in *.
  - refine (Cut (Val v) (t_of_v _ (v_subst e _ (v_of_p m)))).
  - refine (Cut (t_of_v _ (v_subst e _ (v_of_p m))) v).
Defined.

Definition emb {Γ} (m : pat' Γ) : state (Γ +▶ pat_dom' Γ m) .
  destruct m as [a [i v]]; cbn in *.
  destruct a.
  - refine (Cut _ _).
    + refine (Val (VarP (r_concat_l _ i))).
    + refine (t_rename r_concat_r _ (v_of_p v)).
  - refine (Cut _ _).
    + refine (Val (v_rename r_concat_r _ (v_of_p v))).
    + refine (VarN (r_concat_l _ i)).
Defined.

(*
Definition s_subst_aux_assoc {Γ1 Γ2 Γ3}
  (f : Γ2 =[val]> Γ3) (g : Γ1 =[val]> Γ2)
  ts (x : state (Γ1 +▶ ts))
  : s_subst_aux ts f (s_subst_aux ts g x)
  = s_subst_aux ts (a_comp f g) x .

*)

(*
Definition t_rename_aux_assoc {Γ1 Γ2 Γ3} ts (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2)
  a (t : term (Γ1 +▶ ts) a)
  : t_rename_aux ts f1 a (t_rename_aux ts f2 a t)
    = t_rename_aux ts (s_ren f1 f2) a t.
dependent induction t.
- cbn; f_equal.
  induction t.
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
*)

Scheme term_mut := Induction for term Sort Prop
  with val0_mut := Induction for val0 Sort Prop
  with state_mut := Induction for state Sort Prop.

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

Definition t_ren_proper_P Γ a (t : term Γ a) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> t_rename f1 a t = t_rename f2 a t .
Definition v0_ren_proper_P Γ a (v : val0 Γ a) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> v0_rename f1 a v = v0_rename f2 a v .
Definition s_ren_proper_P Γ (s : state Γ) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> s_rename f1 s = s_rename f2 s .
Lemma ren_proper_prf : syn_ind_args t_ren_proper_P v0_ren_proper_P s_ren_proper_P.
  econstructor.
  all: unfold t_ren_proper_P, v0_ren_proper_P, s_ren_proper_P.
  all: intros; cbn; f_equal.
  all: try apply H; try apply H0.
  all: repeat apply r_shift_eq; auto.
Qed.

#[global] Instance t_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@t_rename Γ Δ).
intros f1 f2 H1 a x y ->; now apply (term_ind_mut _ _ _ ren_proper_prf).
Qed.

#[global] Instance v0_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@v0_rename Γ Δ).
intros f1 f2 H1 a x y ->; now apply (val0_ind_mut _ _ _ ren_proper_prf).
Qed.

#[global] Instance s_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> eq ==> eq) (@s_rename Γ Δ).
intros f1 f2 H1 x y ->; now apply (state_ind_mut _ _ _ ren_proper_prf).
Qed.

#[global] Instance v_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> forall_relation (fun _ => eq ==> eq)) (@v_rename Γ Δ).
intros f1 f2 H1 [] v1 v2 H2; [ apply v0_ren_eq | apply t_ren_eq ]; auto.
Qed.

#[global] Instance a_ren_eq {Γ1 Γ2 Γ3}
  : Proper (ass_eq _ _ ==> ass_eq _ _ ==> ass_eq _ _) (@a_ren Γ1 Γ2 Γ3).
  intros r1 r2 H1 a1 a2 H2 ? i; unfold a_ren; cbn.
  apply (v_ren_eq _ _ H1), H2.
Qed.

Definition t_ren_ren_P Γ1 a (t : term Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2),
    t_rename f1 a (t_rename f2 a t) = t_rename (s_ren f1 f2) a t.
Definition v0_ren_ren_P Γ1 a (v : val0 Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2),
    v0_rename f1 a (v0_rename f2 a v) = v0_rename (s_ren f1 f2) a v.
Definition s_ren_ren_P Γ1 (s : state Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2),
    s_rename f1 (s_rename f2 s) = s_rename (s_ren f1 f2) s.

Lemma ren_ren_prf : syn_ind_args t_ren_ren_P v0_ren_ren_P s_ren_ren_P.
  econstructor.
  all: unfold t_ren_ren_P, v0_ren_ren_P, s_ren_ren_P.
  all: intros; cbn; f_equal.
  all: unfold r_shift2; repeat rewrite r_shift_comp.
  all: auto.
Qed.

Lemma t_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) a (t : term Γ1 a)
  : t_rename f1 a (t_rename f2 a t) = t_rename (s_ren f1 f2) a t.
now apply (term_ind_mut _ _ _ ren_ren_prf). Qed.
Lemma v0_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) a (v : val0 Γ1 a)
  : v0_rename f1 a (v0_rename f2 a v) = v0_rename (s_ren f1 f2) a v.
now apply (val0_ind_mut _ _ _ ren_ren_prf). Qed.
Lemma s_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) (s : state Γ1)
  : s_rename f1 (s_rename f2 s) = s_rename (s_ren f1 f2) s.
now apply (state_ind_mut _ _ _ ren_ren_prf). Qed.
Lemma v_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) a (v : val Γ1 a)
  : v_rename f1 a (v_rename f2 a v) = v_rename (s_ren f1 f2) a v.
destruct a; [ apply v0_ren_ren | apply t_ren_ren ]; auto. Qed.

Definition t_ren_id_l_P Γ a (t : term Γ a) : Prop := t_rename r_id a t = t.
Definition v0_ren_id_l_P Γ a (v : val0 Γ a) : Prop := v0_rename r_id a v = v.
Definition s_ren_id_l_P Γ (s : state Γ) : Prop := s_rename r_id s = s.

Lemma ren_id_l_prf : syn_ind_args t_ren_id_l_P v0_ren_id_l_P s_ren_id_l_P.
  econstructor.
  all: unfold t_ren_id_l_P, v0_ren_id_l_P, s_ren_id_l_P.
  all: intros; cbn; f_equal.
  all: unfold r_shift2; repeat rewrite r_shift_id.
  all: auto.
Qed.

Lemma t_ren_id_l {Γ} a (t : term Γ a) : t_rename r_id a t = t.
now apply (term_ind_mut _ _ _ ren_id_l_prf). Qed.
Lemma v0_ren_id_l {Γ} a (v : val0 Γ a) : v0_rename r_id a v = v.
now apply (val0_ind_mut _ _ _ ren_id_l_prf). Qed.
Lemma s_ren_id_l {Γ} (s : state Γ) : s_rename r_id s = s.
now apply (state_ind_mut _ _ _ ren_id_l_prf). Qed.
Lemma v_ren_id_l {Γ} a (v : val Γ a) : v_rename r_id a v = v.
destruct a; [ apply v0_ren_id_l | apply t_ren_id_l ]; auto. Qed.

Lemma v_ren_id_r {Γ Δ} (f : Γ ⊆ Δ) a (i : Γ ∋ a) : v_rename f a (Var _ i) = Var _ (f _ i).
destruct a; auto. Qed.
  
#[global] Instance a_shift_eq {Γ Δ y} : Proper (ass_eq _ _ ==> ass_eq _ _) (@a_shift Γ Δ y).
intros f1 f2 H.
apply s_append_eq; auto.
intros ? i; rewrite H; auto.
Qed.

Lemma a_shift_id {Γ a} : @a_shift Γ Γ a Var ≡ₐ Var.
intros x i; destruct x; dependent elimination i; auto.
Qed.
(*
*)

Definition t_sub_proper_P Γ a (t : term Γ a) : Prop :=
  forall Δ (f1 f2 : Γ =[val]> Δ), f1 ≡ₐ f2 -> t_subst f1 a t = t_subst f2 a t .
Definition v0_sub_proper_P Γ a (v : val0 Γ a) : Prop :=
  forall Δ (f1 f2 : Γ =[val]> Δ), f1 ≡ₐ f2 -> v0_subst f1 a v = v0_subst f2 a v .
Definition s_sub_proper_P Γ (s : state Γ) : Prop :=
  forall Δ (f1 f2 : Γ =[val]> Δ), f1 ≡ₐ f2 -> s_subst f1 s = s_subst f2 s .

Lemma sub_proper_prf : syn_ind_args t_sub_proper_P v0_sub_proper_P s_sub_proper_P.
  econstructor.
  all: unfold t_sub_proper_P, v0_sub_proper_P, s_sub_proper_P.
  all: intros; cbn; f_equal.
  all: unfold a_shift2; auto.
  all: try apply H; try apply H0.
  all: apply s_append_eq; auto.
  all: intros ? ?; try rewrite H0; try rewrite H1; auto.
  f_equal; apply s_append_eq; auto.
  intros ? ?; rewrite H0; auto.
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

#[global] Instance v_sub_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> dpointwise_relation (fun a => eq ==> eq)) (@v_subst Γ Δ).
intros f1 f2 H1 [] v1 v2 H2; [ apply v0_sub_eq | apply t_sub_eq ]; auto.
Qed.

#[global] Instance a_comp_eq {Γ1 Γ2 Γ3} : Proper (ass_eq _ _ ==> ass_eq _ _ ==> ass_eq _ _) (@a_comp Γ1 Γ2 Γ3).
  intros a b H1 c d H2.
  intros ? i.
  unfold a_comp.
  apply v_sub_eq; auto.
  apply H2.
Qed.

Definition t_ren_sub_P Γ1 a (t : term Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val]> Γ2),
    t_rename f1 a (t_subst f2 a t)
    = t_subst (a_ren f1 f2) a t .
Definition v0_ren_sub_P Γ1 a (v : val0 Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val]> Γ2),
    v0_rename f1 a (v0_subst f2 a v)
    = v0_subst (a_ren f1 f2) a v .
Definition s_ren_sub_P Γ1 (s : state Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val]> Γ2),
    s_rename f1 (s_subst f2 s)
    = s_subst (a_ren f1 f2) s .
Lemma ren_sub_prf : syn_ind_args t_ren_sub_P v0_ren_sub_P s_ren_sub_P.
  econstructor.
  all: unfold t_ren_sub_P, v0_ren_sub_P, s_ren_sub_P.
  all: intros; cbn; f_equal.
  all: auto.
  all: unfold a_shift, a_ren.
  all: etransitivity; [now (try apply H; try apply H0) |].
  all: try apply s_sub_eq; try apply t_sub_eq; auto.
  all: intros ? i; dependent elimination i; auto.
  all: cbn. unfold a_ren. unfold v_shift.
  all: destruct x0; cbn; repeat rewrite v0_ren_ren; repeat rewrite t_ren_ren; f_equal.
  unfold a_shift.
  all: dependent elimination h; cbn; repeat rewrite v0_ren_ren; repeat rewrite t_ren_ren; f_equal.
  Qed.
  
Lemma t_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val]> Γ2) a (t : term Γ1 a)
  : t_rename f1 a (t_subst f2 a t) = t_subst (a_ren f1 f2) a t.
now apply (term_ind_mut _ _ _ ren_sub_prf). Qed.
Lemma v0_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val]> Γ2) a (v : val0 Γ1 a)
  : v0_rename f1 a (v0_subst f2 a v) = v0_subst (a_ren f1 f2) a v.
now apply (val0_ind_mut _ _ _ ren_sub_prf). Qed.
Lemma s_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val]> Γ2) (s : state Γ1)
  : s_rename f1 (s_subst f2 s) = s_subst (a_ren f1 f2) s.
now apply (state_ind_mut _ _ _ ren_sub_prf). Qed.
Lemma v_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val]> Γ2) a (v : val Γ1 a)
  : v_rename f1 a (v_subst f2 a v) = v_subst (a_ren f1 f2) a v.
destruct a; [ apply v0_ren_sub | apply t_ren_sub ]; auto. Qed.
  
Lemma a_shift_ren {Γ1 Γ2 Γ3 y} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 ⊆ Γ2)
  : a_shift (y:=y) (s_ren f1 f2) ≡ₐ s_ren (a_shift f1) (r_shift f2) .
  intros ? i; dependent elimination i; auto.
Qed.

Definition t_sub_ren_P Γ1 a (t : term Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 ⊆ Γ2),
    t_subst f1 a (t_rename f2 a t)
    = t_subst (s_ren f1 f2) a t .
Definition v0_sub_ren_P Γ1 a (v : val0 Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 ⊆ Γ2),
    v0_subst f1 a (v0_rename f2 a v)
    = v0_subst (s_ren f1 f2) a v .
Definition s_sub_ren_P Γ1 (s : state Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 ⊆ Γ2),
    s_subst f1 (s_rename f2 s)
    = s_subst (s_ren f1 f2) s .

Lemma sub_ren_prf : syn_ind_args t_sub_ren_P v0_sub_ren_P s_sub_ren_P.
  econstructor.
  all: unfold t_sub_ren_P, v0_sub_ren_P, s_sub_ren_P.
  all: intros; cbn; f_equal.
  all: unfold a_shift2; repeat rewrite a_shift_ren; auto.
  etransitivity; [ apply H |]. (* missing proper? *)
  apply t_sub_eq; auto; rewrite 2 a_shift_ren; auto.
Qed.

Lemma t_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 ⊆ Γ2) a (t : term Γ1 a)
  : t_subst f1 a (t_rename f2 a t) = t_subst (s_ren f1 f2) a t.
now apply (term_ind_mut _ _ _ sub_ren_prf). Qed.
Lemma v0_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 ⊆ Γ2) a (v : val0 Γ1 a)
  : v0_subst f1 a (v0_rename f2 a v) = v0_subst (s_ren f1 f2) a v.
now apply (val0_ind_mut _ _ _ sub_ren_prf). Qed.
Lemma s_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 ⊆ Γ2) (s : state Γ1)
  : s_subst f1 (s_rename f2 s) = s_subst (s_ren f1 f2) s.
now apply (state_ind_mut _ _ _ sub_ren_prf). Qed.
Lemma v_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 ⊆ Γ2) a (v : val Γ1 a)
  : v_subst f1 a (v_rename f2 a v) = v_subst (s_ren f1 f2) a v.
destruct a; [ apply v0_sub_ren | apply t_sub_ren ]; auto. Qed.
  
Lemma v_sub_id_r {Γ Δ} (f : Γ =[val]> Δ) a (i : Γ ∋ a) : v_subst f a (Var _ i) = f _ i.
destruct a; auto. Qed.

Lemma a_shift_comp {Γ1 Γ2 Γ3 y} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2)
  : a_shift (y:=y) (a_comp f1 f2) ≡ₐ a_comp (a_shift f1) (a_shift f2) .
  intros x i; dependent elimination i; unfold a_shift, a_comp, v_shift; cbn.
  - rewrite v_sub_id_r; auto.
  - rewrite v_ren_sub, v_sub_ren; apply v_sub_eq; auto.
Qed.
    
Definition t_sub_sub_P Γ1 a (t : term Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2),
    t_subst f1 a (t_subst f2 a t) = t_subst (a_comp f1 f2) a t.
Definition v0_sub_sub_P Γ1 a (v : val0 Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2),
    v0_subst f1 a (v0_subst f2 a v) = v0_subst (a_comp f1 f2) a v.
Definition s_sub_sub_P Γ1 (s : state Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2),
    s_subst f1 (s_subst f2 s) = s_subst (a_comp f1 f2) s.

Lemma sub_sub_prf : syn_ind_args t_sub_sub_P v0_sub_sub_P s_sub_sub_P.
  econstructor.
  all: unfold t_sub_sub_P, v0_sub_sub_P, s_sub_sub_P.
  all: intros; cbn; f_equal.
  all: unfold a_shift2; repeat rewrite a_shift_comp; auto.
  etransitivity; [apply H |]. (* missing proper? *)
  apply t_sub_eq; auto.
  rewrite 2 a_shift_comp; auto.
Qed.

Lemma t_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2) a (t : term Γ1 a)
  : t_subst f1 a (t_subst f2 a t) = t_subst (a_comp f1 f2) a t.
now apply (term_ind_mut _ _ _ sub_sub_prf). Qed.
Lemma v0_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2) a (v : val0 Γ1 a)
  : v0_subst f1 a (v0_subst f2 a v) = v0_subst (a_comp f1 f2) a v.
now apply (val0_ind_mut _ _ _ sub_sub_prf). Qed.
Lemma s_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2) (s : state Γ1)
  : s_subst f1 (s_subst f2 s) = s_subst (a_comp f1 f2) s.
now apply (state_ind_mut _ _ _ sub_sub_prf). Qed.
Lemma v_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2) a (v : val Γ1 a)
  : v_subst f1 a (v_subst f2 a v) = v_subst (a_comp f1 f2) a v.
destruct a; [ apply v0_sub_sub | apply t_sub_sub ]; auto. Qed.

Lemma a_comp_assoc {Γ1 Γ2 Γ3 Γ4} (u : Γ3 =[val]> Γ4) (v : Γ2 =[val]> Γ3) (w : Γ1 =[val]> Γ2)
           : a_comp u (a_comp v w) ≡ₐ a_comp (a_comp u v) w .
  intros ? i; unfold a_comp; now apply v_sub_sub.
Qed.

Definition t_sub_id_l_P Γ a (t : term Γ a) : Prop := t_subst Var a t = t.
Definition v0_sub_id_l_P Γ a (v : val0 Γ a) : Prop := v0_subst Var a v = v.
Definition s_sub_id_l_P Γ (s : state Γ) : Prop := s_subst Var s = s.

Lemma sub_id_l_prf : syn_ind_args t_sub_id_l_P v0_sub_id_l_P s_sub_id_l_P.
  econstructor.
  all: unfold t_sub_id_l_P, v0_sub_id_l_P, s_sub_id_l_P.
  all: intros; cbn; f_equal.
  all: unfold a_shift2; repeat rewrite a_shift_id; auto.
  etransitivity; [ | exact H ]. (* missing proper? *)
  apply t_sub_eq; auto.
  rewrite 2 a_shift_id; auto.
Qed.

Lemma t_sub_id_l {Γ} a (t : term Γ a) : t_subst Var a t = t.
now apply (term_ind_mut _ _ _ sub_id_l_prf). Qed.
Lemma v0_sub_id_l {Γ} a (v : val0 Γ a) : v0_subst Var a v = v.
now apply (val0_ind_mut _ _ _ sub_id_l_prf). Qed.
Lemma s_sub_id_l {Γ} (s : state Γ) : s_subst Var s = s.
now apply (state_ind_mut _ _ _ sub_id_l_prf). Qed.
Lemma v_sub_id_l {Γ} a (v : val Γ a) : v_subst Var a v = v.
destruct a; [ apply v0_sub_id_l | apply t_sub_id_l ]; auto. Qed.

Lemma sub1_sub {Γ Δ a} (f : Γ =[val]> Δ) (v : val Γ a) :
  a_comp (ass1 (v_subst f a v)) (a_shift f) ≡ₐ a_comp f (ass1 v).
  intros ? i.
  dependent elimination i.
  - unfold a_comp; cbn; rewrite v_sub_id_r; reflexivity.
  - unfold a_comp, a_shift, v_shift; cbn.
    rewrite v_sub_ren, v_sub_id_r.
    apply v_sub_id_l.
Qed.

Lemma sub1_ren {Γ Δ a} (f : Γ ⊆ Δ) (v : val Γ a) :
  ass1 (v_rename f a v) ⊛ᵣ r_shift f ≡ₐ a_ren f (ass1 v) .
  intros ? i.
  dependent elimination i; auto.
  unfold a_ren, ass1; cbn.
  now rewrite v_ren_id_r.
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

Lemma s_sub1_sub {Γ Δ a} (f : Γ =[val]> Δ) (v : val Γ a) (s : state (Γ ▶ a))
  : s_subst (a_shift f) s /ₛ v_subst f a v = s_subst f (s /ₛ v) .
  unfold s_subst1; rewrite 2 s_sub_sub, sub1_sub; reflexivity.
Qed.

Lemma s_sub1_ren {Γ Δ a} (f : Γ ⊆ Δ) (v : val Γ a) (s : state (Γ ▶ a))
  : s_rename (r_shift f) s /ₛ v_rename f a v = s_rename f (s /ₛ v) .
  unfold s_subst1; rewrite s_sub_ren, s_ren_sub, sub1_ren; reflexivity.
Qed.

Lemma t_sub1_sub {Γ Δ a b} (f : Γ =[val]> Δ) (v : val Γ a) (t : term (Γ ▶ a) b)
  : t_subst (a_shift f) b t /ₜ v_subst f a v = t_subst f b (t /ₜ v) .
  unfold t_subst1; rewrite 2 t_sub_sub.
  apply t_sub_eq; auto.
  rewrite sub1_sub; reflexivity.
Qed.

Lemma t_sub1_run {Γ Δ a b} (f : Γ ⊆ Δ) (v : val Γ a) (t : term (Γ ▶ a) b)
  : t_rename (r_shift f) b t /ₜ v_rename f a v = t_rename f b (t /ₜ v) .
  unfold t_subst1; rewrite t_sub_ren, t_ren_sub.
  apply t_sub_eq; auto.
  now rewrite sub1_ren.
Qed.

#[global] Instance p_app_eq {Γ x} (v : val Γ x) (m : pat (t_neg x)) : Proper (ass_eq _ _ ==> eq) (p_app v m) .
  intros u1 u2 H.
  destruct x as [ x | x ]; cbn in *.
  erewrite (t_sub_eq u1 u2 H); auto.
  erewrite (v0_sub_eq u1 u2 H); auto.
Qed.


From Coinduction Require Import coinduction lattice rel tactics.
From OGS.Utils Require Import Psh Rel.
From OGS.ITree Require Import ITree Eq Structure.

(*
Definition play_split {Γ Δ : neg_ctx} (e : Γ =[val]> Δ)
  (p : { m : pat' (Δ +▶ Γ) & pat_dom' (Δ +▶ Γ) m =[val]> (Δ +▶ Γ) })
           : delay ({ m : pat' Δ & pat_dom' Δ m =[val]> Δ }).
  destruct (cat_split (fst (projT2 (projT1 p)))).
  - refine (Ret' ((_ ,' (i , snd (projT2 (projT1 p)))) ,' a_comp ([Var,e]) (projT2 p))).
  - destruct (p_app (e _ j) (snd (projT2 (projT1 p)))).
    + refine (Tau' _).
      refine (play (s_subst ([Var, (a_comp ([Var,e]) (projT2 p))]) s)).
    + refine (Ret' _).
      pose (u := @p_of_nf (Δ +▶ₛ _) n).
      pose (s := @p_dom_of_nf (Δ +▶ₛ _) n).
      unshelve refine ((projT1 u ,' (_ , _)) ,' _).
      refine (p_of_nf n ,' p_dom_of_nf n).
      refine 
    refine ([[Var,e], (a_comp ([Var,e]) (projT2 p))]).
Defined.
*)

(*
Lemma refold_lem {Γ Δ : neg_ctx} (n : nf Γ) (e : Γ =[val]> Δ) :
  Cut' (t_of_v _ (e _ i)) (t_of_v _ (v_subst e _ v)) = (s_subst (a_comp e ([ Var , projT2 n ])) (emb (projT1 n))).
*)

Lemma refold_id {Γ : neg_ctx} (a : ty0) (v : val0 Γ a)
  : v0_subst (p_dom_of_v0 a v) a (v_of_p (p_of_v0 a v)) = v.
  induction a.
  - dependent elimination v.
    pose (nope := (s_elt_upg h).(sub_prf)); dependent elimination nope.
  - reflexivity.
  - reflexivity.
  - dependent elimination v.
    pose (nope := (s_elt_upg h).(sub_prf)); dependent elimination nope.
    + exact (f_equal Inl (IHa1 v)).
    + exact (f_equal Inr (IHa2 v0)).
  - reflexivity.
Qed.

Lemma var_inj {Γ x} (i j : Γ ∋ x) (H : Var x i = Var x j) : i = j .
  destruct x; now dependent induction H.
Qed.

(*
Lemma emb_play_var {Γ : neg_ctx} {a} (p : pat (t_neg a)) (i : Γ ∋ a)
  : play (Γ:=_+▶ₛ_) (Cut' (t_of_v _ (Var _ (r_concat_l _ i))) (t_of_v _ (v_rename r_concat_r _ (v_of_p p))))
  ≊ ret_delay ((a ,' (r_concat_l _ i , p)) ,' Var ⊛ᵣ r_concat_r).
  destruct a; cbn in *.
  - dependent elimination p.
    + apply (gfp_fp (it_eq_map _ _)).
      cbn; econstructor; cbn.
      rewrite v0_ren_ren.
      eassert (H : r_shift (r_cover_r cover_cat) ⊛ᵣ s_pop ≡ₐ _).
      intros ? j. cbn.
      by reflexivity.
*)

Definition then_play1 {Γ Δ : neg_ctx} (e : Γ =[val]> Δ) (n : nf Γ) : delay (nf Δ)
  := play (p_app (e _ (fst (projT2 n))) (projT1 (snd (projT2 n))) (a_comp e (projT2 (snd (projT2 n))))) .

(*
(* the final version we would like to have in the hypothesis, in terms of [emb] *)
Definition then_play1 {Γ Δ : neg_ctx} (e : Γ =[val]> Δ) (n : nf Γ) : delay (nf Δ)
  := play (s_subst (a_comp e ([ Var , projT2 n ])) (emb (projT1 n))).
*)

(* the clean version with simplified substitutions we would like to have in the proof *)
Definition then_play2 {Γ Δ : neg_ctx} (e : Γ =[val]> Δ) (n : nf Γ) : delay (nf Δ) :=
  let '(i , v) := refold n in
  play (Cut' (t_of_v _ (e _ i)) (t_of_v _ (v_subst e _ v))).

(* both are the same thing up to substitution shenenigans *)
Lemma then_play_eq {Γ Δ : neg_ctx} (e : Γ =[val]> Δ) (n : nf Γ) : then_play1 e n ≊ then_play2 e n.
  unfold then_play1, then_play2, p_app, refold.
  destruct n as [ [] [i [ m γ ]] ]; cbn.
  - now rewrite <- t_sub_sub.
  - now rewrite <- v0_sub_sub.
Qed.
(*
    change (([Var, γ]) ?x (r_concat_l ?x ?i)) with ((([Var,γ]) ⊛ᵣ r_concat_l) x i).
    rewrite (s_eq_cat_l Var γ _ i); cbn.
    rewrite t_sub_ren; unfold a_comp, s_ren, s_map.
    change (([Var, γ]) ?x (r_concat_r ?x ?i)) with ((([Var,γ]) ⊛ᵣ r_concat_r) x i).
    change (fun x : ty => v_subst e x ∘ (([Var, γ]) ⊛ᵣ r_concat_r) x) with (a_comp e ((([Var, γ]) ⊛ᵣ r_concat_r))).
    rewrite (t_sub_eq _ _ (s_eq_cat_r _ _) _ _ _ eq_refl).
    reflexivity.
  - change (([Var, γ]) ?x (r_concat_l ?x ?i)) with ((([Var,γ]) ⊛ᵣ r_concat_l) x i).
    rewrite (s_eq_cat_l Var γ _ i); cbn.
    rewrite v0_sub_ren; unfold a_comp, s_ren, s_map.
    change (([Var, γ]) ?x (r_concat_r ?x ?i)) with ((([Var,γ]) ⊛ᵣ r_concat_r) x i).
    change (fun x : ty => v_subst e x ∘ (([Var, γ]) ⊛ᵣ r_concat_r) x) with (a_comp e (([Var, γ]) ⊛ᵣ r_concat_r)).
    rewrite <- v0_sub_sub.
    rewrite (v0_sub_eq _ _ (s_eq_cat_r _ _) _ _ _ eq_refl).
    reflexivity.
Qed.
*)

(* we can prove the hypothesis:

    eval (c / e) == eval c >>= λ n => eval (⌊ n ⌋ / e)
*)


From Coinduction Require Import coinduction lattice rel tactics.

Lemma fmap_comp_eq {Γ} {u v : delay (nf Γ)} : u ≋ v -> fmap_delay (pat_of_nf Γ) u ≊ fmap_delay (pat_of_nf Γ) v .
  intro H.
  unfold it_eq; revert u v H; coinduction R CIH; intros u v H.
  unfold comp_eq in H; apply it_eq_step in H; cbn in *; unfold observe in H.
  remember (_observe u) as ou; remember (_observe v) as ov; clear Heqou u Heqov v.
  dependent elimination H; cbn; econstructor; auto.
  destruct r1 as [ x1 [ i1 [ m1 e1 ] ] ].
  destruct r2 as [ x2 [ i2 [ m2 e2 ] ] ].
  destruct r_rel as [ H1 [ H2 [ H3 _ ] ] ]; cbn in *.
  unfold pat_of_nf; cbn.
  revert i1 m1 e1 H2 H3; rewrite H1; clear x1 H1; intros i1 m1 e1 H2 H3; cbn in H2,H3.
  now rewrite H2,H3.
  destruct q.
Qed.
(*
Lemma clean_hyp {Γ Δ : neg_ctx} (c : state Γ) (e : Γ ⊆ Δ)
   : play (s_rename e c) ≊ fmap_delay (n_rename e) (play c) .
  unfold it_eq; revert Γ c e; coinduction R CIH; intros Γ c e.
  cbn.
  dependent elimination c.
  dependent elimination t0.
  - cbn; econstructor. (* Cut (Mu _) _) *)
    change (t_rename e (t- a0) t1) with (v_rename e (t- a0) t1).
    rewrite s_sub1_ren.
    apply CIH.
  - dependent elimination t1.
    + cbn; econstructor. unfold n_rename; cbn.
      do 2 f_equal.
      rewrite p_of_v_eq.
      unfold a_ren.
      ; reflexivity. cbn. rewrite s_subst_equation_1, t_subst_equation_3.
      unfold play at 2; cbn -[play then_play2].
      unfold then_play2.
      cbn -[eval eval_aux]; rewrite refold_id.
      cbv [observe]; destruct (_observe (play (Cut (Val (v0_subst e a2 v)) (e (t- a2) h)))); econstructor; reflexivity.
    + unfold play. cbn -[then_play2]; change (iter _ T1_0 ?x) with (play x).
      change (v0_subst e a3 v) with (v_subst e (t+ a3) v); rewrite s_sub1_sub.
      econstructor; apply CIH.
    + dependent elimination v. (* Cut (Val _) ZerK *)
      pose (nope := (s_elt_upg h).(sub_prf)); dependent elimination nope.
    + dependent elimination v. (* Cut (Val _) (App _ _)) *)
      * unfold play at 2; cbn -[play then_play2].
        unfold then_play2; cbn -[play eval_aux].
        rewrite v0_sub_ren.
        assert ((@s_append _ _ _ _ (t- b) (p_dom_of_v0 a4 v1) t0 ⊛ᵣ s_pop)
                ≡ₐ p_dom_of_v0 a4 v1) by auto.
        rewrite (v0_sub_eq _ _ H a4 _ _ eq_refl), refold_id.
        cbn -[eval_aux];
          destruct (eval_aux (Cut (Val (e _ h)) (App (v0_subst e _ v1) (t_subst e _ t0))));
          econstructor;
          reflexivity.
      * cbn; econstructor; change (iter _ T1_0 ?x) with (play x).
        change (LamRec (t_subst (a_shift2 e) (t+ b2) t1)) with (v0_subst e (a2 → b2) (LamRec t1)).
        unfold t_subst1 at 1 2.
        rewrite 2 t_sub_sub.
        rewrite <- (t_sub_eq _ _ (a_comp_assoc _ _ _) (t+ b2) t1 t1 eq_refl).
        rewrite <- t_sub_sub.
        unfold v0_shift at 1; rewrite v0_ren_sub.
        assert (a_comp (ass1 (v_subst (a_ren (s_pop (x:= (t+ (a2 → b2)))) e) (t+ a2) v1)) (a_shift2 e) ≡ₐ a_comp (a_shift e) (ass1 (v_shift (t+ _) v1))).
        ** intros ? i; dependent elimination i as [ Ctx.top | Ctx.pop Ctx.top | Ctx.pop (Ctx.pop i) ]; cbn.
           ++ rewrite v0_sub_ren; now apply v0_sub_eq.
           ++ reflexivity.
           ++ destruct x1; cbn.
              rewrite v0_ren_ren, v0_sub_ren.
              rewrite <- (v0_sub_id_l t (v0_rename s_pop t (e _ i))), v0_sub_ren.
              now apply v0_sub_eq.
              rewrite t_ren_ren, t_sub_ren.
              rewrite <- (t_sub_id_l _ (t_rename s_pop _ (e _ i))), t_sub_ren.
              now apply t_sub_eq.
        ** rewrite (t_sub_eq _ _ H _ _ _ eq_refl).
           rewrite t_sub_sub.
        rewrite (t_sub_eq _ _ (a_comp_assoc _ _ _) (t+ b2) t1 t1 eq_refl).
        rewrite <- t_sub_sub.
        change (v0_subst e _ (LamRec t1)) with (v_subst e (t+ _) (LamRec t1)).
        rewrite (t_sub_eq _ _ (sub1_sub (a:=t+ _) e (LamRec t1)) _ _ _ eq_refl).
        rewrite <- t_sub_sub.
        change (Cut (t_subst e _ ?a) (t_subst e _ t0)) with (s_subst e (Cut a t0)).
        apply CIH.
    + dependent elimination v. (* Cut (Val _) Fst *)
      * unfold play at 2; cbn -[play then_play2].
        unfold then_play2; cbn -[play eval_aux].
        cbn -[eval_aux];
          destruct (eval_aux (Cut (Val (e _ h)) (Fst (t_subst e _ t1))));
          econstructor;
          reflexivity.
      * cbn; econstructor; apply CIH.
    + dependent elimination v. (* Cut (Val _) Snd *)
      * unfold play at 2; cbn -[play then_play2].
        unfold then_play2; cbn -[play eval_aux].
        cbn -[eval_aux];
          destruct (eval_aux (Cut (Val (e _ h)) (Snd (t_subst e _ t2))));
          econstructor;
          reflexivity.
      * cbn; econstructor; apply CIH.
    + dependent elimination v. (* Cut (Val _) (Match _ _) *)
      * pose (nope := (s_elt_upg h).(sub_prf)); dependent elimination nope.
      * cbn; econstructor; change (iter _ T1_0 ?x) with (play x).
        change (v0_subst e a0 v) with (v_subst e (t+ a0) v); rewrite s_sub1_sub.
        apply CIH.
      * cbn; econstructor; change (iter _ T1_0 ?x) with (play x).
        change (v0_subst e b0 v0) with (v_subst e (t+ b0) v0); rewrite s_sub1_sub.
        apply CIH.
Qed.
  - 
    unfold 
    rewrite s_ren1_sub.
    apply CIH.
    *)

Lemma clean_hyp {Γ Δ : neg_ctx} (c : state Γ) (e : Γ =[val]> Δ)
   : play (s_subst e c) ≊ bind_delay' (play c) (then_play1 e) .
  transitivity (bind_delay' (play c) (then_play2 e)); cycle 1.
  apply (proj1 (t_gfp (it_eq_map ∅ₑ (eqᵢ _)) _ _ _)).
  eapply (it_eq_up2bind_t (eqᵢ _)); econstructor; auto.
  intros [] ? ? <-; symmetry; exact (then_play_eq e x1).
  unfold iter_delay, it_eq, bind.
  revert Γ c e; coinduction R CIH; intros Γ c e.
  dependent elimination c.
  dependent elimination t0.
  - cbn; econstructor. (* Cut (Mu _) _) *)
    change (t_subst e (t- a0) t1) with (v_subst e (t- a0) t1).
    rewrite s_sub1_sub.
    apply CIH.
  - dependent elimination t1.
    + rewrite s_subst_equation_1, t_subst_equation_3.
      unfold play at 2; cbn -[play then_play2].
      unfold then_play2.
      cbn -[eval eval_aux]; rewrite refold_id.
      cbv [observe]; destruct (_observe (play (Cut (Val (v0_subst e a2 v)) (e (t- a2) h)))); econstructor; reflexivity.
    + unfold play. cbn -[then_play2]; change (iter _ T1_0 ?x) with (play x).
      change (v0_subst e a3 v) with (v_subst e (t+ a3) v); rewrite s_sub1_sub.
      econstructor; apply CIH.
    + dependent elimination v. (* Cut (Val _) ZerK *)
      pose (nope := (s_elt_upg h).(sub_prf)); dependent elimination nope.
    + dependent elimination v. (* Cut (Val _) (App _ _)) *)
      * unfold play at 2; cbn -[play then_play2].
        unfold then_play2; cbn -[play eval_aux].
        rewrite v0_sub_ren.
        assert ((@s_append _ _ _ _ (t- b) (p_dom_of_v0 a4 v1) t0 ⊛ᵣ s_pop)
                ≡ₐ p_dom_of_v0 a4 v1) by auto.
        rewrite (v0_sub_eq _ _ H a4 _ _ eq_refl), refold_id.
        cbn -[eval_aux];
          destruct (eval_aux (Cut (Val (e _ h)) (App (v0_subst e _ v1) (t_subst e _ t0))));
          econstructor;
          reflexivity.
      * cbn; econstructor; change (iter _ T1_0 ?x) with (play x).
        change (LamRec (t_subst (a_shift2 e) (t+ b2) t1)) with (v0_subst e (a2 → b2) (LamRec t1)).
        unfold t_subst1 at 1 2.
        rewrite 2 t_sub_sub.
        rewrite <- (t_sub_eq _ _ (a_comp_assoc _ _ _) (t+ b2) t1 t1 eq_refl).
        rewrite <- t_sub_sub.
        unfold v0_shift at 1; rewrite v0_ren_sub.
        assert (a_comp (ass1 (v_subst (a_ren (s_pop (x:= (t+ (a2 → b2)))) e) (t+ a2) v1)) (a_shift2 e) ≡ₐ a_comp (a_shift e) (ass1 (v_shift (t+ _) v1))).
        ** intros ? i; dependent elimination i as [ Ctx.top | Ctx.pop Ctx.top | Ctx.pop (Ctx.pop i) ]; cbn.
           ++ rewrite v0_sub_ren; now apply v0_sub_eq.
           ++ reflexivity.
           ++ destruct x1; cbn.
              rewrite v0_ren_ren, v0_sub_ren.
              rewrite <- (v0_sub_id_l t (v0_rename s_pop t (e _ i))), v0_sub_ren.
              now apply v0_sub_eq.
              rewrite t_ren_ren, t_sub_ren.
              rewrite <- (t_sub_id_l _ (t_rename s_pop _ (e _ i))), t_sub_ren.
              now apply t_sub_eq.
        ** rewrite (t_sub_eq _ _ H _ _ _ eq_refl).
           rewrite t_sub_sub.
        rewrite (t_sub_eq _ _ (a_comp_assoc _ _ _) (t+ b2) t1 t1 eq_refl).
        rewrite <- t_sub_sub.
        change (v0_subst e _ (LamRec t1)) with (v_subst e (t+ _) (LamRec t1)).
        rewrite (t_sub_eq _ _ (sub1_sub (a:=t+ _) e (LamRec t1)) _ _ _ eq_refl).
        rewrite <- t_sub_sub.
        change (Cut (t_subst e _ ?a) (t_subst e _ t0)) with (s_subst e (Cut a t0)).
        apply CIH.
    + dependent elimination v. (* Cut (Val _) Fst *)
      * unfold play at 2; cbn -[play then_play2].
        unfold then_play2; cbn -[play eval_aux].
        cbn -[eval_aux];
          destruct (eval_aux (Cut (Val (e _ h)) (Fst (t_subst e _ t1))));
          econstructor;
          reflexivity.
      * cbn; econstructor; apply CIH.
    + dependent elimination v. (* Cut (Val _) Snd *)
      * unfold play at 2; cbn -[play then_play2].
        unfold then_play2; cbn -[play eval_aux].
        cbn -[eval_aux];
          destruct (eval_aux (Cut (Val (e _ h)) (Snd (t_subst e _ t2))));
          econstructor;
          reflexivity.
      * cbn; econstructor; apply CIH.
    + dependent elimination v. (* Cut (Val _) (Match _ _) *)
      * pose (nope := (s_elt_upg h).(sub_prf)); dependent elimination nope.
      * cbn; econstructor; change (iter _ T1_0 ?x) with (play x).
        change (v0_subst e a0 v) with (v_subst e (t+ a0) v); rewrite s_sub1_sub.
        apply CIH.
      * cbn; econstructor; change (iter _ T1_0 ?x) with (play x).
        change (v0_subst e b0 v0) with (v_subst e (t+ b0) v0); rewrite s_sub1_sub.
        apply CIH.
Qed.

Definition is_var {Γ x} (v : val Γ x) : Type := { i : Γ ∋ x & v = Var x i } .
Definition is_var_get {Γ x} {v : val Γ x} (p : is_var v) : Γ ∋ x := projT1 p .

Lemma is_var_dec {Γ x} (v : val Γ x) : is_var v + (is_var v -> False) .
  destruct x; dependent elimination v.
  all: try now (apply inr; intros [ i H ]; inversion H).
  all: apply inl; econstructor; auto.
Qed.

(*
Lemma v_is_var_ren {Γ1 Γ2 x} (v : val Γ1 x) (e : Γ1 ⊆ Γ2) : is_var (v_rename e _ v) -> is_var v .
  intros [ i H ].
  destruct x; cbn in *.
  - dependent induction v; cbn in *; try now inversion H.
    exact (h ,' eq_refl).
  - dependent induction v; cbn in *; try now inversion H.
    exact (h ,' eq_refl).
Qed.

Lemma v_is_var_sub {Γ1 Γ2 x} (v : val Γ1 x) (e : Γ1 ⊆ Γ2) : is_var (v_subst (Var ⊛ᵣ e) _ v) -> is_var v .
  intros [ i H ].
  destruct x; cbn in *.
  - dependent induction v; cbn in *; try now inversion H.
    exact (h ,' eq_refl).
  - dependent induction v; cbn in *; try now inversion H.
    exact (h ,' eq_refl).
Qed.
*)

Equations p_of_v_eq {Γ : neg_ctx} {t} (p : pat (t+ t)) (e : (pat_dom p) =[ val ]> Γ) 
          : p_of_v0 t (v0_subst e t (v_of_p p)) = p :=
  p_of_v_eq (PInl p) e := f_equal PInl (p_of_v_eq p e) ;
  p_of_v_eq (PInr p) e := f_equal PInr (p_of_v_eq p e) ;
  p_of_v_eq (POneI)  e := eq_refl ;
  p_of_v_eq (PLam)   e := eq_refl ;
  p_of_v_eq (PPair)  e := eq_refl .

Lemma p_dom_of_v_eq {Γ : neg_ctx} {t} (p : pat (t+ t)) (e : (pat_dom p) =[ val ]> Γ)
  : rew [fun p0 => pat_dom p0 =[ val ]> Γ] p_of_v_eq p e in p_dom_of_v0 t (v0_subst e t (v_of_p p)) ≡ₐ e .
  induction t; dependent elimination p.
  - intros ? h; repeat (dependent elimination h; auto).
  - intros ? h; repeat (dependent elimination h; auto).
  - cbn.
    pose (xx := rew [fun p0 : pat (t+ (a + b)) => pat_dom p0 =[ val ]> Γ] f_equal PInl (p_of_v_eq p e) in
  p_dom_of_v0 (a + b) (Inl (v0_subst e a (v_of_p p)))).
    change (_ ≡ₐ e) with (xx ≡ₐ e).
    remember xx as yy; unfold xx in Heqyy; clear xx.
    rewrite (eq_trans Heqyy (eq_sym (rew_map (fun p0 => pat_dom p0 =[ val ]> Γ) PInl (p_of_v_eq p e) (p_dom_of_v0 (a + b) (Inl (v0_subst e a (v_of_p p))))))).
    apply IHt1.
  - cbn.
    pose (xx := rew [fun p0 : pat (t+ (a0 + b0)) => pat_dom p0 =[ val ]> Γ] f_equal PInr (p_of_v_eq p0 e) in
  p_dom_of_v0 (a0 + b0) (Inr (v0_subst e b0 (v_of_p p0)))).
    change (_ ≡ₐ e) with (xx ≡ₐ e).
    remember xx as yy; unfold xx in Heqyy; clear xx.
    rewrite (eq_trans Heqyy (eq_sym (rew_map (fun p0 => pat_dom p0 =[ val ]> Γ) PInr (p_of_v_eq p0 e) (p_dom_of_v0 (a0 + b0) (Inr (v0_subst e b0 (v_of_p p0))))))).
    apply IHt2.
  - intros ? h; repeat (dependent elimination h; auto).
Qed.

Lemma eval_nf_ret {Γ : neg_ctx} (u : nf Γ) : eval (p_app (Var _ (fst (projT2 u))) (projT1 (snd (projT2 u))) (projT2 (snd (projT2 u)))) ≋ ret_delay u .
  unfold play, iter_delay.
  rewrite iter_unfold.
  unfold comp_eq. apply it_eq_unstep; cbn.
  change (iter _ T1_0 ?x) with (iter_delay (fun c : state Γ => Ret' (eval_aux c)) x).
  destruct u as [ [] [ i [ m γ ]]]; simpl t_neg in m; simpl p_app.
  - funelim (v_of_p m); cbn.
    + do 3 unshelve econstructor; auto; cbn.
      rewrite v0_sub_ren.
      clear ; cbn in *.
      assert (@nf0_eq _ (t- a4) ((p_of_v0 a4 (v0_subst (γ ⊛ᵣ s_pop) a4 (v_of_p v))) ,'
                                  p_dom_of_v0 a4 (v0_subst (γ ⊛ᵣ s_pop) a4 (v_of_p v)))
                (v,' (γ ⊛ᵣ s_pop)))
        by (unshelve econstructor; [ apply p_of_v_eq | apply p_dom_of_v_eq ]).
      destruct H as [ p q ]; unshelve econstructor; [ exact (f_equal PApp p) | ].
      cbn; rewrite <- rew_map.
      cbn; rewrite (rew_map (fun xs => (xs ▶ t- b3) =[val]> Γ) pat_dom).
      rewrite rew_s_append.
      intros ? h; dependent elimination h; auto.
      etransitivity; [ | apply (q _ h) ].
      now rewrite (rew_map (fun xs => xs =[val]> Γ) pat_dom).
    + repeat unshelve econstructor; cbn.
      intros ? h; repeat (dependent elimination h; auto).
    + repeat unshelve econstructor; cbn.
      intros ? h; repeat (dependent elimination h; auto).
  - repeat unshelve econstructor; [ apply p_of_v_eq | apply p_dom_of_v_eq ].
Qed.

Lemma foo {I : Type} {E : event I I} {X : psh I} {RX RY : relᵢ X X}
  : Subrelationᵢ RX RY -> Subrelationᵢ (it_eq (E:=E) RX) (it_eq (E:=E) RY) .
  intros H1 i a b H2.
  unfold it_eq; revert i a b H2; coinduction R CIH; intros i a b H2.
  apply it_eq_step in H2; cbn in *.
  remember (observe a) as oa; clear Heqoa a.
  remember (observe b) as ob; clear Heqob b.
  dependent elimination H2.
  - econstructor; now apply H1.
  - econstructor; now apply CIH.
  - econstructor; intro; now apply CIH. 
Qed.

Lemma clean_hyp_ren {Γ Δ : neg_ctx} (c : state Γ) (e : Γ ⊆ Δ)
   : play (s_rename e c) ≋ fmap_delay (n_rename e) (play c) .
  rewrite <- (s_sub_id_l c) at 1.
  rewrite s_ren_sub.
  unfold comp_eq.
  etransitivity.
  eapply (foo (RX := eqᵢ _)).
  intros ? ? ? ->; now apply nf_eq_rfl.
  exact (clean_hyp c (a_ren e Var)).
  remember (play c) as t; clear Heqt c.
  unfold then_play1.
  unfold fmap_delay, bind_delay'.
  rewrite bind_ret.
  apply (proj1 (t_gfp (it_eq_map ∅ₑ (fun _ : T1 => nf_eq)) _ _ _)).
  eapply (it_eq_up2bind_t (eqᵢ _)); econstructor; auto.
  intros [] u v ->.
  destruct v as [ x [ i [ m e' ] ] ]; cbn in *.
  unfold n_rename; cbn.
  unfold a_ren at 1; rewrite v_ren_id_r.
  rewrite (eval_nf_ret (x ,' (e x i , (m ,' a_comp (a_ren e Var) e')))).
  change (gfp _ _ ?a ?b) with (it_eq (fun _ : T1 => nf_eq) a b).
  apply it_eq_unstep.
  econstructor.
  unshelve econstructor; auto; cbn.
  unshelve econstructor; auto; cbn.
  unshelve econstructor; auto; cbn.
  clear; intros ? i.
  unfold a_comp, a_ren; cbn.
  erewrite (v_sub_eq _ (Var ⊛ᵣ e)); auto.
  now rewrite <- v_sub_ren, v_sub_id_l.
  intros ? j. now rewrite v_ren_id_r.
Qed.

  
  
(*
Lemma eval_nf_ret {Γ : neg_ctx} (u : nf Γ) : fmap_delay (pat_of_nf Γ) (eval (p_app (Var _ (fst (projT2 u))) (projT1 (snd (projT2 u))) (projT2 (snd (projT2 u))))) ≊ ret_delay (pat_of_nf _ u) .
  unfold play, iter_delay.
  rewrite iter_unfold.
  apply it_eq_unstep; cbn.
  change (iter _ T1_0 ?x) with (iter_delay (fun c : state Γ => Ret' (eval_aux c)) x).
  destruct u as [ [] [ i [ m γ ]]]; simpl t_neg in m; simpl p_app.
  - funelim (v_of_p m); cbn; econstructor; cbn; auto.
    unfold pat_of_nf; cbn.
    now rewrite v0_sub_ren, p_of_v_eq.
  - funelim (v_of_p m); cbn; econstructor; cbn; auto.
    + unfold pat_of_nf; cbn.
      change (p_of_v0 _ (Inl ?a)) with (PInl (b:=b) (p_of_v0 _ a)).
      now rewrite p_of_v_eq.
    + unfold pat_of_nf; cbn.
      change (p_of_v0 _ (Inr ?a)) with (PInr (a:=a1) (p_of_v0 _ a)).
      now rewrite p_of_v_eq.
Qed.
*)

Variant head_inst_nostep (u : { x : ty & pat (t_neg x) }) : { x :ty & pat (t_neg x) } -> Prop :=
| HeadInst {Γ : neg_ctx} {y} (v : val Γ y) (m : pat (t_neg y)) (e : pat_dom m =[val]> Γ) (p : is_var v -> False) (i : Γ ∋ (projT1 u : ty))
           : fmap_delay (pat_of_nf Γ) (eval (p_app v m e)) ≊ ret_delay ((projT1 u : ty) ,' (i , projT2 u)) -> head_inst_nostep u (y ,' m) .

Lemma eval_app_not_var : well_founded head_inst_nostep .
  intros a; econstructor; intros b H.
  dependent elimination H.
  apply it_eq_step in i0; cbn - [ eval_aux ] in i0.
  destruct y as [ t | t ]; simpl p_app in *; simpl t_neg in *.
  - funelim (v_of_p m); cbn - [ eval_aux ] in i0.
    all: try dependent elimination v0; try dependent elimination v; dependent elimination i0.
    all: destruct (p (_ ,' eq_refl)).
  - funelim (v_of_p m); cbn - [ eval_aux ] in i0.
    all: dependent elimination v; try now destruct (p (_ ,' eq_refl)).
    all: try now dependent elimination i0.
    all: pose (v := (e (t+ _) Ctx.top)); change (e (t+ _) _) with v in i0.
    all: remember v as v'; clear v Heqv'; dependent elimination v'; dependent elimination i0.
    all: unfold pat_of_nf in r_rel; cbn in r_rel; inversion r_rel; clear r_rel.
    all: clear i H1 p; destruct b as [ t p1 ]; cbn in *.
    all: revert p1; rewrite <- H0; clear H0; intros p1; simpl in p1.
    all: econstructor; intros c H; dependent elimination H; cbn in *.
    all: apply it_eq_step in i0; cbn in i0.
    all: dependent elimination m; dependent elimination v; dependent elimination i0.
    all: destruct (p (_ ,' eq_refl)).
Qed.

From OGS.OGS Require Spec.

(*
Definition ctx_allS (Γ : ctx neg_ty) : allS is_neg (c_map sub_elt Γ).
  induction Γ; intros ? i; cbn in *.
  - remember ∅%ctx as Γ; destruct i; inversion HeqΓ.
  - remember (_ ▶ _)%ctx as Γ' in i; destruct i; inversion HeqΓ'.
    + exact x.(sub_prf).
    + rewrite <- H0 in IHΓ; exact (IHΓ _ i).
Defined.

Definition ctx_from (Γ : ctx neg_ty) : neg_ctx := {| sub_elt := c_map sub_elt Γ ; sub_prf := ctx_allS Γ |}.
*)

Definition mu_spec : Spec.interaction_spec :=
  {| Spec.typ := neg_ty ;
     Spec.msg := fun t => pat (t_neg t) ;
     Spec.dom := fun t p => ctx_s_to (pat_dom p) |}
.

Definition state' (Γ : ctx neg_ty) : Type := state (ctx_s_from Γ).
Definition val' (Γ : ctx neg_ty) (a : neg_ty) : Type := val (ctx_s_from Γ) a.(sub_elt).

Definition r_from_to_l {Γ : neg_ctx} : ctx_s_from (ctx_s_to Γ) ⊆ Γ.
  rewrite ctx_s_from_to; exact r_id.
Defined.

Definition r_from_to_r {Γ : neg_ctx} : Γ ⊆ ctx_s_from (ctx_s_to Γ) .
  rewrite ctx_s_from_to; exact r_id.
Defined.

Lemma r_from_to_lr {Γ : neg_ctx} : r_from_to_l ⊛ᵣ r_from_to_r ≡ₐ @r_id _ Γ .
  unfold r_from_to_l, r_from_to_r; now rewrite (ctx_s_from_to Γ).
Qed.

Lemma r_from_to_rl {Γ : neg_ctx} : r_from_to_r ⊛ᵣ r_from_to_l ≡ₐ @r_id _ (ctx_s_from (ctx_s_to Γ)) .
  unfold r_from_to_l, r_from_to_r; now rewrite (ctx_s_from_to Γ).
Qed.

Definition r_to_from_l {Γ : ctx neg_ty} : ctx_s_to (ctx_s_from Γ) ⊆ Γ .
  unfold ctx_s_from; destruct (ctx_s_to_inv Γ); exact r_id.
Defined.

Definition r_to_from_r {Γ : ctx neg_ty} : Γ ⊆ ctx_s_to (ctx_s_from Γ) .
  unfold ctx_s_from; destruct (ctx_s_to_inv Γ); exact r_id.
Defined.

Lemma r_to_from_lr {Γ : ctx neg_ty} : r_to_from_l ⊛ᵣ r_to_from_r ≡ₐ @r_id _ Γ .
  unfold ctx_s_from, r_to_from_l, r_to_from_r, s_ren, s_map; cbn.
  intros ? i; now destruct (ctx_s_to_inv Γ).
Qed.

Lemma r_to_from_rl {Γ : ctx neg_ty} : r_to_from_r ⊛ᵣ r_to_from_l ≡ₐ @r_id _ (ctx_s_to (ctx_s_from Γ)) .
  unfold ctx_s_from, r_to_from_l, r_to_from_r, s_ren, s_map; cbn.
  intros ? i; now destruct (ctx_s_to_inv Γ).
Qed.

Definition from_has_F {Γ : neg_ctx} {t} (i : ctx_s_to Γ ∋ t) : Γ ∋ t.(sub_elt) :=
  match view_s_has_map _ _ i in (s_has_map_view _ _ y h) return (Γ ∋ sub_elt y) with
  | SHasMapV j => j
  end .

Definition to_has_F {Γ : neg_ctx} {t} (i : Γ ∋ t) : ctx_s_to Γ ∋ s_elt_upg i :=
  s_map_has _ _ i .

Lemma to_from_has_F {Γ : neg_ctx} {t} (i : ctx_s_to Γ ∋ t) : to_has_F (from_has_F i) = i .
  unfold to_has_F, from_has_F.
  pose (xx := view_s_has_map (fun x : sigS is_neg => x) Γ i).
  change (view_s_has_map (fun x : sigS is_neg => x) Γ i) with xx.
  now destruct xx.
Qed.

Lemma from_to_has_F {Γ : neg_ctx} {t} (i : Γ ∋ t) : from_has_F (to_has_F i) = i .
  unfold from_has_F, to_has_F.
  pose proof (s_has_map_view_simpl (f := fun x : neg_ty => x) (i := i)).
  pose (xx := view_s_has_map (fun x : neg_ty => x) Γ (s_map_has (fun x : neg_ty => x) Γ i)).
  change (view_s_has_map _ _ _) with xx in H |- *.
  now rewrite H.
Qed.

Definition from_has_R {Γ : ctx neg_ty} {t} (i : Γ ∋ t) : ctx_s_from Γ ∋ t.(sub_elt) .
  unfold ctx_s_from; destruct (ctx_s_to_inv Γ).
  exact (from_has_F i).
Defined.

Definition to_has_R {Γ : ctx neg_ty} {t} (i : ctx_s_from Γ ∋ t) : Γ ∋ s_elt_upg i .
  unfold s_elt_upg; unfold ctx_s_from in *; destruct (ctx_s_to_inv Γ).
  exact (to_has_F i).
Defined.

Lemma from_to_has_R {Γ : ctx neg_ty} {t} (i : ctx_s_from Γ ∋ t) : from_has_R (to_has_R i) = i .
  unfold from_has_R, to_has_R, s_elt_upg; unfold ctx_s_from in *.
  destruct (ctx_s_to_inv Γ).
  unfold from_has_F.
  pose proof (s_has_map_view_simpl (f := fun x : neg_ty => x) (i := i)).
  pose (xx := view_s_has_map (fun x : neg_ty => x) a (s_map_has (fun x : neg_ty => x) a i)).
  change (view_s_has_map _ _ _) with xx in H |- *.
  now rewrite H.
Qed.

Lemma to_from_has_R {Γ : ctx neg_ty} {t} (i : Γ ∋ t) : to_has_R (from_has_R i) = i .
  unfold to_has_R, from_has_R; unfold ctx_s_from. 
  destruct (ctx_s_to_inv Γ).
  apply to_from_has_F.
Qed.
  
Definition to_FB {Γ1 : neg_ctx} {Γ2} (u : Γ1 =[val]> ctx_s_from Γ2) : ctx_s_to Γ1 =[val']> Γ2 :=
  fun _ i => u _ (from_has_F i) .

#[global] Instance to_FB_proper {Γ1 Γ2} : Proper (ass_eq _ _ ==> ass_eq _ _) (@to_FB Γ1 Γ2).
  intros u1 u2 H ? i; apply (H _ (from_has_F i)).
Qed.

Definition from_FB {Γ1 : neg_ctx} {Γ2} (u : ctx_s_to Γ1 =[val']> Γ2) : Γ1 =[val]> ctx_s_from Γ2 :=
  fun _ i => u _ (to_has_F i) .

#[global] Instance from_FB_proper {Γ1 Γ2} : Proper (ass_eq _ _ ==> ass_eq _ _) (@from_FB Γ1 Γ2).
  intros u1 u2 H ? i; unfold from_FB.
  exact (H _ (s_map_has _ _ i)).
Qed.

Lemma to_from_FB {Γ1 : neg_ctx} {Γ2} (u : ctx_s_to Γ1 =[val']> Γ2) : to_FB (from_FB u) ≡ₐ u .
  intros ? i; unfold to_FB, from_FB.
  f_equal; apply to_from_has_F.
Qed.

Lemma from_to_FB {Γ1 : neg_ctx} {Γ2} (u : Γ1 =[val]> ctx_s_from Γ2) : from_FB (to_FB u) ≡ₐ u.
  intros ? i; unfold to_FB, from_FB.
  now rewrite from_to_has_F.
Qed.

Definition to_FF {Γ1 Γ2 : neg_ctx} (u : Γ1 =[val]> Γ2) : ctx_s_to Γ1 =[val']> ctx_s_to Γ2 := 
  to_FB (a_ren r_from_to_r u).

#[global] Instance to_FF_proper {Γ1 Γ2} : Proper (ass_eq _ _ ==> ass_eq _ _) (@to_FF Γ1 Γ2).
  intros u1 u2 H ? i; unfold to_FF.
  apply to_FB_proper.
  now rewrite H.
Qed.

Definition from_FF {Γ1 Γ2 : neg_ctx} (u : ctx_s_to Γ1 =[val']> ctx_s_to Γ2) : Γ1 =[val]> Γ2 :=
  a_ren r_from_to_l (from_FB u) .

#[global] Instance from_FF_proper {Γ1 Γ2} : Proper (ass_eq _ _ ==> ass_eq _ _) (@from_FF Γ1 Γ2).
  intros u1 u2 H ? i; unfold from_FF.
  apply a_ren_eq; auto.
  now apply from_FB_proper.
Qed.

Definition to_BB {Γ1 Γ2} (u : ctx_s_from Γ1 =[val]> ctx_s_from Γ2) : Γ1 =[val']> Γ2 :=
  fun _ i => u _ (from_has_R i) .

#[global] Instance to_BB_proper {Γ1 Γ2} : Proper (ass_eq _ _ ==> ass_eq _ _) (@to_BB Γ1 Γ2).
  intros ? ? H ? i; exact (H _ (from_has_R i)).
Qed.

Definition from_BB {Γ1 Γ2} (u : Γ1 =[val']> Γ2) : ctx_s_from Γ1 =[val]> ctx_s_from Γ2 :=
  fun _ i => u _ (to_has_R i).

#[global] Instance from_BB_proper {Γ1 Γ2} : Proper (ass_eq _ _ ==> ass_eq _ _) (@from_BB Γ1 Γ2).
  intros u1 u2 H ? i; exact (H _ (to_has_R i)).
Qed.

Lemma to_from_BB {Γ1 Γ2} (u : Γ1 =[val']> Γ2) : to_BB (from_BB u) ≡ₐ u .
  unfold to_BB, from_BB.
  intros ? i; f_equal.
  apply to_from_has_R.
Qed.

Lemma from_to_BB {Γ1 Γ2} (u : ctx_s_from Γ1 =[val]> ctx_s_from Γ2) : from_BB (to_BB u) ≡ₐ u .
  unfold to_BB, from_BB.
  intros ? i; f_equal.
  apply from_to_has_R.
Qed.

Definition ugly_var {Γ} : Γ =[val']> Γ := fun _ i => Var _ (from_has_R i) .

Lemma from_BB_var {Γ} : from_BB (@ugly_var Γ) ≡ₐ Var .
  unfold from_BB, from_FB, ugly_var, ctx_s_from, s_ren, s_map, from_has_R, to_has_R, r_to_from_l, s_elt_upg.
  intros ? i; f_equal.
  destruct (ctx_s_to_inv Γ); cbn in *.
  unfold from_has_F; change (s_map_has' ?a _ _ i) with (s_map_has a a0 i).
  pose proof (s_has_map_view_simpl (f := fun x : neg_ty => x) (Γ := a0) (i := i)).
  pose (x := view_s_has_map (fun x => x) a0 (s_map_has (fun x => x) a0 i)).
  change (view_s_has_map _ _ _) with x in H |- *.
  now rewrite H.
Qed.

Lemma ugly_var_inj {Γ x} (i j : Γ ∋ x) : ugly_var x i = ugly_var x j -> i = j .
  intro H.
  unfold ugly_var, from_has_R, from_has_F in H.
  apply var_inj in H.
  pose (xx := ctx_s_to_inv Γ).
  fold xx in H.
  dependent induction xx; clear xx0.
  pose (xx := ctx_s_to_inv (ctx_s_to a)).
  change (ctx_s_to_inv (ctx_s_to a)) with xx in x , H.
  change (sigS _) with neg_ty in H.

  (* >> !!!! rewrite is borked *)
  pose proof (@eq_ind (fiber ctx_s_to (ctx_s_to a)) xx
           (fun u =>
  match u as f in (fiber _ b) return (b ∋ x0 -> fib_extr f ∋ sub_elt x0) with
      | Fib a =>
          fun i : ctx_s_to a ∋ x0 =>
          match view_s_has_map (fun x : neg_ty => x) a i in (s_has_map_view _ _ y h) return (a ∋ sub_elt y) with
          | SHasMapV j => j
          end
      end i =
      match u as f in (fiber _ b) return (b ∋ x0 -> fib_extr f ∋ sub_elt x0) with
      | Fib a =>
          fun i : ctx_s_to a ∋ x0 =>
          match view_s_has_map (fun x : neg_ty => x) a i in (s_has_map_view _ _ y h) return (a ∋ sub_elt y) with
          | SHasMapV j => j
          end
      end j
        ) H _ (eq_sym x)).
  clear H x xx; cbn in H0.
  (* << !!!! rewrite is borked *)

  destruct (view_s_has_map (fun x : neg_ty => x) _ i).
  rewrite H0; clear H0.

  (* >> !!!! remember is borked *)
  unfold s_elt_upg in j; revert j.
  refine (((fun p => _) : forall (p : is_neg x) (j : @ctx_s_to ty is_neg a ∋ {| sub_elt := x; sub_prf := p |}),
  @s_map_has ty is_neg neg_ty (fun x0 : neg_ty => x0) a x
    match
      @view_s_has_map ty is_neg neg_ty (fun x0 : neg_ty => x0) a
        {| sub_elt := x; sub_prf := p |} j in (s_has_map_view _ _ y h)
      return (a ∋ @sub_elt _ _ y)
    with
    | SHasMapV j0 => j0
    end = j) (sub_prf a x i)).
  clear i; intro j.
  pose (xx := view_s_has_map (fun x0 : neg_ty => x0) a j); fold xx.
  dependent induction xx; clear xx0.
  (* >> !!!! remember is borked *)

  pose (xx := view_s_has_map (fun x1 : neg_ty => x1) a (s_map_has (fun x1 : sigS is_neg => x1) a i)).
  change (view_s_has_map _ _ _) with xx in x |- *.
  now rewrite <- x.  
Qed.

Lemma ugly_var_dec {Γ x} (v : val' Γ x) : {i : Γ ∋ x & v = ugly_var x i} + ({i : Γ ∋ x & v = ugly_var x i} -> False) .
 destruct (is_var_dec v); [ apply inl | apply inr ].
 + unfold val' in v; unfold ugly_var, from_has_R; unfold ctx_s_from in *.
   destruct i; unshelve econstructor.
   * clear e; destruct (ctx_s_to_inv Γ).
     exact (s_map_has _ _ x0).
   * refine (eq_trans e _); clear e; f_equal.
     destruct (ctx_s_to_inv Γ); cbn.
     unfold from_has_F.
     pose (xx := view_s_has_map (fun x1 : sigS is_neg => x1) a (s_map_has (fun x1 : sigS is_neg => x1) a x0)).
     pose proof (s_has_map_view_simpl (f := fun x : neg_ty => x) (i := x0)).
     change (view_s_has_map _ _ _) with xx in H |- *.
     now rewrite H.
 + intros []; apply f.
   exact (from_has_R x0 ,' e).
Qed.

Lemma ugly_is_var_ren {Γ1 Γ2 x} (v : val' Γ1 x) (e : Γ1 ⊆ Γ2) :
  {i : Γ2 ∋ x & v_subst (from_BB (ugly_var ⊛ᵣ e)) (sub_elt x) v = ugly_var x i} ->
  {i : Γ1 ∋ x & v = ugly_var x i} .
  intros p; unfold val' in v.
  destruct p as [ i H ].
  destruct x as [ [ x | x ] p ]; cbn in *.
  all: dependent induction v; cbn in *; try now inversion H.
  all: exact (to_has_R h ,' f_equal _ (eq_sym (from_to_has_R h))).
Qed.

Lemma from_BB_comp {Γ1 Γ2 Γ3} (u : Γ2 =[ val' ]> Γ3) (v : Γ1 =[ val' ]> Γ2)
  : a_comp (from_BB u) (from_BB v) ≡ₐ from_BB (fun _ i => v_subst (from_BB u) _ (v _ i)) .
  reflexivity.
Qed.

Lemma ugly_comp_weird {Γ1 : neg_ctx} {Γ2 Γ3} (u : Γ2 =[ val' ]> Γ3) (v : ctx_s_to Γ1 =[ val' ]> Γ2)
  : a_comp (from_BB u) (from_FB v)
      ≡ₐ from_FB (fun _ i => v_subst (from_BB u) _ (v _ i)) .
  reflexivity.
Qed.

Definition to_nf {Γ} (u : nf (ctx_s_from Γ)) :
  { t : neg_ty & (Γ ∋ t * { m : pat (t_neg t) & ctx_s_to (pat_dom m) =[ val' ]> Γ })%type } :=
  (_ ,' (to_has_R (fst (projT2 u)) , (projT1 (snd (projT2 u)) ,' to_FB (projT2 (snd (projT2 u)))))) .

Program Definition mu_val : @Spec.lang_monoid mu_spec :=
  {| Spec.val := val' ;
     Spec.v_var := fun _ => ugly_var ;
     Spec.v_sub := fun _ _ a _ v => v_subst (from_BB a) _ v ;
  |}.

Program Definition mu_conf : @Spec.lang_module mu_spec mu_val :=
  {| Spec.conf := state' ;
     Spec.c_sub := fun _ _ a s => s_subst (from_BB a) s ;
  |}.

Program Definition mu_machine : @Spec.machine mu_spec mu_val mu_conf :=
  {| Spec.eval := fun _ c => fmap_delay to_nf (play c) ;
      Spec.app := fun _ _ v m r => p_app v m (from_FB r) |} .

Lemma mu_val_laws : @Spec.lang_monoid_laws mu_spec mu_val .
  unfold mu_spec, mu_val.
  econstructor; unfold Spec.e_comp, s_map; cbn in *.
  - intros Γ Δ u1 u2 H1 i v1 v2 H2.
    apply v_sub_eq; auto.
    now rewrite H1.
  - intros Γ1 Γ2 u ? i.
    etransitivity.
    unfold ugly_var, from_has_R; apply v_sub_id_r.
    unfold from_BB, from_has_F, r_to_from_l, s_elt_upg, ctx_s_from, to_has_R.
    destruct (ctx_s_to_inv Γ1); cbn.
    pose (xx := view_s_has_map (fun x : sigS is_neg => x) a0 i).
    fold xx; now destruct xx.
  - intros Γ1 Γ2 u ? i.
    etransitivity.
    apply v_sub_eq; [ apply from_BB_var | reflexivity ].
    apply v_sub_id_l.
  - intros Γ1 Γ2 Γ3 Γ4 p q r ? i.
    rewrite v_sub_sub.
    apply v_sub_eq; auto.
Qed.

Lemma mu_conf_laws : @Spec.lang_module_laws mu_spec mu_val mu_conf .
  unfold mu_spec, mu_val, mu_conf.
  econstructor; unfold Spec.e_comp, s_map; cbn in *.
  - intros Γ Δ u1 u2 H1 s1 s2 H2.
    apply s_sub_eq; auto.
    now rewrite H1.
  - intros Γ c.
    rewrite from_BB_var.
    apply s_sub_id_l.
  - intros Γ1 Γ2 Γ3 u v c; cbn.
    rewrite s_sub_sub.
    apply s_sub_eq; auto.
Qed.

Lemma mu_var_laws : @Spec.var_assumptions mu_spec mu_val .
  unfold mu_spec, mu_val.
  econstructor; unfold Spec.is_var; cbn in *.
  - exact @ugly_var_inj.
  - exact @ugly_var_dec.
  - exact @ugly_is_var_ren.
Qed.

Definition substS {X : SProp} (P : X -> Type) (a b : X) : P a -> P b := fun p => p .

Lemma to_comp_eq {Γ} (u v : delay (nf (ctx_s_from Γ))) (H : u ≋ v) :
  @Spec.comp_eq mu_spec mu_val _ (fmap_delay to_nf u) (fmap_delay to_nf v) .
  unfold Spec.comp_eq, fmap_delay.
  eapply (fmap_eq (RX := fun _ => nf_eq)); auto.
  intros [] ? ?  H1.
  destruct x as [ x1 [ i1 [ m1 γ1 ] ] ].
  destruct y as [ x2 [ i2 [ m2 γ2 ] ] ].
  destruct H1 as [ H1 [ H2 [ H3 H4 ] ] ].
  cbn in *.
  revert i1 m1 γ1 H2 H3 H4; rewrite H1; clear H1 x1; intros i1 m1 γ1 H2 H3 H4; cbn in *.
  rewrite H2; clear H2 i1.
  revert γ1 H4; rewrite H3; clear H3 m1; intros γ1 H4; cbn in *.
  unshelve econstructor; auto; cbn.
  unshelve econstructor; auto; cbn.
  unshelve econstructor; auto; cbn.
  now rewrite H4.
Qed.

Definition from_pat {Γ : ctx neg_ty} : { x : neg_ty & (Γ ∋ x * pat (t_neg x))%type } -> pat' (ctx_s_from Γ) :=
  fun u => (_ ,' (from_has_R (fst (projT2 u)) , snd (projT2 u))) .

Definition to_pat {Γ : ctx neg_ty} : pat' (ctx_s_from Γ) -> { x : neg_ty & (Γ ∋ x * pat (t_neg x))%type } :=
  fun u => (_ ,' (to_has_R (fst (projT2 u)) , snd (projT2 u))) .
        

Definition mu_machine_laws : @Spec.machine_laws mu_spec mu_val mu_conf mu_machine.
  unfold mu_spec, mu_val, mu_conf.
  econstructor; unfold Spec.e_comp, s_map; cbn in *.
  - intros Γ x v m u1 u2 H.
    destruct x as [ [ t | t ] neg ]; cbn in *.
    + f_equal; apply t_sub_eq; [ now rewrite H | reflexivity ].
    + do 2 f_equal; apply v0_sub_eq; auto; now rewrite H.
  - intros Γ1 Γ2 x e v m r; cbn.
    destruct x as [ [t | t] neg]; cbn in *.
    + f_equal; rewrite t_sub_sub; apply t_sub_eq; auto.
    + do 2 f_equal; rewrite v0_sub_sub; apply v0_sub_eq; auto.
  - intros Γ Δ c e .
    unfold Spec.comp_eq, fmap_delay.
    etransitivity.
    unshelve eapply fmap_eq. 5: exact (clean_hyp c (from_BB e)).
    exact ((fun _ => to_nf)).
    intros ? u v ->; unshelve econstructor; auto.
    unfold bind_delay', then_play1.
    rewrite fmap_bind_com, bind_fmap_com.
    apply (proj1 (t_gfp (it_eq_map ∅ₑ (fun _ : T1 => Spec.nf_eq')) _ _ _)).
    eapply (it_eq_up2bind_t (eqᵢ _)); econstructor; auto.
    intros [] u v ->. 
    change (gfp _ _ ?a ?b) with (Spec.comp_eq a b).
    apply to_comp_eq.
    erewrite p_app_eq; auto.
    now rewrite <- (from_to_FB (projT2 (snd (projT2 v)))).
  - intros Γ u .
    unfold Spec.eval_to_msg, Spec.msg_of_nf', Spec.nf', Spec.nf_ty', Spec.nf_msg', Spec.nf_val', Spec.nf_var'.
    destruct u as [ x [ j [ m γ ] ] ] ; cbn in *.
    pose proof (eval_nf_ret ((x : ty) ,' (from_has_R j , (m ,' from_FB γ)))); cbn in H.
    apply to_comp_eq in H.
    rewrite H; clear H.
    unfold Spec.comp_eq; apply it_eq_unstep; cbn; econstructor.
    unshelve econstructor; auto; cbn.
    unshelve econstructor; auto; cbn.
    + exact (to_from_has_R _).
    + unshelve econstructor; auto; cbn.
      apply to_from_FB.
  - intros [ [ t H ] p ]; simpl in p.
    pose (u := (t ,' p) : { t : ty & pat (t_neg t) }); simpl in u.
    change t with (projT1 u) in H |- *.
    change p with (projT2 u).
    revert H.
    remember u; clear t p u Heqs.
    induction (eval_app_not_var s).
    intro H1.
    econstructor. intros y H2.
    eassert (H3 : _). refine (H0 ((projT1 y).(sub_elt) ,' projT2 y) _ ((projT1 y).(sub_prf))).
    * dependent elimination H2.
      cbn in *.
      unfold Spec.eval_to_msg in i0.
      destruct x as [ t m ]; cbn in *.
      unshelve econstructor.
      + clear - Γ ; exact (ctx_s_from Γ).
      + clear - v ; exact v.
      + clear - e ; exact (from_FB e).
      + exact (from_has_R i).
      + intros []; apply p; unfold Spec.is_var, Spec.v_var.
        apply (substS (fun u => {i1 : Γ ∋ {| sub_elt := t; sub_prf := u |} & v = ugly_var {| sub_elt := t; sub_prf := u |} i1}) ((ctx_s_from Γ).(sub_prf) _ x)).
        refine (to_has_R x ,' _).
        rewrite e0; unfold ugly_var; f_equal; symmetry.
        apply from_to_has_R.
      + cbn in *.
        eapply (fmap_eq (RY := eqᵢ _) (fun _ => from_pat) (fun _ => from_pat)) in i0; [ | intros ? ? ? ->; auto ].
        unfold fmap_delay in i0.
        rewrite 2 fmap_fmap_com in i0.
        transitivity (((fun (_ : T1) (x : nf (ctx_s_from Γ)) => from_pat (@Spec.msg_of_nf' mu_spec mu_val Γ (to_nf x))) <$>
        play (p_app v m (from_FB e)))).
        unfold fmap_delay.
        eapply fmap_eq; auto.
        ** intros [] n1 n2 H'; cbn.
           destruct n1 as [ x1 [ i1 [ m1 γ1 ]] ].
           destruct n2 as [ x2 [ i2 [ m2 γ2 ]] ].
           destruct H' as [ H2 [ H3 [ H4 _ ] ] ]; cbn in *.
           unfold Spec.msg_of_nf', pat_of_nf, from_pat; cbn.
           revert i1 m1 γ1 H3 H4; rewrite H2; clear H2 x1; intros i1 m1 γ1 H3 H4; cbn in H3,H4.
           now rewrite H3, H4, from_to_has_R.
        ** rewrite i0; clear.
           apply it_eq_unstep; cbn; econstructor; reflexivity.
    * clear - H3; cbn in H3.
      change ({| sub_elt := sub_elt (projT1 y); sub_prf := sub_prf (projT1 y) |}) with (projT1 y) in H3.
      assert (H4 : (projT1 y,' projT2 y) = y) ; [ | rewrite H4 in H3; exact H3 ].
      clear; destruct y; cbn in *.
      reflexivity.
Qed.

Definition sem_act (Δ Γ : neg_ctx) : Type :=
  @Spec.ogs_act mu_spec (ctx_s_to Δ) (∅ ▶ ctx_s_to Γ)%ctx .

Definition sem_pas (Δ Γ : neg_ctx) : Type :=
  @Spec.ogs_pas mu_spec (ctx_s_to Δ) (∅ ▶ ctx_s_to Γ)%ctx .

Definition interp_act {Δ Γ : neg_ctx} (c : state Γ) : sem_act Δ Γ :=
  @Spec.m_strat mu_spec mu_val mu_conf mu_machine (ctx_s_to Δ) (∅ ▶ ctx_s_to Γ)%ctx
    (@Spec.inj_init_act mu_spec mu_val mu_conf (ctx_s_to Δ) (ctx_s_to Γ)
       (rew <- [state ∘ coe_ctx] (ctx_s_from_to Γ) in c)) .

Definition interp_pas {Δ Γ : neg_ctx} (e : Γ =[val]> Δ) : sem_pas Δ Γ :=
  @Spec.m_stratp mu_spec mu_val mu_conf mu_machine (ctx_s_to Δ) (∅ ▶ ctx_s_to Γ)%ctx
    (@Spec.inj_init_pas mu_spec mu_val (ctx_s_to Δ) (ctx_s_to Γ)
      (to_FF e)) .

Notation "⟦ c ⟧ₐ" := (interp_act c) .
Notation "⟦ e ⟧ₚ" := (interp_pas e) .

Definition ogs_weq_act Δ {Γ} : relation (sem_act Δ Γ) := fun u v => u ≈ v .
Definition ogs_weq_pas {Δ Γ} : relation (sem_pas Δ Γ) := fun u v => forall m, u m ≈ v m .

Definition ogs_eq_act Δ {Γ} : relation (sem_act Δ Γ) := fun u v => u ≊ v .
Definition ogs_eq_pas {Δ Γ} : relation (sem_pas Δ Γ) := fun u v => forall m, u m ≊ v m .

Notation "u ≈[ Δ ]≈ v" := (ogs_weq_act Δ u v) (at level 40).
Notation "u ≈ₚ v" := (ogs_weq_pas u v) (at level 40).
Notation "u ≊[ Δ ]≈ v" := (ogs_eq_act Δ u v) (at level 40).
Notation "u ≊ₚ v" := (ogs_eq_pas u v) (at level 40).

Definition eval_to_msg {Γ : neg_ctx} (c : state Γ) : delay (pat' Γ) :=
  fmap_delay (pat_of_nf Γ) (eval c) .

Definition ciu_eq (Δ : neg_ctx) {Γ} : relation (state Γ) :=
  fun u v => forall e : Γ =[val]> Δ, eval_to_msg (s_subst e u) ≈ eval_to_msg (s_subst e v) .

(*
Definition unuglify42 {Γ1 Γ2 : neg_ctx} (u : Γ1 =[val]> Γ2) : Prop.
  pose (uu := rew [fun u] unuglify4 (unuglify2 u)).
  rewrite 2 ctx_s_from_to in uu.
*)
Lemma foobar {Γ1 Γ2 Δ : neg_ctx} (c : state Γ1) (e : Γ1 =[val]> Δ) (H : Γ2 = Γ1) :
             s_subst (rew <- [fun xs : neg_ctx => xs =[val]> Δ] H in e) (rew <- [ fun xs : neg_ctx => state xs] H in c)
             = s_subst e c .
  now rewrite H.
  Qed.

(*
ogs_typ := stlc_typ + stlc_typ

conf Γ := {
    t : stlc_typ
    Γ' : list stlc_typ 
    ctx_in_ctx : map inj1 Γ' ⊆ Γ
    ret_in_ctx : inj2 t ∈ Γ
    term : stlc_term Γ' t
}
Inductive conf : list ogs_typ -> Type :=
| A {Γ Δ t} (u : stlc_term (Γ + Δ) t) -> conf (map inj1 Γ + inj2 t + map inj1 Δ)

CTX := list stlc_typ × opt (stlc_typ)
conf (Γ , Some t) := term Γ t
conf (Γ , None) := False

(Γ , t1) ++ (Δ , Some t2) = (Γ + Δ , t2)
(u , t0) (Γ , t1) ++ (Δ , None) = (Γ + Δ , t1)


c : conf (foobar_complique a b c d)
*)

Lemma from_to_has_FR {Γ a} (i : ctx_s_from (ctx_s_to Γ) ∋ a) : from_has_F (to_has_R i) = rew [ fun xs : neg_ctx => xs ∋ a ] ctx_s_from_to Γ in i .
  pose (H := ctx_s_from_to Γ); fold H.
  unfold from_has_F, to_has_R.
  unfold s_elt_upg. cbn in *.
  unfold ctx_s_from in *; cbn in *.

  assert (a_neg : is_neg a).
  exact ((ctx_s_from (ctx_s_to Γ)).(sub_prf) _ i).
  change ({| sub_elt := a; sub_prf := _|}) with {| sub_elt := a ; sub_prf := a_neg |}.
  revert i.
  pose (uu := ctx_s_to_inv (ctx_s_to Γ)).
  fold uu in H |- *.

 pose (vv := ctx_s_to Γ); fold vv in uu ,H |- *.

 remember H as H'; clear H HeqH'.
 remember uu; clear Heqf uu.
 rewrite <- H'.
 dependent induction f.
 apply ctx_s_to_inj in x0.
 revert x H'; rewrite x0; intros x H'. clear x0 a0.
 rewrite H'.
 Set Printing Implicit.
 
 dependent elimination x.
 destruct (ctx_s_to_inv vv).
 remember vv.
 dependent elimination H'.
 rewrite <- H'.
 

 revert H'.
 
 pose proof (ctx_s_from_to Γ).
 rewrite <- H in vv.
   in vv.
 destruct (ctx_s_to_inv vv).
 cbn in *.
 dependent elimination H'.

  revert i; rewrite <- H.
  remember (ctx_s_to Γ).
  dependent elimination H



  
  remember (ctx_s_to Γ).
  desturct (ctx_s_to Γ).
  dependent elimination H.
  rewrite H.
  fold H
  revert i; rewrite -> (ctx_s_from_to Γ).
  unfold from_has_F, to_has_R; cbn.

  destruct (ctx_s_from_to Γ).

Theorem mu_correction (Δ : neg_ctx) {Γ : neg_ctx} (x y : state Γ)
  : ⟦ x ⟧ₐ ≈[ Δ ]≈ ⟦ y ⟧ₐ -> ciu_eq Δ x y .
  intros H e.
  apply (@Spec.ogs_correction mu_spec mu_val mu_val_laws mu_conf mu_conf_laws
                 mu_var_laws mu_machine mu_machine_laws
                 (ctx_s_to Γ)
                 (ctx_s_to Δ)
                 (rew <- [state ∘ coe_ctx] (ctx_s_from_to Γ) in x)
                 (rew <- [state ∘ coe_ctx] (ctx_s_from_to Γ) in y)) in H.
  specialize (H (to_FF e)).
  
  unfold Spec.eval_in_env, Spec.eval_to_msg in H ; cbn in H.

  (*
  unshelve epose (u := _ : Δ ⊆ ctx_s_from (ctx_s_to Δ)).
    clear; intros ? i.
    unfold ctx_s_from.
    remember (ctx_s_to Δ).
    destruct (ctx_s_to_inv c).
    apply ctx_s_to_inj in Heqc.
    rewrite Heqc; exact i.
  cbn in u.
    clear -i .
*)

  assert (H1 : from_BB (to_FF e) ≡ₐ rew <- [fun xs : neg_ctx => xs =[val]> _] ctx_s_from_to Γ in (a_ren r_from_to_r e)).
  clear H; intros ? i; unfold from_BB, to_FF, to_FB, r_from_to_r; cbn.
  rewrite (ctx_s_from_to Δ); cbn.
  unfold a_ren at 1; rewrite v_ren_id_l.
  remember (ctx_s_from_to Γ) as H; clear HeqH.
  Check (from_has_F (to_has_R i)).
  unfold from_has_F, to_has_R; cbn in *.
  
  unfold ctx_s_from in *.
  pose (xx := ctx_s_to Γ).
  fold xx in i,H |- *.
  destruct (ctx_s_to_inv xx).
  destruct (ctx_s_to Γ).
  
  rewrite H.
  dependent elimination H.
  Check (from_BB (to_FF e)).

  unfold to_has_R, from_has_F, ctx_s_from_to; cbn [fib_extr].
  
  unfold ctx_s_to_inj.
  
  
  revert i; rewrite (ctx_s_from_to Γ).

  remember (ctx_s_to Γ).
  destruct (ctx_s_to_inv)
  Search r_id.

  cbn.
  rewrite (ctx_s_from_to Γ).
  unuglify4, unuglify2, a_comp, u; clear.
  unfold a_ren; cbn.
  pose (xx := (rew <- [fun xs : neg_ctx => xs =[ val ]> ctx_s_from (ctx_s_to Δ)] ctx_s_from_to Γ in
   (fun i0 : ty =>
    v_rename (fun (i2 : ty) (i3 : Δ ∋ i2) => rew <- [fun c : neg_ctx => c ∋ i2] ctx_s_from_to Δ in i3) i0
      ∘ e i0)) a i).
  pose (yy :=match
    view_s_has_map (fun x : sigS is_neg => x) Γ
      (match
         ctx_s_to_inv (ctx_s_to Γ) as f in (fiber _ b) return (forall i0 : fib_extr f ∋ a, b ∋ s_elt_upg i0)
       with
       | Fib a0 => fun i0 : fib_extr (Fib a0) ∋ a => s_map_has (fun x : sigS is_neg => x) a0 i0
       end i) in (s_has_map_view _ _ y h) return (val' (ctx_s_to Δ) y)
  with
  | @SHasMapV _ _ _ _ _ x i0 =>
      rew <- [fun c : ctx_s is_neg => val c (sub_elt (s_elt_upg i0))] ctx_s_from_to Δ in e x i0
  end).
  unfold val' in yy.
  change (?u = _) with (u = xx).
  change (_ = xx) with (yy = xx).
  admit.
  rewrite 2 (s_sub_eq _ _ H1 _ _ eq_refl) in H; clear H1.
  rewrite (ctx_s_from_to Γ) in H; cbn in H.
  unfold eval_to_msg.
  rewrite <- 2 s_ren_sub in H.
  pose proof (fmap_comp_eq (clean_hyp_ren (s_subst e x) u)).
  About clean_hyp_ren.
  About fmap_delay.
  About fmap.
  unfold fmap_delay in H.
  rewrite 2 fmap_fmap_com in H.
  fold fmap_delay in H.
  eapply fmap_eq in H.
  unfold Spec.msg_of_nf', Spec.nf', Spec.nf, Spec.nf_ty', Spec.nf_var', Spec.nf_msg' in H; cbn in H.
  unfold ugly_nf.
  cbn in H.
Admitted.
