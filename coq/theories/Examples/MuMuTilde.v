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

Lemma v_sub1_sub {Γ Δ a b} (f : Γ =[val]> Δ) (v : val Γ a) (w : val (Γ ▶ a) b)
  : v_subst (a_shift f) b w /ᵥ v_subst f a v = v_subst f b (w /ᵥ v) .
  unfold v_subst1; rewrite 2 v_sub_sub.
  apply v_sub_eq; auto.
  rewrite sub1_sub; reflexivity.
Qed.

Lemma s_sub1_sub {Γ Δ a} (f : Γ =[val]> Δ) (v : val Γ a) (s : state (Γ ▶ a))
  : s_subst (a_shift f) s /ₛ v_subst f a v = s_subst f (s /ₛ v) .
  unfold s_subst1; rewrite 2 s_sub_sub, sub1_sub; reflexivity.
Qed.

Lemma t_sub1_sub {Γ Δ a b} (f : Γ =[val]> Δ) (v : val Γ a) (t : term (Γ ▶ a) b)
  : t_subst (a_shift f) b t /ₜ v_subst f a v = t_subst f b (t /ₜ v) .
  unfold t_subst1; rewrite 2 t_sub_sub.
  apply t_sub_eq; auto.
  rewrite sub1_sub; reflexivity.
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

Definition unuglify1 {Γ1 : neg_ctx} {Γ2} (u : Γ1 =[val]> ctx_s_from Γ2) : ctx_s_to Γ1 =[val']> Γ2 .
  intros ? i; destruct (view_s_has_map _ _ i); exact (u _ i).
Defined.

#[global] Instance unuglify1_proper {Γ1 Γ2} : Proper (ass_eq _ _ ==> ass_eq _ _) (@unuglify1 Γ1 Γ2).
  intros u1 u2 H ? i.
  unfold unuglify1.
  destruct (view_s_has_map _ _ i); exact (H _ i).
Qed.

Definition unuglify1_inv {Γ1 : neg_ctx} {Γ2} (u : ctx_s_to Γ1 =[val']> Γ2) : Γ1 =[val]> ctx_s_from Γ2 .
  intros ? i; exact (u _ (s_map_has _ _ i)).
Defined.

Lemma unuglify11 {Γ1 : neg_ctx} {Γ2} (u : ctx_s_to Γ1 =[val']> Γ2) : unuglify1 (unuglify1_inv u) ≡ₐ u .
  intros ? i.
  unfold unuglify1, unuglify1_inv.
  pose (xx := view_s_has_map (fun x : sigS is_neg => x) Γ1 i).
  change (view_s_has_map (fun x : sigS is_neg => x) Γ1 i) with xx.
  now destruct xx.
Qed.

Definition unuglify2 {Γ1 Γ2 : neg_ctx} (u : Γ1 =[val]> Γ2) : ctx_s_to Γ1 =[val']> ctx_s_to Γ2 .
  intros ? i; destruct (view_s_has_map _ _ i).
  unfold val'; rewrite ctx_s_from_to.
  exact (u _ i).
Defined.

Definition unuglify3 {Γ1 Γ2} (u : ctx_s_from Γ1 =[val]> ctx_s_from Γ2) : Γ1 =[val']> Γ2.
  intros ? i.
  refine (unuglify1 u _ _).
  clear u.
  unfold ctx_s_from.
  destruct (ctx_s_to_inv Γ1).
  exact i.
Defined.

#[global] Instance unuglify3_proper {Γ1 Γ2} : Proper (ass_eq _ _ ==> ass_eq _ _) (@unuglify3 Γ1 Γ2).
  intros u1 u2 H ? i.
  exact (unuglify1_proper _ _ H _ _).
Qed.

Definition unuglify4 {Γ1 Γ2} (u : Γ1 =[val']> Γ2) : ctx_s_from Γ1 =[val]> ctx_s_from Γ2 .
  intros ? i.
  refine (u (s_elt_upg i) _); clear u.
  unfold ctx_s_from in *; destruct (ctx_s_to_inv Γ1); cbn in *.
  exact (s_map_has _ _ i).
Defined.

#[global] Instance unuglify4_proper {Γ1 Γ2} : Proper (ass_eq _ _ ==> ass_eq _ _) (@unuglify4 Γ1 Γ2).
  intros u1 u2 H ? i.
  exact (H (s_elt_upg i) _).
Qed.

Lemma unuglify34 {Γ1 Γ2} (u : Γ1 =[val']> Γ2) : unuglify3 (unuglify4 u) ≡ₐ u .
  intros ? i.
  unfold unuglify4, unuglify3, unuglify1.
  unfold ctx_s_from.
  destruct (ctx_s_to_inv Γ1); cbn.
  now destruct (view_s_has_map _ _ i).
Qed.

Lemma unuglify43 {Γ1 Γ2} (u : ctx_s_from Γ1 =[val]> ctx_s_from Γ2) : unuglify4 (unuglify3 u) ≡ₐ u .
  revert u; unfold unuglify3, unuglify4, unuglify1, ctx_s_from.
  intros u ? i.
  destruct (ctx_s_to_inv Γ1); cbn in *.
  pose (xx := view_s_has_map (fun x => x) a0 (s_map_has (fun x => x) a0 i)).
  change (view_s_has_map _ a0 _) with xx.
  remember xx; unfold xx in Heqs.
  rewrite (eq_trans Heqs s_has_map_view_simpl).
  reflexivity.
Qed.

(*
Lemma unuglify4_inj {Γ1 Γ2} (u v : Γ1 =[val']> Γ2) : unuglify4 u ≡ₐ unuglify4 v -> u ≡ₐ v .
  intro H.
  apply unuglify3_
*)


(*
Definition unuglify2 {Γ1 : neg_ctx} {Γ2} (u : Γ1 =[val]> ctx_from Γ2) : ctx_to Γ1 =[val']> Γ2 .
  intros ? i; destruct (view_s_has_map _ _ i); exact (u _ i).
Defined.

Definition ugly_ass_1 {Γ} {x : neg_ty} (m : pat (t_neg (sub_elt x)))
          (s : pat_dom m =[ val ]> ctx_from Γ)
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
*)

Definition clean_var {Γ : neg_ctx} {t} (i : ctx_s_to Γ ∋ t) : Γ ∋ t.(sub_elt) :=
  match view_s_has_map _ _ i in (s_has_map_view _ _ y h) return (Γ ∋ sub_elt y) with
  | SHasMapV j => j
  end .

Definition ugly_has {Γ} (t : neg_ty) (i : Γ ∋ t) : ctx_s_from Γ ∋ sub_elt t .
  unfold ctx_s_from; destruct (ctx_s_to_inv Γ); cbn in *.
  exact (clean_var i).
Defined.

Definition ugly_var {Γ} : Γ =[val']> Γ := fun _ i => Var _ (ugly_has _ i) .

Lemma fib_inj_irr {X Y} (f : X -> Y) (H : forall x y, f x = f y -> x = y) {y} (a b : fiber f y) : a = b .
  destruct b.
  dependent induction a.
  apply H in x0; rewrite x0 in x.
  apply (JMeq_eq_dep _ eq_refl) in x.
  now dependent induction x.
Qed.

Lemma ctx_s_to_inv_simpl {Γ : neg_ctx} : ctx_s_to_inv (ctx_s_to Γ) = Fib Γ .
  apply (fib_inj_irr _ (@ctx_s_to_inj _ _)).
Qed.

Lemma ugly4_id {Γ} : unuglify4 (@ugly_var Γ) ≡ₐ Var .
  unfold unuglify4, unuglify3, unuglify1, ctx_s_from in *.
  intros ? i.
  unfold ugly_var, ugly_has, clean_var.
  (*
  unfold view_s_has_map.
  unfold s_elt_upg.
  cbn in *.
  unfold view_s_has_map_clause_1.
  unfold s_map_has.
*)
  f_equal.
  destruct (ctx_s_to_inv Γ); cbn in *.
  pose (xx := view_s_has_map (fun x => x) a0 (s_map_has (fun x => x) a0 i)).
  change (view_s_has_map _ _ _) with xx.
  remember xx; unfold xx in Heqs; clear xx.
  rewrite (eq_trans Heqs s_has_map_view_simpl).
  reflexivity.
Qed.

Lemma ugly_var_inj {Γ x} (i j : Γ ∋ x) : ugly_var x i = ugly_var x j -> i = j .
  intro H.
  unfold ugly_var, ugly_has,clean_var in H.
  apply var_inj in H.
  pose (xx := ctx_s_to_inv Γ).
  fold xx in H.
  dependent induction xx.
  change (sigS _) with neg_ty in H. 
  (* >> !!!! rewrite is borked *)
  eassert (H' : _) by exact (@eq_ind (fiber ctx_s_to (ctx_s_to a)) (ctx_s_to_inv (ctx_s_to a))
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
  clear H x xx0; cbn in H'.
  (* << !!!! rewrite is borked *)

  destruct (view_s_has_map (fun x : neg_ty => x) _ i).

  rewrite H'.
  clear H'.
  fold is_neg in j.
  unfold s_elt_upg in *.

  (* >> !!!! remember is borked *)

  revert j.
  refine (((fun p => _) : forall (p : is_neg x) (j : @ctx_s_to ty is_neg a ∋ {| sub_elt := x; sub_prf := p |}),
  @s_map_has ty is_neg neg_ty (fun x0 : neg_ty => x0) a x
    match
      @view_s_has_map ty is_neg neg_ty (fun x0 : neg_ty => x0) a
        {| sub_elt := x; sub_prf := p |} j in (s_has_map_view _ _ y h)
      return (a ∋ @sub_elt _ _ y)
    with
    | SHasMapV j0 => j0
    end = j

          ) (sub_prf a x i)).
  cbn in *; clear i.
  intro j.
  pose (xx := view_s_has_map (fun x0 : neg_ty => x0) a j); fold xx.
  dependent induction xx.
  clear xx0.
  pose (xx := view_s_has_map (fun x1 : neg_ty => x1) a (s_map_has (fun x1 : sigS is_neg => x1) a i)).
  change (view_s_has_map _ _ _) with xx in x.
  change (view_s_has_map _ _ _) with xx.

  (* >> !!!! remember is borked *)

  (* >> !!!! rewrite is still borked *)
  exact (@eq_ind (s_has_map_view (fun x1 : neg_ty => x1) a (s_elt_upg i) (s_map_has (fun x1 : sigS is_neg => x1) a i)) (SHasMapV i) (fun uu =>
  s_map_has (fun x1 : sigS is_neg => x1) a
    match uu in (s_has_map_view _ _ y0 h) return (a ∋ sub_elt y0) with
    | SHasMapV j => j
    end = s_map_has (fun x1 : sigS is_neg => x1) a i) eq_refl _ x).
  (* << !!!! rewrite is still borked *)
  Qed.

Lemma ugly4_comp {Γ1 Γ2 Γ3} (u : Γ2 =[ val' ]> Γ3) (v : Γ1 =[ val' ]> Γ2)
  : a_comp (unuglify4 u) (unuglify4 v)
      ≡ₐ unuglify4 (fun _ i => v_subst (unuglify4 u) _ (v _ i)) .
  reflexivity.
Qed.

#[global] Instance ugly1_inv_proper {Γ1 : neg_ctx} {Γ2} : Proper (ass_eq _ _ ==> ass_eq _ _) (@unuglify1_inv Γ1 Γ2).
  intros u1 u2 H ? i.
  apply (H _ (s_map_has _ _ i)).
Qed.

Lemma ugly_comp_weird {Γ1 : neg_ctx} {Γ2 Γ3} (u : Γ2 =[ val' ]> Γ3) (v : ctx_s_to Γ1 =[ val' ]> Γ2)
  : a_comp (unuglify4 u) (unuglify1_inv v)
      ≡ₐ unuglify1_inv (fun _ i => v_subst (unuglify4 u) _ (v _ i)) .
  reflexivity.
Qed.

Definition ugly_nf {Γ} (u : nf (ctx_s_from Γ)) :
  {t : neg_ty & (Γ ∋ t * {m : pat (t_neg t) & ctx_s_to (pat_dom m) =[ val' ]> Γ})%type} .
  destruct u as [ x [ i [ p e ] ] ]; cbn in e.
  refine (s_elt_upg i ,' (_ , (p ,' unuglify1 e))).
  clear -i .
  unfold ctx_s_from in *.
  destruct (ctx_s_to_inv Γ); exact (s_map_has _ _ i).
Defined.

Program Definition mu_val : @Spec.lang_monoid mu_spec :=
  {| Spec.val := val' ;
     Spec.v_var := fun _ => ugly_var ;
     Spec.v_sub := fun _ _ a _ v => v_subst (unuglify4 a) _ v ;
  |}.

Program Definition mu_conf : @Spec.lang_module mu_spec mu_val :=
  {| Spec.conf := state' ;
     Spec.c_sub := fun _ _ a s => s_subst (unuglify4 a) s ;
  |}.

Program Definition mu_machine : @Spec.machine mu_spec mu_val mu_conf :=
  {| Spec.eval := fun _ c => fmap_delay (@ugly_nf _) (play c) ;
      Spec.app := fun _ _ v m r => (p_app v m (unuglify1_inv r)) |} .

Lemma mu_val_laws : @Spec.lang_monoid_laws mu_spec mu_val .
  unfold mu_spec, mu_val.
  econstructor; unfold Spec.e_comp, s_map; cbn in *.
  - intros Γ Δ u1 u2 H1 i v1 v2 H2.
    apply v_sub_eq; auto.
    now rewrite H1.
  - intros Γ1 Γ2 u ? i.
    etransitivity.
    unfold ugly_var, ugly_has; apply v_sub_id_r.
    unfold unuglify4, clean_var, s_elt_upg, ctx_s_from.
    destruct (ctx_s_to_inv Γ1); cbn.
    pose (xx := view_s_has_map (fun x : sigS is_neg => x) a0 i).
    fold xx; now destruct xx.
  - intros Γ1 Γ2 u ? i.
    etransitivity.
    apply v_sub_eq; [ apply ugly4_id | reflexivity ].
    apply v_sub_id_l.
  - intros Γ1 Γ2 Γ3 Γ4 p q r ? i.
    rewrite v_sub_sub.
    apply v_sub_eq; [ | reflexivity ].
    apply ugly4_comp.
Qed.

Lemma mu_conf_laws : @Spec.lang_module_laws mu_spec mu_val mu_conf .
  unfold mu_spec, mu_val, mu_conf.
  econstructor; unfold Spec.e_comp, s_map; cbn in *.
  - intros Γ Δ u1 u2 H1 s1 s2 H2.
    apply s_sub_eq; auto.
    now rewrite H1.
  - intros Γ c.
    rewrite ugly4_id.
    apply s_sub_id_l.
  - intros Γ1 Γ2 Γ3 u v c; cbn.
    rewrite s_sub_sub.
    apply s_sub_eq; [ | reflexivity ].
    apply ugly4_comp.
Qed.

Lemma mu_var_laws : @Spec.var_assumptions mu_spec mu_val .
  unfold mu_spec, mu_val.
  econstructor; unfold Spec.is_var; cbn in *.
  - exact @ugly_var_inj.
  - intros Γ x v.
    destruct (is_var_dec v); [ apply inl | apply inr ].
    + unfold ugly_var, ugly_has,clean_var.
      destruct i.
      unfold val' in v.
      unfold ctx_s_from in *.
      unshelve econstructor.
      * clear e. destruct (ctx_s_to_inv Γ).
        cbn in x0.
        exact (s_map_has _ _ x0).
      * refine (eq_trans e _).
        f_equal.
        clear e.
        destruct (ctx_s_to_inv Γ); cbn.
        pose (xx := view_s_has_map (fun x1 : sigS is_neg => x1) a (s_map_has (fun x1 : sigS is_neg => x1) a x0)).
        change (view_s_has_map _ _ _) with xx.
        eassert (H : _) by exact (s_has_map_view_simpl (f := fun x : neg_ty => x) (i:=x0)).
        change (view_s_has_map _ _ _) with xx in H.
        rewrite H.
        reflexivity.
    + intros [].
      unfold ugly_var,ugly_has in e.
      pose (j := (match ctx_s_to_inv Γ as f in (fiber _ b) return (b ∋ x -> fib_extr f ∋ sub_elt x) with
         | Fib a => fun i : ctx_s_to a ∋ x => clean_var i
         end x0)).
      change (v = Var _ _) with (v = Var _ j) in e.
      apply f.
      unshelve econstructor.
      exact j.
      exact e.
  - intros Γ1 Γ2 x v e p; unfold val' in v.
    destruct p as [ i H ].
    destruct x as [ [ x | x ] p ]; cbn in *.
    + dependent induction v; cbn in *; try now inversion H.
      clear H e.
      unfold ctx_s_from in h.
      unfold ugly_has.
      unshelve econstructor.
      destruct (ctx_s_to_inv Γ1).
      exact (s_map_has _ _ h).
      f_equal.
      unfold clean_var.
      destruct (ctx_s_to_inv Γ1).
      cbn -[ s_map_has].
      eassert (H : _) by exact (s_has_map_view_simpl (f := fun x : neg_ty => x) (i := h)).
      pose (xx := view_s_has_map (fun x : sigS is_neg => x) a0 (s_map_has (fun x : sigS is_neg => x) a0 h)).
      change (view_s_has_map _ _ _) with xx in H |- *.
      rewrite H.
      reflexivity.
    + dependent induction v; cbn in *; try now inversion H.
      clear H e.
      unfold ctx_s_from in h.
      unfold ugly_has.
      unshelve econstructor.
      destruct (ctx_s_to_inv Γ1).
      exact (s_map_has _ _ h).
      f_equal.
      unfold clean_var.
      destruct (ctx_s_to_inv Γ1).
      cbn -[ s_map_has].
      eassert (H : _) by exact (s_has_map_view_simpl (f := fun x : neg_ty => x) (i := h)).
      pose (xx := view_s_has_map (fun x : sigS is_neg => x) a (s_map_has (fun x : sigS is_neg => x) a h)).
      change (view_s_has_map _ _ _) with xx in H |- *.
      rewrite H.
      reflexivity.
Qed.

Definition mu_machine_laws : @Spec.machine_laws mu_spec mu_val mu_conf mu_machine.
  unfold mu_spec, mu_val, mu_conf.
  econstructor; unfold Spec.e_comp, s_map; cbn in *.
  - intros Γ x v m u1 u2 H.
    destruct x as [ [t | t] neg]; cbn in *.
    + f_equal. apply t_sub_eq; [ now rewrite H | reflexivity ].
    + do 2 f_equal.
      apply v0_sub_eq; [ | reflexivity ].
      now rewrite H.
  - intros Γ1 Γ2 x e v m r; cbn.
    destruct x as [ [t | t] neg]; cbn in *.
    + f_equal.
      rewrite t_sub_sub.
      apply t_sub_eq; [ | reflexivity ].
      now rewrite ugly_comp_weird.
    + do 2 f_equal.
      rewrite v0_sub_sub.
      apply v0_sub_eq; [ | reflexivity ].
      now rewrite ugly_comp_weird.
  - intros Γ Δ c e .
    eassert (H : _) by exact (clean_hyp c (unuglify4 e)).
    Check (Spec.eval_to_msg_eq _ _ H).

    rewrite H.
    rewrite H.
    Search bind_delay.
    unfold fmap_delay at 2, bind_delay.
    rewrite 
    unfold it_eq; revert c e H; coinduction R CIH; intros c e H.
    apply it_eq_step in H.
    cbn in *.
    pose (xx := eval_aux (s_subst (unuglify4 e) c)).
    change (eval_aux (s_subst (unuglify4 e) c)) with xx in H |- *.
    pose (yy := eval_aux c); change (eval_aux c) with yy in H |- * .
    destruct xx; destruct yy; cbn in *.
    * dependent elimination H; econstructor.
      econstructor.
  - intros Γ u .
    unfold Spec.eval_to_msg, Spec.msg_of_nf', Spec.nf', Spec.nf_ty', Spec.nf_msg', Spec.nf_val', Spec.nf_var'.
    destruct u as [ x [ j [ m γ ] ] ] ; cbn in *.
    eassert (H : _) by exact (eval_nf_ret ((x : ty) ,' (ugly_has _ j , (m ,' unuglify1_inv γ)))).
    cbn in *.
    unfold Spec.comp_eq; unfold comp_eq in H; apply it_eq_step in H.
    apply it_eq_unstep.
    cbn in *.
    change ((Var x (ugly_has x j))) with (ugly_var x j) in H.
    pose (xx := eval_aux (p_app (ugly_var x j) m (unuglify1_inv γ))).
    change (eval_aux (p_app _ _ _)) with xx in H |- *.
    destruct xx; dependent elimination H.
    econstructor.
    destruct r1 as [ x' [ j' [ m' γ' ] ] ] ; cbn in *.
    destruct r_rel as [ p [ q r ] ] ; cbn in *.
    unfold Spec.nf_eq'; cbn.
    revert j' m' γ' q r; rewrite p; clear p x'; intros j' m' γ' q r; cbn in q,r.
    rewrite q; clear q j'.
    destruct r as [ p q ]; cbn in p,q.
    revert γ' q; rewrite p; clear p m'; intros γ' q; cbn in q.
    pose (H2 := fun (U : SProp) (a b : U) => (eq_refl : a = b)); cbn in H2.
    unshelve econstructor; [ | split ].
    + unfold s_elt_upg, ugly_has.
      change x with ({| sub_elt := sub_elt x ; sub_prf := sub_prf x |}) at 7.
      f_equal.
    + cbn.
      unfold ugly_has, clean_var.
      clear .
      destruct (ctx_s_to_inv Γ).
      now destruct (view_s_has_map (fun x0 : sigS is_neg => x0) a j).
    + unshelve econstructor; auto; cbn.
      now rewrite q, unuglify11.
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
      + clear - e ; exact (unuglify1_inv e).
      + clear - i ; unfold ctx_s_from; destruct (ctx_s_to_inv Γ); exact (clean_var i).
      + intros [].
        apply p.
        clear - e0 .
        unfold val' in v.
        unfold ctx_s_from in *; cbn in *.
        unfold Spec.is_var.
        cbn.
        rewrite e0; clear e0.
        unfold ugly_var; cbn.
        pose (H2 := fun (U : SProp) (a b : U) => (eq_refl : a = b)); cbn in H2.
        unfold ugly_has.
        rewrite (H2 _ H1 ((fib_extr (ctx_s_to_inv Γ)).(sub_prf) _ x)).
        unshelve econstructor.
        ++ clear - x H2.
           destruct (ctx_s_to_inv Γ); exact (s_map_has (fun x => x) _ x).
        ++ unfold ugly_has, clean_var; f_equal; cbn.
           destruct (ctx_s_to_inv Γ).
           unfold view_s_has_map.
           unfold view_s_has_map_clause_1.
           pose (H3 := s_has_map_view_simpl' (f := fun x0 : sigS is_neg => x0) (ΓH := sub_prf a) (i := x)).
           pose (xx := view_s_has_map' (fun x0 : sigS is_neg => x0) (sub_elt a) (sub_prf a)
        (s_map_has' (fun x0 : sigS is_neg => x0) (sub_elt a) (sub_prf a) x)).
           change (view_s_has_map' _ _ _ _) with xx in H3 |- *.
           rewrite H3.
           reflexivity.
      + cbn in *.
        clear - i0.
        apply it_eq_step in i0.
        apply it_eq_unstep.
        cbn in *.
        pose (xx := eval_aux (p_app v m (unuglify1_inv e))).
        change (eval_aux (p_app v m (unuglify1_inv e))) with xx in i0 |- *.
        destruct xx; dependent elimination i0.
        econstructor.
        clear - r_rel.
        destruct n as [ x [ j [ m γ ] ] ] .
        unfold Spec.msg_of_nf', Spec.nf_ty', Spec.nf_val', Spec.nf_var', Spec.nf_msg' in r_rel.
        unfold ugly_nf in r_rel.
        unfold pat_of_nf.
        cbn in *.
        destruct y as [ t m' ]; cbn in *.
        inversion r_rel.
        unfold s_elt_upg in *.
        unfold ctx_s_from in *.
        destruct (ctx_s_to_inv Γ).
        cbn in *.
        remember (sub_prf a x j); clear Heqi0.
        eassert (H2 : _) by exact (f_equal (fun a => sub_elt a) H0); cbn in H2.
        revert j m γ i0 r_rel H0 H1; rewrite H2; clear H2; intros j m γ i0 r_rel H0 H1.
        clear H0.
        f_equal.
        inversion r_rel; clear r_rel H1.
        f_equal.
        ++ unfold clean_var.
           dependent elimination H0.
           unfold view_s_has_map.
           unfold view_s_has_map_clause_1.
           pose (H3 := s_has_map_view_simpl' (f := fun x0 : sigS is_neg => x0) (ΓH := sub_prf a) (i := j)).
           pose (xx := view_s_has_map' (fun x0 : sigS is_neg => x0) (sub_elt a) (sub_prf a)
        (s_map_has' (fun x0 : sigS is_neg => x0) (sub_elt a) (sub_prf a) j)).
           change (view_s_has_map' _ _ _ _) with xx in H3 |- *.
           rewrite H3.
           reflexivity.
        ++ clear - H2; dependent elimination H2. reflexivity.
        *  clear - H3. cbn in H3.
           change ({| sub_elt := sub_elt (projT1 y); sub_prf := sub_prf (projT1 y) |}) with (projT1 y) in H3.
           assert (H4 : (projT1 y,' projT2 y) = y) ; [ | rewrite H4 in H3; exact H3 ].
           clear; destruct y; cbn in *.
           reflexivity.
Qed.
Admitted.

(*
Theorem mu_correction {Γ} Δ (x y : state Γ)
    : inj_init_act (Δ:=Δ) x ≈ₐ inj_init_act y -> ciu Δ x y.

*)
