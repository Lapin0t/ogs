From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.
From OGS.Ctx Require Import All Ctx Covering Subset.
From OGS.ITree Require Import Event ITree Eq Delay Structure Properties.
From OGS.OGS Require Import Soundness.
Set Equations Transparent.

Inductive pre_ty : Type :=
| Zer : pre_ty
| One : pre_ty
| Prod : pre_ty -> pre_ty -> pre_ty
| Sum : pre_ty -> pre_ty -> pre_ty
| Arr : pre_ty -> pre_ty -> pre_ty
.

(*| .. coq:: none |*)
Derive NoConfusion for pre_ty.
Declare Scope ty_scope.
Delimit Scope ty_scope with ty.
Bind Scope ty_scope with pre_ty.

(*||*)
Notation "`0" := (Zer) : ty_scope.
Notation "`1" := (One) : ty_scope.
Notation "A `× B" := (Prod A B) (at level 40) : ty_scope.
Notation "A `+ B" := (Sum A B) (at level 40) : ty_scope.
Notation "A `→ B" := (Arr A B) (at level 40) : ty_scope .

Variant ty : Type :=
| LTy : pre_ty -> ty
| RTy : pre_ty -> ty
.
Derive NoConfusion for ty.
Bind Scope ty_scope with ty.
#[global] Coercion LTy : pre_ty >-> ty.
#[global] Notation "↑ t" := (LTy t) (at level 5) : ty_scope .
#[global] Notation "¬ t" := (RTy t) (at level 5) : ty_scope .
Open Scope ty_scope.

Equations t_neg : ty -> ty :=
  t_neg ↑a := ¬a ;
  t_neg ¬a := ↑a .
Notation "a †" := (t_neg a) (at level 5) : ty_scope.

Definition t_ctx : Type := ctx ty.
Bind Scope ctx_scope with t_ctx.

Inductive term : t_ctx -> ty -> Type :=
| Val {Γ A} : whn Γ A -> term Γ ↑A
| Mu {Γ A} : state (Γ ▶ₓ ¬A) -> term Γ ↑A

| VarR {Γ A} : Γ ∋ ¬A -> term Γ ¬A
| MuT {Γ A} : state (Γ ▶ₓ ↑A) -> term Γ ¬A

| Boom {Γ} : term Γ ¬`0
| Case {Γ A B} : state (Γ ▶ₓ ↑A) -> state (Γ ▶ₓ ↑B) -> term Γ ¬(A `+ B)

| Fst {Γ A B} : term Γ ¬A -> term Γ ¬(A `× B)
| Snd {Γ A B} : term Γ ¬B -> term Γ ¬(A `× B)
| App {Γ A B} : whn Γ A -> term Γ ¬B -> term Γ ¬(A `→ B)

with whn : t_ctx -> pre_ty -> Type :=
| VarL {Γ A} : Γ ∋ ↑A -> whn Γ A

| Inl {Γ A B} : whn Γ A -> whn Γ (A `+ B)
| Inr {Γ A B} : whn Γ B -> whn Γ (A `+ B)

| Tt {Γ} : whn Γ `1
| Pair {Γ A B} : state (Γ ▶ₓ ¬A) -> state (Γ ▶ₓ ¬B) -> whn Γ (A `× B)
| Lam {Γ A B} : state (Γ ▶ₓ ↑(A `→ B) ▶ₓ ↑A ▶ₓ ¬B) -> whn Γ (A `→ B)

with state : t_ctx -> Type :=
| Cut {Γ A} : term Γ ↑A -> term Γ ¬A -> state Γ
.

Definition Cut' {Γ A} : term Γ A -> term Γ A† -> state Γ
  := match A with
     | ↑_ => fun x y => Cut x y
     | ¬_ => fun x y => Cut y x
     end .

Equations val : t_ctx -> ty -> Type :=
  val Γ ↑A := whn Γ A ;
  val Γ ¬A := term Γ ¬A .

Equations Var Γ A : Γ ∋ A -> val Γ A :=
  Var _ ↑_ i := VarL i ;
  Var _ ¬_ i := VarR i .
Arguments Var {Γ} [A] i.

Equations t_of_v Γ A : val Γ A -> term Γ A :=
  t_of_v _ ↑_ v := Val v ;
  t_of_v _ ¬_ k := k .
Arguments t_of_v [Γ A] v.
Coercion t_of_v : val >-> term.

Equations t_rename : term ⇒₁ ⟦ c_var , term ⟧₁ :=
  t_rename _ _ (Mu c)     _ f := Mu (s_rename _ c _ (r_shift1 f)) ;
  t_rename _ _ (Val v)    _ f := Val (w_rename _ _ v _ f) ;
  t_rename _ _ (VarR i)   _ f := VarR (f _ i) ;
  t_rename _ _ (MuT c)    _ f := MuT (s_rename _ c _ (r_shift1 f)) ;
  t_rename _ _ (Boom)     _ f := Boom ;
  t_rename _ _ (App u k)  _ f := App (w_rename _ _ u _ f) (t_rename _ _ k _ f) ;
  t_rename _ _ (Fst k)    _ f := Fst (t_rename _ _ k _ f) ;
  t_rename _ _ (Snd k)    _ f := Snd (t_rename _ _ k _ f) ;
  t_rename _ _ (Case u v) _ f :=
    Case (s_rename _ u _ (r_shift1 f))
         (s_rename _ v _ (r_shift1 f))
with w_rename : whn ⇒₁ ⟦ c_var , val ⟧₁ :=
  w_rename _ _ (VarL i)   _ f := VarL (f _ i) ;
  w_rename _ _ (Tt)       _ f := Tt ;
  w_rename _ _ (Lam u)    _ f := Lam (s_rename _ u _ (r_shift3 f)) ;
  w_rename _ _ (Pair u v) _ f :=
    Pair (s_rename _ u _ (r_shift1 f))
         (s_rename _ v _ (r_shift1 f)) ;
  w_rename _ _ (Inl u)    _ f := Inl (w_rename _ _ u _ f) ;
  w_rename _ _ (Inr u)    _ f := Inr (w_rename _ _ u _ f)
with s_rename : state ⇒₀ ⟦ c_var , state ⟧₀ :=
   s_rename _ (Cut v k) _ f := Cut (t_rename _ _ v _ f) (t_rename _ _ k _ f) .

Equations v_rename : val ⇒₁ ⟦ c_var , val ⟧₁ :=
  v_rename _ ↑_ v _ f := w_rename _ _ v _ f ;
  v_rename _ ¬_ k _ f := t_rename _ _ k _ f .

Notation "t ₜ⊛ᵣ r" := (t_rename _ _ t _ r%asgn) (at level 14).
Notation "w `ᵥ⊛ᵣ r" := (w_rename _ _ w _ r%asgn) (at level 14).
Notation "v ᵥ⊛ᵣ r" := (v_rename _ _ v _ r%asgn) (at level 14).
Notation "s ₛ⊛ᵣ r" := (s_rename _ s _ r%asgn) (at level 14).

Definition a_ren {Γ1 Γ2 Γ3} : Γ1 =[val]> Γ2 -> Γ2 ⊆ Γ3 -> Γ1 =[val]> Γ3 :=
  fun f g _ i => v_rename _ _ (f _ i) _ g .
Arguments a_ren {_ _ _} _ _ _ _ /.
Notation "a ⊛ᵣ r" := (a_ren a r%asgn) (at level 14) : asgn_scope.

Definition t_shift1 {Γ A} : term Γ  ⇒ᵢ term (Γ ▶ₓ A) := fun _ t => t ₜ⊛ᵣ r_pop.
Definition w_shift1 {Γ A} : whn Γ   ⇒ᵢ whn (Γ ▶ₓ A)  := fun _ w => w `ᵥ⊛ᵣ r_pop.
Definition s_shift1 {Γ A} : state Γ -> state (Γ ▶ₓ A) := fun s => s ₛ⊛ᵣ r_pop.
Definition v_shift1 {Γ A} : val Γ   ⇒ᵢ val (Γ ▶ₓ A)  := fun _ v => v ᵥ⊛ᵣ r_pop.
Definition v_shift3 {Γ A B C} : val Γ ⇒ᵢ val (Γ ▶ₓ A ▶ₓ B ▶ₓ C)
  := fun _ v => v ᵥ⊛ᵣ (r_pop ᵣ⊛ r_pop ᵣ⊛ r_pop).
Definition a_shift1 {Γ Δ} [A] (a : Γ =[val]> Δ) : (Γ ▶ₓ A) =[val]> (Δ ▶ₓ A)
  := [ fun _ i => v_shift1 _ (a _ i) ,ₓ Var top ].
Definition a_shift3 {Γ Δ} [A B C] (a : Γ =[val]> Δ)
  : (Γ ▶ₓ A ▶ₓ B ▶ₓ C) =[val]> (Δ ▶ₓ A ▶ₓ B ▶ₓ C)
  := [ [ [ fun _ i => v_shift3 _ (a _ i) ,ₓ
           Var (pop (pop top)) ] ,ₓ
         Var (pop top) ] ,ₓ
       Var top ].

Equations t_subst : term ⇒₁ ⟦ val , term ⟧₁ :=
  t_subst _ _ (Mu c)     _ f := Mu (s_subst _ c _ (a_shift1 f)) ;
  t_subst _ _ (Val v)    _ f := Val (w_subst _ _ v _ f) ;
  t_subst _ _ (VarR i)   _ f := f _ i ;
  t_subst _ _ (MuT c)    _ f := MuT (s_subst _ c _ (a_shift1 f)) ;
  t_subst _ _ (Boom)     _ f := Boom ;
  t_subst _ _ (App u k)  _ f := App (w_subst _ _ u _ f) (t_subst _ _ k _ f) ;
  t_subst _ _ (Fst k)    _ f := Fst (t_subst _ _ k _ f) ;
  t_subst _ _ (Snd k)    _ f := Snd (t_subst _ _ k _ f) ;
  t_subst _ _ (Case u v) _ f :=
    Case (s_subst _ u _ (a_shift1 f))
          (s_subst _ v _ (a_shift1 f))
with w_subst : forall Γ A, whn Γ A -> forall Δ, Γ =[val]> Δ -> whn Δ A :=
  w_subst _ _ (VarL i)   _ f := f _ i ;
  w_subst _ _ (Tt)       _ f := Tt ;
  w_subst _ _ (Lam u)    _ f := Lam (s_subst _ u _ (a_shift3 f)) ;
  w_subst _ _ (Pair u v) _ f := Pair (s_subst _ u _ (a_shift1 f))
                                     (s_subst _ v _ (a_shift1 f)) ;
  w_subst _ _ (Inl u)    _ f := Inl (w_subst _ _ u _ f) ;
  w_subst _ _ (Inr u)    _ f := Inr (w_subst _ _ u _ f)
with s_subst : state ⇒₀ ⟦ val , state ⟧₀ :=
   s_subst _ (Cut v k) _ f := Cut (t_subst _ _ v _ f) (t_subst _ _ k _ f) .

Notation "t `ₜ⊛ a" := (t_subst _ _ t _ a%asgn) (at level 30).
Notation "w `ᵥ⊛ a" := (w_subst _ _ w _ a%asgn) (at level 30).

Equations v_subst : val ⇒₁ ⟦ val , val ⟧₁ :=
  v_subst _ ↑_ v _ f := v `ᵥ⊛ f ;
  v_subst _ ¬_ k _ f := k `ₜ⊛ f .

#[global] Instance val_monoid : subst_monoid val :=
  {| v_var := @Var ; v_sub := v_subst |} .
#[global] Instance state_module : subst_module val state :=
  {| c_sub := s_subst |} .

Definition asgn1 {Γ A} (v : val Γ A) : (Γ ▶ₓ A) =[val]> Γ
  := [ Var ,ₓ v ] .
Definition asgn3 {Γ A B C} (v1 : val Γ A) (v2 : val Γ B) (v3 : val Γ C)
  : (Γ ▶ₓ A ▶ₓ B ▶ₓ C) =[val]> Γ
  := [ [ [ Var ,ₓ v1 ] ,ₓ v2 ] ,ₓ v3 ].
Arguments asgn1 {_ _} & _.
Arguments asgn3 {_ _ _ _} & _ _.

Notation "₁[ v ]" := (asgn1 v).
Notation "₃[ v1 , v2 , v3 ]" := (asgn3 v1 v2 v3).

(*
Variant forcing0 (Γ : t_ctx) : pre_ty -> Type :=
| FBoom : forcing0 Γ Zer
| FApp {a b} : whn Γ a -> term Γ ¬b -> forcing0 Γ (a `→ b)
| FFst {a b} : term Γ ¬a -> forcing0 Γ (a `× b)
| FSnd {a b} : term Γ ¬b -> forcing0 Γ (a `× b)
| FCase {a b} : state (Γ ▶ₓ ↑a) -> state (Γ ▶ₓ ↑b) -> forcing0 Γ (a `+ b)
.
Arguments FBoom {Γ}.
Arguments FApp {Γ a b}.
Arguments FFst {Γ a b}.
Arguments FSnd {Γ a b}.
Arguments FCase {Γ a b}.

Equations f0_subst {Γ Δ} : Γ =[val]> Δ -> forcing0 Γ ⇒ᵢ forcing0 Δ :=
  f0_subst f a (FBoom)        := FBoom ;
  f0_subst f a (FApp v k)     := FApp (w_subst f _ v) (t_subst f _ k) ;
  f0_subst f a (FFst k)       := FFst (t_subst f _ k) ;
  f0_subst f a (FSnd k)       := FSnd (t_subst f _ k) ;
  f0_subst f a (FCase s1 s2) := FCase (s_subst (a_shift1 f) s1) (s_subst (a_shift1 f) s2) .

Equations forcing : t_ctx -> ty -> Type :=
  forcing Γ (t+ a) := whn Γ a ;
  forcing Γ (t- a) := forcing0 Γ a .

Equations f_subst {Γ Δ} : Γ =[val]> Δ -> forcing Γ ⇒ᵢ forcing Δ :=
  f_subst s (t+ a) v := w_subst s a v ;
  f_subst s (t- a) f := f0_subst s a f .
*)

Equations is_neg_pre : pre_ty -> SProp :=
  is_neg_pre `0       := sEmpty ;
  is_neg_pre `1       := sUnit ;
  is_neg_pre (_ `× _) := sUnit ;
  is_neg_pre (_ `+ _) := sEmpty ;
  is_neg_pre (_ `→ _) := sUnit .

Equations is_neg : ty -> SProp :=
  is_neg ↑a := is_neg_pre a ;
  is_neg ¬a := sUnit .

Definition neg_ty : Type := sigS is_neg.
Definition neg_coe : neg_ty -> ty := sub_elt.
Global Coercion neg_coe : neg_ty >-> ty.

Definition neg_ctx : Type := ctxS ty t_ctx is_neg.
Definition neg_c_coe : neg_ctx -> ctx ty := sub_elt.
Global Coercion neg_c_coe : neg_ctx >-> ctx.

Bind Scope ctx_scope with neg_ctx.
Bind Scope ctx_scope with ctx.

Inductive pat : ty -> Type :=
| PTt : pat ↑`1
| PPair {a b} : pat ↑(a `× b)
| PInl {a b} : pat ↑a -> pat ↑(a `+ b)
| PInr {a b} : pat ↑b -> pat ↑(a `+ b)
| PLam {a b} : pat ↑(a `→ b)
| PFst {a b} : pat ¬(a `× b)
| PSnd {a b} : pat ¬(a `× b)
| PApp {a b} : pat ↑a -> pat ¬(a `→ b)
.

Equations pat_dom {t} : pat t -> neg_ctx :=
  pat_dom (PInl u) := pat_dom u ;
  pat_dom (PInr u) := pat_dom u ;
  pat_dom (PTt) := ∅ₛ ▶ₛ {| sub_elt := ↑`1 ; sub_prf := stt |} ;
  pat_dom (@PLam a b) := ∅ₛ ▶ₛ {| sub_elt := ↑(a `→ b) ; sub_prf := stt |} ;
  pat_dom (@PPair a b) := ∅ₛ ▶ₛ {| sub_elt := ↑(a `× b) ; sub_prf := stt |} ;
  pat_dom (@PApp a b v) := pat_dom v ▶ₛ {| sub_elt := ¬b ; sub_prf := stt |} ;
  pat_dom (@PFst a b) := ∅ₛ ▶ₛ {| sub_elt := ¬a ; sub_prf := stt |} ;
  pat_dom (@PSnd a b) := ∅ₛ ▶ₛ {| sub_elt := ¬b ; sub_prf := stt |} .

Definition op_pat : Oper ty neg_ctx :=
  {| o_op a := pat a ; o_dom _ p := (pat_dom p) |} .

Definition op_copat : Oper ty neg_ctx :=
  {| o_op a := pat (t_neg a) ; o_dom _ p := (pat_dom p) |} .

Definition bare_copat := op_copat∙ .

Equations v_of_p {A} (p : pat A) : val (pat_dom p) A :=
  v_of_p (PInl u) := Inl (v_of_p u) ;
  v_of_p (PInr u) := Inr (v_of_p u) ;
  v_of_p (PTt) := VarL top ;
  v_of_p (PLam) := VarL top ;
  v_of_p (PPair) := VarL top ;
  v_of_p (PApp v) := App (v_shift1 _ (v_of_p v)) (VarR top) ;
  v_of_p (PFst) := Fst (VarR top) ;
  v_of_p (PSnd) := Snd (VarR top) .
Coercion v_of_p : pat >-> val.

Definition elim_var_zer {A : Type} {Γ : neg_ctx} (i : Γ ∋ ↑ `0) : A
  := match s_prf i with end .
Definition elim_var_sum {A : Type} {Γ : neg_ctx} {s t} (i : Γ ∋ ↑ (s `+ t)) : A
  := match s_prf i with end .

Equations p_of_w {Γ : neg_ctx} a : whn Γ a -> pat ↑a :=
  p_of_w (`0)     (VarL i) := elim_var_zer i ;
  p_of_w (a `+ b) (VarL i) := elim_var_sum i ;
  p_of_w (a `+ b) (Inl v)  := PInl (p_of_w _ v) ;
  p_of_w (a `+ b) (Inr v)  := PInr (p_of_w _ v) ;
  p_of_w (`1)     _        := PTt ;
  p_of_w (a `× b) _        := PPair ;
  p_of_w (a `→ b) _        := PLam .

Equations p_dom_of_w {Γ : neg_ctx} a (v : whn Γ a) : pat_dom (p_of_w a v) =[val]> Γ :=
  p_dom_of_w (`0)     (VarL i) := elim_var_zer i ;
  p_dom_of_w (a `+ b) (VarL i) := elim_var_sum i ;
  p_dom_of_w (a `+ b) (Inl v)  := p_dom_of_w a v ;
  p_dom_of_w (a `+ b) (Inr v)  := p_dom_of_w b v ;
  p_dom_of_w (`1)     v        := [ ! ,ₓ v ] ;
  p_dom_of_w (a `→ b) v        := [ ! ,ₓ v ] ;
  p_dom_of_w (a `× b) v        := [ ! ,ₓ v ] .

Program Definition w_split {Γ : neg_ctx} a (v : whn Γ a) : (op_copat # val) Γ ¬a
  := p_of_w _ v ⦇ p_dom_of_w _ v ⦈ .

Definition L_nf : Fam₀ ty neg_ctx := c_var ∥ₛ (op_copat # val ).

(*
Definition n_rename {Γ Δ : neg_ctx} : Γ ⊆ Δ -> L_nf Γ -> L_nf Δ
  := fun r n => r _ (nf_var n) ⋅ nf_obs n ⦇ a_ren r (nf_args n) ⦈.
*)

(*
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
*)

Program Definition app_nf {Γ : neg_ctx} {a b} (i : Γ ∋ ↑(a `→ b))
  (v : whn Γ a) (k : term Γ ¬b) : L_nf Γ
  := i ⋅ PApp (p_of_w _ v) ⦇ [ p_dom_of_w _ v ,ₓ (k : val _ ¬_) ] ⦈ .

Program Definition fst_nf {Γ : neg_ctx} {a b} (i : Γ ∋ ↑(a `× b))
  (k : term Γ ¬a) : L_nf Γ
  := i ⋅ PFst ⦇ [ ! ,ₓ (k : val _ ¬_) ] ⦈ .

Program Definition snd_nf {Γ : neg_ctx} {a b} (i : Γ ∋ ↑(a `× b))
  (k : term Γ ¬b) : L_nf Γ
  := i ⋅ PSnd ⦇ [ ! ,ₓ (k : val _ ¬_) ] ⦈ .

Equations eval_aux {Γ : neg_ctx} : state Γ -> (state Γ + L_nf Γ) :=
  eval_aux (Cut (Mu s)           (k))        := inl (s ₜ⊛ ₁[ k ]) ;
  eval_aux (Cut (Val v)          (MuT s))    := inl (s ₜ⊛ ₁[ v ]) ;

  eval_aux (Cut (Val v)          (VarR i))   := inr (s_var_upg i ⋅ w_split _ v) ;

  eval_aux (Cut (Val (VarL i))   (Boom))     := elim_var_zer i ;
  eval_aux (Cut (Val (VarL i))   (Case s t)) := elim_var_sum i ;

  eval_aux (Cut (Val (VarL i))   (App v k))  := inr (app_nf i v k) ;
  eval_aux (Cut (Val (VarL i))   (Fst k))    := inr (fst_nf i k) ;
  eval_aux (Cut (Val (VarL i))   (Snd k))    := inr (snd_nf i k) ;


  eval_aux (Cut (Val (Lam s))    (App v k))  := inl (s ₜ⊛ ₃[ Lam s , v , k ]) ;
  eval_aux (Cut (Val (Pair s t)) (Fst k))    := inl (s ₜ⊛ ₁[ k ]) ;
  eval_aux (Cut (Val (Pair s t)) (Snd k))    := inl (t ₜ⊛ ₁[ k ]) ;
  eval_aux (Cut (Val (Inl u))    (Case s t)) := inl (s ₜ⊛ ₁[ u ]) ;
  eval_aux (Cut (Val (Inr u))    (Case s t)) := inl (t ₜ⊛ ₁[ u ]) .

Definition eval {Γ : neg_ctx} : state Γ -> delay (L_nf Γ)
  := iter_delay (fun c => Ret' (eval_aux c)).

(*
Definition refold {Γ : neg_ctx} (p : nf Γ)
  : (Γ ∋ (projT1 p) * val Γ (t_neg (projT1 p)))%type.
destruct p as [x [i [ p s ]]]; cbn in *.
exact (i , v_subst s _ (v_of_p p)).
Defined.
*)

Definition p_app {Γ A} (v : val Γ A) (m : pat A†) (e : pat_dom m =[val]> Γ) : state Γ
  := Cut' v (m `ₜ⊛ e) .

(*
Definition emb {Γ} (m : pat' Γ) : state (Γ +▶ₓ pat_dom' Γ m) .
  destruct m as [a [i v]]; cbn in *.
  destruct a.
  - refine (Cut _ _).
    + refine (Val (VarL (r_concat_l _ i))).
    + refine (t_rename r_concat_r _ (v_of_p v)).
  - refine (Cut _ _).
    + refine (Val (v_rename r_concat_r _ (v_of_p v))).
    + refine (VarR (r_concat_l _ i)).
Defined.
*)

Scheme term_mut := Induction for term Sort Prop
  with whn_mut := Induction for whn Sort Prop
  with state_mut := Induction for state Sort Prop.

Record syn_ind_args (Pt : forall Γ A, term Γ A -> Prop)
                    (Pv : forall Γ A, whn Γ A -> Prop)
                    (Ps : forall Γ, state Γ -> Prop) :=
{
  ind_s_mu : forall Γ A s, Ps _ s -> Pt Γ ↑A (Mu s) ;
  ind_s_val : forall Γ A v, Pv _ _ v -> Pt Γ ↑A (Val v) ;
  ind_s_varn : forall Γ A i, Pt Γ ¬A (VarR i) ;
  ind_s_mut : forall Γ A s, Ps _ s -> Pt Γ ¬A (MuT s) ;
  ind_s_zer : forall Γ, Pt Γ ¬`0 Boom ;
  ind_s_app : forall Γ A B, forall v, Pv _ _ v -> forall k, Pt _ _ k -> Pt Γ ¬(A `→ B) (App v k) ;
  ind_s_fst : forall Γ A B, forall k, Pt _ _ k -> Pt Γ ¬(A `× B) (Fst k) ;
  ind_s_snd : forall Γ A B, forall k, Pt _ _ k -> Pt Γ ¬(A `× B) (Snd k) ;
  ind_s_match : forall Γ A B, forall s, Ps _ s -> forall t, Ps _ t -> Pt Γ ¬(A `+ B) (Case s t) ;
  ind_s_varp : forall Γ A i, Pv Γ A (VarL i) ;
  ind_s_inl : forall Γ A B v, Pv _ _ v -> Pv Γ (A `+ B) (Inl v) ;
  ind_s_inr : forall Γ A B v, Pv _ _ v -> Pv Γ (A `+ B) (Inr v) ;
  ind_s_onei : forall Γ, Pv Γ `1 Tt ;
  ind_s_lam : forall Γ A B s, Ps _ s -> Pv Γ (A `→ B) (Lam s) ;
  ind_s_pair : forall Γ A B, forall s, Ps _ s -> forall t, Ps _ t -> Pv Γ (A `× B) (Pair s t) ;
  ind_s_cut : forall Γ A, forall u, Pt _ _ u -> forall v, Pt _ _ v -> Ps Γ (@Cut _ A u v)
} .

Lemma term_ind_mut Pt Pv Ps (arg : syn_ind_args Pt Pv Ps) Γ A u : Pt Γ A u.
  destruct arg; now apply (term_mut Pt Pv Ps).
Qed.

Lemma whn_ind_mut Pt Pv Ps (arg : syn_ind_args Pt Pv Ps) Γ A v : Pv Γ A v.
  destruct arg; now apply (whn_mut Pt Pv Ps).
Qed.

Lemma state_ind_mut Pt Pv Ps (arg : syn_ind_args Pt Pv Ps) Γ s : Ps Γ s.
  destruct arg; now apply (state_mut Pt Pv Ps).
Qed.

Definition t_ren_proper_P Γ A (t : term Γ A) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> t ₜ⊛ᵣ f1 = t ₜ⊛ᵣ f2 .
Definition w_ren_proper_P Γ A (v : whn Γ A) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> v `ᵥ⊛ᵣ f1 = v `ᵥ⊛ᵣ f2 .
Definition s_ren_proper_P Γ (s : state Γ) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> s ₛ⊛ᵣ f1 = s ₛ⊛ᵣ f2 .
Lemma ren_proper_prf : syn_ind_args t_ren_proper_P w_ren_proper_P s_ren_proper_P.
  econstructor.
  all: unfold t_ren_proper_P, w_ren_proper_P, s_ren_proper_P.
  all: intros; cbn; f_equal; cbn; eauto.
  all: try now apply H.
  all: first [ apply H | apply H0 | apply H1 | apply H2 ]; auto.
  all: first [ apply r_shift1_eq | apply r_shift3_eq ]; auto.
Qed.

#[global] Instance t_ren_eq {Γ a t Δ} : Proper (asgn_eq _ _ ==> eq) (t_rename Γ a t Δ).
  intros f1 f2 H1; now apply (term_ind_mut _ _ _ ren_proper_prf).
Qed.

#[global] Instance w_ren_eq {Γ a v Δ} : Proper (asgn_eq _ _ ==> eq) (w_rename Γ a v Δ).
  intros f1 f2 H1; now apply (whn_ind_mut _ _ _ ren_proper_prf).
Qed.

#[global] Instance s_ren_eq {Γ s Δ} : Proper (asgn_eq _ _ ==> eq) (s_rename Γ s Δ).
  intros f1 f2 H1; now apply (state_ind_mut _ _ _ ren_proper_prf).
Qed.

#[global] Instance v_ren_eq {Γ a v Δ} : Proper (asgn_eq _ _ ==> eq) (v_rename Γ a v Δ).
  destruct a.
  now apply w_ren_eq.
  now apply t_ren_eq.
Qed.

#[global] Instance a_ren_eq {Γ1 Γ2 Γ3}
  : Proper (asgn_eq _ _ ==> asgn_eq _ _ ==> asgn_eq _ _) (@a_ren Γ1 Γ2 Γ3).
  intros r1 r2 H1 a1 a2 H2 ? i; cbn; now rewrite H1, (v_ren_eq _ _ H2).
Qed.

#[global] Instance a_shift1_eq {Γ Δ A} : Proper (asgn_eq _ _ ==> asgn_eq _ _) (@a_shift1 Γ Δ A).
  intros ? ? H ? h.
  dependent elimination h; auto; cbn; now rewrite H.
Qed.

#[global] Instance a_shift3_eq {Γ Δ A B C}
  : Proper (asgn_eq _ _ ==> asgn_eq _ _) (@a_shift3 Γ Δ A B C).
  intros ? ? H ? v.
  do 3 (dependent elimination v; auto).
  cbn; now rewrite H.
Qed.

Definition t_ren_ren_P Γ1 A (t : term Γ1 A) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 ⊆ Γ3),
    (t ₜ⊛ᵣ f1) ₜ⊛ᵣ f2 = t ₜ⊛ᵣ (f1 ᵣ⊛ f2) .
Definition w_ren_ren_P Γ1 A (v : whn Γ1 A) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 ⊆ Γ3),
    (v `ᵥ⊛ᵣ f1) `ᵥ⊛ᵣ f2 = v `ᵥ⊛ᵣ (f1 ᵣ⊛ f2) .
Definition s_ren_ren_P Γ1 (s : state Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 ⊆ Γ3),
    (s ₛ⊛ᵣ f1) ₛ⊛ᵣ f2 = s ₛ⊛ᵣ (f1 ᵣ⊛ f2) .

Lemma ren_ren_prf : syn_ind_args t_ren_ren_P w_ren_ren_P s_ren_ren_P.
  econstructor.
  all: unfold t_ren_ren_P, w_ren_ren_P, s_ren_ren_P.
  all: intros; cbn; f_equal; eauto.
  all: first [ rewrite r_shift1_comp | rewrite r_shift3_comp ]; eauto.
Qed.

Lemma t_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 ⊆ Γ3) A (t : term Γ1 A)
  : (t ₜ⊛ᵣ f1) ₜ⊛ᵣ f2 = t ₜ⊛ᵣ (f1 ᵣ⊛ f2) .
  now apply (term_ind_mut _ _ _ ren_ren_prf).
Qed.
Lemma w_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 ⊆ Γ3) A (v : whn Γ1 A)
  : (v `ᵥ⊛ᵣ f1) `ᵥ⊛ᵣ f2 = v `ᵥ⊛ᵣ (f1 ᵣ⊛ f2) .
  now apply (whn_ind_mut _ _ _ ren_ren_prf).
Qed.
Lemma s_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 ⊆ Γ3) (s : state Γ1)
  : (s ₛ⊛ᵣ f1) ₛ⊛ᵣ f2 = s ₛ⊛ᵣ (f1 ᵣ⊛ f2) .
  now apply (state_ind_mut _ _ _ ren_ren_prf).
Qed.
Lemma v_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 ⊆ Γ3) A (v : val Γ1 A)
  : (v ᵥ⊛ᵣ f1) ᵥ⊛ᵣ f2 = v ᵥ⊛ᵣ (f1 ᵣ⊛ f2) .
  destruct A.
  now apply w_ren_ren.
  now apply t_ren_ren.
Qed.

Definition t_ren_id_l_P Γ A (t : term Γ A) : Prop := t ₜ⊛ᵣ r_id = t.
Definition w_ren_id_l_P Γ A (v : whn Γ A) : Prop := v `ᵥ⊛ᵣ r_id = v.
Definition s_ren_id_l_P Γ (s : state Γ) : Prop := s ₛ⊛ᵣ r_id  = s.

Lemma ren_id_l_prf : syn_ind_args t_ren_id_l_P w_ren_id_l_P s_ren_id_l_P.
  econstructor.
  all: unfold t_ren_id_l_P, w_ren_id_l_P, s_ren_id_l_P.
  all: intros; cbn; f_equal; eauto.
  all: first [ rewrite r_shift1_id | rewrite r_shift3_id ]; eauto.
Qed.

Lemma t_ren_id_l {Γ} A (t : term Γ A) : t ₜ⊛ᵣ r_id = t.
  now apply (term_ind_mut _ _ _ ren_id_l_prf).
Qed.
Lemma w_ren_id_l {Γ} A (v : whn Γ A) : v `ᵥ⊛ᵣ r_id = v.
  now apply (whn_ind_mut _ _ _ ren_id_l_prf).
Qed.
Lemma s_ren_id_l {Γ} (s : state Γ) : s ₛ⊛ᵣ r_id  = s.
  now apply (state_ind_mut _ _ _ ren_id_l_prf).
Qed.
Lemma v_ren_id_l {Γ} A (v : val Γ A) : v ᵥ⊛ᵣ r_id = v.
  destruct A.
  now apply w_ren_id_l.
  now apply t_ren_id_l.
Qed.

Lemma v_ren_id_r {Γ Δ} (f : Γ ⊆ Δ) A (i : Γ ∋ A) : (Var i) ᵥ⊛ᵣ f = Var (f _ i).
  now destruct A.
Qed.

Lemma a_shift1_id {Γ A} : @a_shift1 Γ Γ A Var ≡ₐ Var.
  intros [ [] | [] ] i; dependent elimination i; auto.
Qed.

Lemma a_shift3_id {Γ A B C} : @a_shift3 Γ Γ A B C Var ≡ₐ Var.
  intros ? v; cbn.
  do 3 (dependent elimination v; cbn; auto).
  now destruct a.
Qed.

Arguments Var : simpl never.
Lemma a_shift1_ren_r {Γ1 Γ2 Γ3 A} (f1 : Γ1 =[ val ]> Γ2) (f2 : Γ2 ⊆ Γ3)
      : a_shift1 (A:=A) (f1 ⊛ᵣ f2) ≡ₐ a_shift1 f1 ⊛ᵣ r_shift1 f2 .
  intros ? h; dependent elimination h; cbn.
  - now rewrite v_ren_id_r.
  - now unfold v_shift1; rewrite 2 v_ren_ren.
Qed.

Lemma a_shift3_ren_r {Γ1 Γ2 Γ3 A B C} (f1 : Γ1 =[ val ]> Γ2) (f2 : Γ2 ⊆ Γ3)
      : a_shift3 (A:=A) (B:=B) (C:=C) (f1 ⊛ᵣ f2) ≡ₐ a_shift3 f1 ⊛ᵣ r_shift3 f2 .
  intros ? v; do 3 (dependent elimination v; cbn; [ now rewrite v_ren_id_r | ]).
  unfold v_shift3; now rewrite 2 v_ren_ren.
Qed.

Lemma a_shift1_ren_l {Γ1 Γ2 Γ3 A} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val]> Γ3)
  : a_shift1 (A:=A) (f1 ᵣ⊛ f2) ≡ₐ r_shift1 f1 ᵣ⊛ a_shift1 f2 .
  intros ? i; dependent elimination i; auto.
Qed.

Lemma a_shift3_ren_l {Γ1 Γ2 Γ3 A B C} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val]> Γ3)
      : a_shift3 (A:=A) (B:=B) (C:=C) (f1 ᵣ⊛ f2) ≡ₐ r_shift3 f1 ᵣ⊛ a_shift3 f2 .
  intros ? v; do 3 (dependent elimination v; auto).
Qed.

Definition t_sub_proper_P Γ A (t : term Γ A) : Prop :=
  forall Δ (f1 f2 : Γ =[val]> Δ), f1 ≡ₐ f2 -> t `ₜ⊛ f1 = t `ₜ⊛ f2 .
Definition w_sub_proper_P Γ A (v : whn Γ A) : Prop :=
  forall Δ (f1 f2 : Γ =[val]> Δ), f1 ≡ₐ f2 -> v `ᵥ⊛ f1 = v `ᵥ⊛ f2 .
Definition s_sub_proper_P Γ (s : state Γ) : Prop :=
  forall Δ (f1 f2 : Γ =[val]> Δ), f1 ≡ₐ f2 -> s ₜ⊛ f1 = s ₜ⊛ f2 .

Lemma sub_proper_prf : syn_ind_args t_sub_proper_P w_sub_proper_P s_sub_proper_P.
  econstructor.
  all: unfold t_sub_proper_P, w_sub_proper_P, s_sub_proper_P.
  all: intros; cbn; f_equal.
  all: first [ apply H | apply H0 | apply H1 | apply H2 ]; auto.
  all: first [ apply a_shift1_eq | apply a_shift3_eq ]; auto.
Qed.

#[global] Instance t_sub_eq {Γ a t Δ} : Proper (asgn_eq _ _ ==> eq) (t_subst Γ a t Δ).
  intros f1 f2 H1; now apply (term_ind_mut _ _ _ sub_proper_prf).
Qed.

#[global] Instance w_sub_eq {Γ a v Δ} : Proper (asgn_eq _ _ ==> eq) (w_subst Γ a v Δ).
  intros f1 f2 H1; now apply (whn_ind_mut _ _ _ sub_proper_prf).
Qed.

#[global] Instance s_sub_eq {Γ s Δ} : Proper (asgn_eq _ _ ==> eq) (s_subst Γ s Δ).
  intros f1 f2 H1; now apply (state_ind_mut _ _ _ sub_proper_prf).
Qed.

#[global] Instance v_sub_eq {Γ a v Δ} : Proper (asgn_eq _ _ ==> eq) (v_subst Γ a v Δ).
  destruct a.
  - now apply w_sub_eq.
  - now apply t_sub_eq.
Qed.

#[global] Instance a_comp_eq {Γ1 Γ2 Γ3}
  : Proper (asgn_eq _ _ ==> asgn_eq _ _ ==> asgn_eq _ _) (@a_comp _ _ _ _ _ Γ1 Γ2 Γ3).
  intros ? ? H1 ? ? H2 ? ?; cbn; rewrite H1; now eapply v_sub_eq.
Qed.

Definition t_ren_sub_P Γ1 A (t : term Γ1 A) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 ⊆ Γ3),
    (t `ₜ⊛ f1) ₜ⊛ᵣ f2 = t `ₜ⊛ (f1 ⊛ᵣ f2) .
Definition w_ren_sub_P Γ1 A (v : whn Γ1 A) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 ⊆ Γ3),
    (v `ᵥ⊛ f1) `ᵥ⊛ᵣ f2 = v `ᵥ⊛ (f1 ⊛ᵣ f2) .
Definition s_ren_sub_P Γ1 (s : state Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 ⊆ Γ3),
    (s ₜ⊛ f1) ₛ⊛ᵣ f2 = s ₜ⊛ (f1 ⊛ᵣ f2) .
Lemma ren_sub_prf : syn_ind_args t_ren_sub_P w_ren_sub_P s_ren_sub_P.
  econstructor.
  all: unfold t_ren_sub_P, w_ren_sub_P, s_ren_sub_P.
  all: intros; cbn; f_equal; auto.
  all: first [ rewrite a_shift1_ren_r | rewrite a_shift3_ren_r ]; auto.
Qed.

Lemma t_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 ⊆ Γ3) A (t : term Γ1 A)
  : (t `ₜ⊛ f1) ₜ⊛ᵣ f2 = t `ₜ⊛ (f1 ⊛ᵣ f2) .
  now apply (term_ind_mut _ _ _ ren_sub_prf).
Qed.
Lemma w_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 ⊆ Γ3) A (v : whn Γ1 A)
  : (v `ᵥ⊛ f1) `ᵥ⊛ᵣ f2 = v `ᵥ⊛ (f1 ⊛ᵣ f2) .
  now apply (whn_ind_mut _ _ _ ren_sub_prf).
Qed.
Lemma s_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 ⊆ Γ3) (s : state Γ1)
  : (s ₜ⊛ f1) ₛ⊛ᵣ f2 = s ₜ⊛ (f1 ⊛ᵣ f2) .
  now apply (state_ind_mut _ _ _ ren_sub_prf).
Qed.
Lemma v_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 ⊆ Γ3) A (v : val Γ1 A)
  : (v ᵥ⊛ f1) ᵥ⊛ᵣ f2 = v ᵥ⊛ (f1 ⊛ᵣ f2) .
  destruct A.
  - now apply w_ren_sub.
  - now apply t_ren_sub.
Qed.

Definition t_sub_ren_P Γ1 A (t : term Γ1 A) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val]> Γ3),
    (t ₜ⊛ᵣ f1) `ₜ⊛ f2 = t `ₜ⊛ (f1 ᵣ⊛ f2).
Definition w_sub_ren_P Γ1 A (v : whn Γ1 A) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val]> Γ3),
    (v `ᵥ⊛ᵣ f1) `ᵥ⊛ f2 = v `ᵥ⊛ (f1 ᵣ⊛ f2).
Definition s_sub_ren_P Γ1 (s : state Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val]> Γ3),
    (s ₛ⊛ᵣ f1) ₜ⊛ f2 = s ₜ⊛ (f1 ᵣ⊛ f2).

Lemma sub_ren_prf : syn_ind_args t_sub_ren_P w_sub_ren_P s_sub_ren_P.
  econstructor.
  all: unfold t_sub_ren_P, w_sub_ren_P, s_sub_ren_P.
  all: intros; cbn; f_equal; auto.
  all: first [ rewrite a_shift1_ren_l | rewrite a_shift3_ren_l ]; auto.
Qed.

Lemma t_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val]> Γ3) A (t : term Γ1 A)
  : (t ₜ⊛ᵣ f1) `ₜ⊛ f2 = t `ₜ⊛ (f1 ᵣ⊛ f2).
  now apply (term_ind_mut _ _ _ sub_ren_prf).
Qed.
Lemma w_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val]> Γ3) A (v : whn Γ1 A)
  : (v `ᵥ⊛ᵣ f1) `ᵥ⊛ f2 = v `ᵥ⊛ (f1 ᵣ⊛ f2).
  now apply (whn_ind_mut _ _ _ sub_ren_prf).
Qed.
Lemma s_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val]> Γ3) (s : state Γ1)
  : (s ₛ⊛ᵣ f1) ₜ⊛ f2 = s ₜ⊛ (f1 ᵣ⊛ f2).
  now apply (state_ind_mut _ _ _ sub_ren_prf).
Qed.
Lemma v_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val]> Γ3) A (v : val Γ1 A)
  : (v ᵥ⊛ᵣ f1) ᵥ⊛ f2 = v ᵥ⊛ (f1 ᵣ⊛ f2).
  destruct A.
  - now apply w_sub_ren.
  - now apply t_sub_ren.
Qed.

Lemma v_sub_id_r {Γ Δ} (f : Γ =[val]> Δ) A (i : Γ ∋ A) : Var i ᵥ⊛ f = f A i.
  now destruct A.
Qed.

Lemma a_shift1_comp {Γ1 Γ2 Γ3 A} (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 =[val]> Γ3)
  : @a_shift1 _ _ A (f1 ⊛ f2) ≡ₐ a_shift1 f1 ⊛ a_shift1 f2 .
  intros x i; dependent elimination i; cbn.
  - now rewrite v_sub_id_r.
  - now unfold v_shift1; rewrite v_ren_sub, v_sub_ren.
Qed.

Lemma a_shift3_comp {Γ1 Γ2 Γ3 A B C} (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 =[val]> Γ3)
  : @a_shift3 _ _ A B C (f1 ⊛ f2) ≡ₐ a_shift3 f1 ⊛ a_shift3 f2 .
  intros ? v; do 3 (dependent elimination v; cbn; [ now rewrite v_sub_id_r | ]).
  now unfold v_shift3; rewrite v_ren_sub, v_sub_ren.
Qed.

Definition t_sub_sub_P Γ1 A (t : term Γ1 A) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 =[val]> Γ3),
    (t `ₜ⊛ f1) `ₜ⊛ f2 = t `ₜ⊛ (f1 ⊛ f2) .
Definition w_sub_sub_P Γ1 A (v : whn Γ1 A) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 =[val]> Γ3),
    (v `ᵥ⊛ f1) `ᵥ⊛ f2 = v `ᵥ⊛ (f1 ⊛ f2) .
Definition s_sub_sub_P Γ1 (s : state Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 =[val]> Γ3),
    (s ₜ⊛ f1) ₜ⊛ f2 = s ₜ⊛ (f1 ⊛ f2) .

Lemma sub_sub_prf : syn_ind_args t_sub_sub_P w_sub_sub_P s_sub_sub_P.
  econstructor.
  all: unfold t_sub_sub_P, w_sub_sub_P, s_sub_sub_P.
  all: intros; cbn; f_equal; auto.
  all: first [ rewrite a_shift1_comp | rewrite a_shift3_comp ]; auto.
Qed.

Lemma t_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 =[val]> Γ3) A (t : term Γ1 A)
  : (t `ₜ⊛ f1) `ₜ⊛ f2 = t `ₜ⊛ (f1 ⊛ f2) .
  now apply (term_ind_mut _ _ _ sub_sub_prf).
Qed.
Lemma w_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 =[val]> Γ3) A (v : whn Γ1 A)
  : (v `ᵥ⊛ f1) `ᵥ⊛ f2 = v `ᵥ⊛ (f1 ⊛ f2) .
  now apply (whn_ind_mut _ _ _ sub_sub_prf).
Qed.
Lemma s_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 =[val]> Γ3) (s : state Γ1)
  : (s ₜ⊛ f1) ₜ⊛ f2 = s ₜ⊛ (f1 ⊛ f2) .
  now apply (state_ind_mut _ _ _ sub_sub_prf).
Qed.
Lemma v_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 =[val]> Γ3) A (v : val Γ1 A)
  : (v ᵥ⊛ f1) ᵥ⊛ f2 = v ᵥ⊛ (f1 ⊛ f2) .
  destruct A.
  - now apply w_sub_sub.
  - now apply t_sub_sub.
Qed.

Lemma a_comp_assoc {Γ1 Γ2 Γ3 Γ4} (u : Γ1 =[val]> Γ2) (v : Γ2 =[val]> Γ3) (w : Γ3 =[val]> Γ4)
           : (u ⊛ v) ⊛ w ≡ₐ u ⊛ (v ⊛ w).
  intros ? i; unfold a_comp; now apply v_sub_sub.
Qed.

Definition t_sub_id_l_P Γ A (t : term Γ A) : Prop := t `ₜ⊛ Var = t.
Definition w_sub_id_l_P Γ A (v : whn Γ A) : Prop := v `ᵥ⊛ Var = v.
Definition s_sub_id_l_P Γ (s : state Γ) : Prop := s ₜ⊛ Var = s.

Lemma sub_id_l_prf : syn_ind_args t_sub_id_l_P w_sub_id_l_P s_sub_id_l_P.
  econstructor.
  all: unfold t_sub_id_l_P, w_sub_id_l_P, s_sub_id_l_P.
  all: intros; cbn; f_equal; auto.
  all: first [ rewrite a_shift1_id | rewrite a_shift3_id ]; auto.
Qed.

Lemma t_sub_id_l {Γ} A (t : term Γ A) : t `ₜ⊛ Var = t.
  now apply (term_ind_mut _ _ _ sub_id_l_prf).
Qed.
Lemma w_sub_id_l {Γ} A (v : whn Γ A) : v `ᵥ⊛ Var = v.
  now apply (whn_ind_mut _ _ _ sub_id_l_prf).
Qed.
Lemma s_sub_id_l {Γ} (s : state Γ) : s ₜ⊛ Var = s.
  now apply (state_ind_mut _ _ _ sub_id_l_prf).
Qed.
Lemma v_sub_id_l {Γ} A (v : val Γ A) : v ᵥ⊛ Var = v.
  destruct A.
  - now apply w_sub_id_l.
  - now apply t_sub_id_l.
Qed.

Lemma sub1_sub {Γ Δ A} (f : Γ =[val]> Δ) (v : val Γ A) :
  a_shift1 f ⊛ asgn1 (v ᵥ⊛ f) ≡ₐ asgn1 v ⊛ f.
  intros ? h; dependent elimination h; cbn.
  - now rewrite v_sub_id_r.
  - unfold v_shift1; rewrite v_sub_ren, v_sub_id_r.
    now apply v_sub_id_l.
Qed.

Lemma sub1_ren {Γ Δ A} (f : Γ ⊆ Δ) (v : val Γ A) :
  r_shift1 f ᵣ⊛ asgn1 (v ᵥ⊛ᵣ f) ≡ₐ asgn1 v ⊛ᵣ f.
  intros ? h; dependent elimination h; auto.
  cbn; now rewrite v_ren_id_r.
Qed.

Lemma v_sub1_sub {Γ Δ A B} (f : Γ =[val]> Δ) (v : val Γ A) (w : val (Γ ▶ₓ A) B)
  : (w ᵥ⊛ a_shift1 f) ᵥ⊛ ₁[ v ᵥ⊛ f ] = (w ᵥ⊛ ₁[ v ]) ᵥ⊛ f .
  cbn; rewrite 2 v_sub_sub.
  apply v_sub_eq; now rewrite sub1_sub.
Qed.

Lemma v_sub1_ren {Γ Δ A B} (f : Γ ⊆ Δ) (v : val Γ A) (w : val (Γ ▶ₓ A) B)
  : (w ᵥ⊛ᵣ r_shift1 f) ᵥ⊛ ₁[ v ᵥ⊛ᵣ f ] = (w ᵥ⊛ ₁[ v ]) ᵥ⊛ᵣ f .
  cbn; rewrite v_sub_ren, v_ren_sub.
  apply v_sub_eq; now rewrite sub1_ren.
Qed.

Lemma s_sub1_sub {Γ Δ A} (f : Γ =[val]> Δ) (v : val Γ A) (s : state (Γ ▶ₓ A))
  : (s ₜ⊛ a_shift1 f) ₜ⊛ ₁[ v ᵥ⊛ f ] = (s ₜ⊛ ₁[ v ]) ₜ⊛ f .
  cbn; now rewrite 2 s_sub_sub, sub1_sub.
Qed.

Lemma s_sub3_sub {Γ Δ A B C} (f : Γ =[val]> Δ) (s : state (Γ ▶ₓ A ▶ₓ B ▶ₓ C)) u v w
  : (s ₜ⊛ a_shift3 f) ₜ⊛ ₃[ u ᵥ⊛ f , v ᵥ⊛ f , w ᵥ⊛ f ] = (s ₜ⊛ ₃[ u, v , w ]) ₜ⊛ f .
  cbn; rewrite 2 s_sub_sub; apply s_sub_eq.
  intros ? v0; cbn.
  do 3 (dependent elimination v0; cbn; [ now rewrite v_sub_id_r | ]).
  unfold v_shift3; rewrite v_sub_ren, v_sub_id_r, <- v_sub_id_l.
  now apply v_sub_eq.
Qed.

Lemma s_sub1_ren {Γ Δ A} (f : Γ ⊆ Δ) (v : val Γ A) (s : state (Γ ▶ₓ A))
  : (s ₛ⊛ᵣ r_shift1 f) ₜ⊛ ₁[ v ᵥ⊛ᵣ f ] = (s ₜ⊛ ₁[ v ]) ₛ⊛ᵣ f .
  cbn; now rewrite s_sub_ren, s_ren_sub, sub1_ren.
Qed.

Lemma t_sub1_sub {Γ Δ A B} (f : Γ =[val]> Δ) (v : val Γ A) (t : term (Γ ▶ₓ A) B)
  : (t `ₜ⊛ a_shift1 f) `ₜ⊛ ₁[ v ᵥ⊛ f ] = (t `ₜ⊛ ₁[ v ]) `ₜ⊛ f .
  cbn; rewrite 2 t_sub_sub.
  apply t_sub_eq; now rewrite sub1_sub.
Qed.

Lemma t_sub1_ren {Γ Δ A B} (f : Γ ⊆ Δ) (v : val Γ A) (t : term (Γ ▶ₓ A) B)
  : (t ₜ⊛ᵣ r_shift1 f) `ₜ⊛ ₁[ v ᵥ⊛ᵣ f ] = (t `ₜ⊛ ₁[ v ]) ₜ⊛ᵣ f .
  cbn; rewrite t_sub_ren, t_ren_sub.
  apply t_sub_eq; now rewrite sub1_ren.
Qed.

#[global] Instance p_app_eq {Γ A} (v : val Γ A) (m : pat (t_neg A))
  : Proper (asgn_eq _ _ ==> eq) (p_app v m) .
  intros u1 u2 H; destruct A; cbn.
  now rewrite (t_sub_eq u1 u2 H).
  now rewrite (w_sub_eq u1 u2 H).
Qed.

Lemma refold_id_aux {Γ : neg_ctx} A (v : whn Γ A)
  : (p_of_w _ v : val _ _) `ᵥ⊛ p_dom_of_w _ v = v .
  cbn; funelim (p_of_w A v); auto.
  - destruct (s_prf i).
  - destruct (s_prf i).
  - now cbn; f_equal. 
  - now cbn; f_equal. 
Qed.

Equations p_of_w_eq {Γ : neg_ctx} A (p : pat ↑A) (e : pat_dom p =[val]> Γ)
          : p_of_w A ((p : val _ _) `ᵥ⊛ e) = p :=
  p_of_w_eq (a `+ b) (PInl v) e := f_equal PInl (p_of_w_eq _ v e) ;
  p_of_w_eq (a `+ b) (PInr v) e := f_equal PInr (p_of_w_eq _ v e) ;
  p_of_w_eq (`1)     PTt      e := eq_refl ;
  p_of_w_eq (a `× b) PPair    e := eq_refl ;
  p_of_w_eq (a `→ b) PLam     e := eq_refl .

Lemma p_dom_of_w_eq {Γ : neg_ctx} A (p : pat ↑A) (e : pat_dom p =[val]> Γ)
      : rew [fun p => pat_dom p =[ val ]> Γ] p_of_w_eq A p e
        in p_dom_of_w A ((p : val _ _) `ᵥ⊛ e)
      ≡ₐ e .
  funelim (p_of_w_eq A p e); cbn.
  - intros ? v; repeat (dependent elimination v; auto).
  - intros ? v; repeat (dependent elimination v; auto).
  - match goal with | |- ?s ≡ₐ e => pose (xx := s); change (_ ≡ₐ e) with (xx ≡ₐ e) end .
    remember xx as xx'; unfold xx in Heqxx'; clear xx.
    now rewrite (eq_trans Heqxx' (eq_sym (rew_map _ PInl _ _))).
  - match goal with | |- ?s ≡ₐ e => pose (xx := s); change (_ ≡ₐ e) with (xx ≡ₐ e) end .
    remember xx as xx'; unfold xx in Heqxx'; clear xx.
    now rewrite (eq_trans Heqxx' (eq_sym (rew_map _ PInr _ _))).
  - intros ? v; repeat (dependent elimination v; auto).
Qed.

Notation val_n := (val ∘ neg_c_coe).
Notation state_n := (state ∘ neg_c_coe).

#[global] Instance val_n_monoid : subst_monoid val_n .
  esplit.
  - intros Γ x i; exact (Var i).
  - intros Γ x v Δ f; exact (v ᵥ⊛ f).
Defined.

#[global] Instance state_n_module : subst_module val_n state_n .
  esplit; intros Γ s Δ f; exact (s ₜ⊛ (f : Γ =[val]> Δ)).
Defined.

#[global] Instance val_n_laws : subst_monoid_laws val_n .
  esplit.
  - intros ???? <- ????; now apply v_sub_eq.
  - intros ?????; now apply v_sub_id_r.
  - intros ???; now apply v_sub_id_l.
  - intros ???????; symmetry; now apply v_sub_sub.
Qed.

#[global] Instance state_n_laws : subst_module_laws val_n state_n .
  esplit.
  - intros ??? <- ????; now apply s_sub_eq.
  - intros ??; now apply s_sub_id_l.
  - intros ??????; symmetry; now apply s_sub_sub.
Qed.

#[global] Instance var_laws : var_assumptions val_n.
  esplit.
  - intros ? [] ?? H; now dependent destruction H.
  - intros ? [] v; dependent elimination v.
    all: try exact (Yes _ (Vvar _)).
    all: apply No; intro H; dependent destruction H.
  - intros ?? [] ???; cbn in v; dependent induction v.
    all: try now dependent destruction X; exact (Vvar _).
    all: dependent induction w; dependent destruction X; exact (Vvar _).
Qed.

#[global] Instance sysl_machine : machine val_n state_n op_copat :=
  {| Machine.eval := @eval ; oapp := @p_app |} .

From Coinduction Require Import coinduction lattice rel tactics.

Ltac refold_eval :=
  change (Structure.iter _ _ ?a) with (eval a);
  change (Structure.subst (fun pat : T1 => let 'T1_0 := pat in ?f) T1_0 ?u)
    with (bind_delay' u f).

Definition upg_v {Γ} {A : pre_ty} : whn Γ A  -> val Γ ↑A := fun v => v.
Definition upg_k {Γ} {A : pre_ty} : term Γ ¬A -> val Γ ¬A := fun v => v.
Definition dwn_v {Γ} {A : pre_ty} : val Γ ↑A -> whn Γ A  := fun v => v.
Definition dwn_k {Γ} {A : pre_ty} : val Γ ¬A -> term Γ ¬A := fun v => v.

Lemma nf_eq_split {Γ : neg_ctx} {A : pre_ty} (i : Γ ∋ ¬A) (p : pat ↑A) γ
  : nf_eq (i ⋅ w_split _ (dwn_v ((p : val _ _) `ᵥ⊛ γ)))
          (i ⋅ (p : o_op op_copat ¬A) ⦇ γ ⦈).
  unfold w_split, dwn_v; cbn.
  pose proof (p_dom_of_w_eq A p γ).
  pose (H' := p_of_w_eq A p γ); fold H' in H.
  pose (a := p_dom_of_w A (v_of_p p `ᵥ⊛ γ)); fold a in H |- *.
  remember a as a'; clear a Heqa'.
  revert a' H; rewrite H'; intros; now econstructor.
Qed.

#[global] Instance machine_law : machine_laws val_n state_n op_copat.
  esplit.
  - intros; apply p_app_eq.
  - intros ?? [] ????; cbn.
    now rewrite (t_sub_sub _ _ _ _).
    now rewrite (w_sub_sub _ _ _ _).
  - cbn; intros Γ Δ; unfold comp_eq, it_eq; coinduction R CIH; intros c a.
    cbn; funelim (eval_aux c); try now destruct (s_prf i).
    + change (it_eqF _ ?RX ?RY _ _ _) with
        (it_eq_map ∅ₑ RX RY T1_0
           (eval (Cut (Val (v `ᵥ⊛ a)) (a _ i)))
           (eval (Cut (Val ((v_of_p (p_of_w _ v) `ᵥ⊛ p_dom_of_w _ v `ᵥ⊛ a))) (a _ i)))).
      now rewrite (refold_id_aux _ v).
    + cbn; econstructor; refold_eval.
      change (?v `ᵥ⊛ ?a) with (upg_v v ᵥ⊛ a); rewrite s_sub1_sub.
      apply CIH.
    + cbn; econstructor; refold_eval.
      change (?v `ᵥ⊛ ?a) with (upg_v v ᵥ⊛ a); rewrite s_sub1_sub.
      apply CIH.
    + cbn; econstructor; refold_eval.
      change (?v `ᵥ⊛ ?a) with (upg_v v ᵥ⊛ a); rewrite s_sub1_sub.
      apply CIH.
    + now change (it_eqF _ ?RX ?RY _ _ _) with
        (it_eq_map ∅ₑ RX RY T1_0
           (eval (Cut (a _ i) (Fst k `ₜ⊛ a)))
           (eval (Cut (a _ i) (Fst k `ₜ⊛ a)))).
    + cbn; econstructor; refold_eval.
      change (?v `ₜ⊛ ?a) with (upg_k v ᵥ⊛ a); rewrite s_sub1_sub.
      apply CIH.
    + now change (it_eqF _ ?RX ?RY _ _ _) with
        (it_eq_map ∅ₑ RX RY T1_0
           (eval (Cut (a _ i) (Snd k `ₜ⊛ a)))
           (eval (Cut (a _ i) (Snd k `ₜ⊛ a)))).
    + cbn; econstructor; refold_eval.
      change (?v `ₜ⊛ ?a) with (upg_k v ᵥ⊛ a); rewrite s_sub1_sub.
      apply CIH.
    + simp eval_aux.
      unfold p_app, app_nf, nf_var, nf_obs, nf_args, cut_l, cut_r, fill_op, fill_args.
      change (it_eqF _ ?RX ?RY _ _ _) with
        (it_eq_map ∅ₑ RX RY T1_0
           (eval (Cut (a _ i) (App v k `ₜ⊛ a)))
           (eval (Cut (a _ i) (PApp (p_of_w A7 v) `ₜ⊛ [ p_dom_of_w _ v ,ₓ upg_k k ] `ₜ⊛ a)))).
      cbn - [ it_eq_map ].
      rewrite w_sub_ren.
      change (r_pop ᵣ⊛ (p_dom_of_w _ v ▶ₐ _))%asgn with (p_dom_of_w _ v).
      now rewrite (refold_id_aux _ v).
    + cbn; econstructor; refold_eval.
      change (Lam (s_subst _ _ _ _)) with (upg_v (Lam s) ᵥ⊛ a).
      change (?v `ₜ⊛ ?a) with (upg_k v ᵥ⊛ a).
      change (?v `ᵥ⊛ ?a) with (upg_v v ᵥ⊛ a).
      rewrite s_sub3_sub.
      apply CIH.
    + cbn; econstructor; refold_eval.
      change (?v `ₜ⊛ ?a) with (upg_k v ᵥ⊛ a); rewrite s_sub1_sub.
      apply CIH.
  - cbn; intros ? [ A i [ o γ ]]; cbn; unfold p_app, nf_args, cut_r, fill_args.
    cbn in o; funelim (v_of_p o); simpl_depind; inversion eqargs.
    all: match goal with
         | H : _ = ?A† |- _ => destruct A; dependent destruction H
         end.
    all: dependent destruction eqargs; cbn.
    all: apply it_eq_unstep; cbn; unfold Var; cbn; econstructor.
    1-2,5-7: econstructor; intros ? v; repeat (dependent elimination v; auto).
    1-2: exact (nf_eq_split _ _ γ).
    (* a bit of an ugly case because we didn't write proper generic functions
       for splitting negative values.. hence knowing this one is an App is
       getting in our way *)
    clear; unfold app_nf.
    rewrite w_sub_ren.
    pose (γ' := (r_pop ᵣ⊛ γ)%asgn);
      change (sub_elt _) with (pat_dom v : t_ctx) in γ' at 1; cbn in γ'.
    change (r_pop ᵣ⊛ γ)%asgn with γ'.
    pose (vv := γ _ Ctx.top); cbn in vv; change (γ _ Ctx.top) with vv.
    assert (H : [ γ' ,ₓ upg_k vv ] ≡ₐ γ) by now intros ? ii; dependent elimination ii.
    remember γ' as a; remember vv as t; clear γ' vv Heqa Heqt.
    pose proof (p_dom_of_w_eq _ v a).
    pose (H' := p_of_w_eq _ v a); fold H' in H0.
    pose (aa := p_dom_of_w _ ((v : val _ _) `ᵥ⊛ a)); fold aa in H0 |- *.
    remember aa as a'; clear aa Heqa'.
    revert a' H0; rewrite H'; intros; econstructor.
    etransitivity; [ | exact H ].
    refine (a_append_eq _ _ _ _ _ _); auto.
  - intros A; econstructor; intros [ B m ] H; dependent elimination H;
      cbn [projT1 projT2] in i, i0.
    destruct y.
    all: dependent elimination v; try now destruct (t0 (Vvar _)).
    all: clear t0.
    all: cbn in o; dependent elimination o; cbn in i0.
    all: match goal with
         | u : dom _ =[val_n]> _ |- _ =>
             cbn in i0;
             pose (vv := u _ Ctx.top); change (u _ Ctx.top) with vv in i0;
             remember vv as v'; clear u vv Heqv'; cbn in v'
         | _ => idtac
       end.
    1-10: now apply it_eq_step in i0; inversion i0.
    all: dependent elimination v'; [ | apply it_eq_step in i0; now inversion i0 ].
    all:
      apply it_eq_step in i0; cbn in i0; dependent elimination i0; cbn in r_rel;
      apply noConfusion_inv in r_rel; unfold w_split in r_rel;
      cbn in r_rel; unfold NoConfusionHom_f_cut,s_var_upg in r_rel; cbn in r_rel;
      pose proof (H := f_equal pr1 r_rel); cbn in H; dependent destruction H;
      apply DepElim.pr2_uip in r_rel;
      pose proof (H := f_equal pr1 r_rel); cbn in H; dependent destruction H;
      apply DepElim.pr2_uip in r_rel; dependent destruction r_rel.
    all:
      econstructor; intros [ t o ] H; cbn in t,o; dependent elimination H.
    all: dependent elimination v; try now destruct (t0 (Vvar _)).
    all: apply it_eq_step in i0; cbn in i0; now inversion i0.
Qed.

Definition subst_eq (Δ : neg_ctx) {Γ} : relation (state Γ) :=
  fun u v => forall (σ : Γ =[val]> Δ), evalₒ (u ₜ⊛ σ : state_n Δ) ≈ evalₒ (v ₜ⊛ σ : state_n Δ) .
Notation "x ≈⟦sub Δ ⟧≈ y" := (subst_eq Δ x y) (at level 50).

Theorem subst_correct (Δ : neg_ctx) {Γ : neg_ctx} (x y : state Γ)
  : x ≈⟦ogs Δ ⟧≈ y -> x ≈⟦sub Δ ⟧≈ y.
  exact (ogs_correction _ x y).
Qed.

Definition c_of_t {Γ : neg_ctx} {A} (t : term Γ ↑A)
           : state_n (Γ ▶ₛ {| sub_elt := ¬A ; sub_prf := stt |}) :=
  Cut (t_shift1 _ t) (VarR Ctx.top) .
Notation "'name⁺'" := c_of_t.

Definition a_of_sk {Γ Δ : neg_ctx} {A} (s : Γ =[val]> Δ) (k : term Δ ¬A)
  : (Γ ▶ₛ {| sub_elt := ¬A ; sub_prf := stt |}) =[val_n]> Δ :=
  [ s ,ₓ k : val _ ¬_ ].

Lemma sub_csk {Γ Δ : neg_ctx} {A} (t : term Γ ↑A) (s : Γ =[val]> Δ)
  (k : term Δ ¬A)
  : Cut (t `ₜ⊛ s) k = c_of_t t ₜ⊛ a_of_sk s k.
Proof.
  cbn; f_equal; unfold t_shift1; rewrite t_sub_ren; now apply t_sub_eq.
Qed.

Definition ciu_eq (Δ : neg_ctx) {Γ A} : relation (term Γ ↑A) :=
  fun u v =>
    forall (σ : Γ =[val]> Δ) (k : term Δ ¬A),
      evalₒ (Cut (u `ₜ⊛ σ) k : state_n Δ) ≈ evalₒ (Cut (v `ₜ⊛ σ) k : state_n Δ) .
Notation "x ≈⟦ciu Δ ⟧⁺≈ y" := (ciu_eq Δ x y) (at level 50).

Theorem ciu_correct (Δ : neg_ctx) {Γ : neg_ctx} {A} (x y : term Γ ↑A)
  : (name⁺ x) ≈⟦ogs Δ ⟧≈ (name⁺ y) -> x ≈⟦ciu Δ ⟧⁺≈ y.
  intros H σ k; rewrite 2 sub_csk.
  now apply subst_correct.
Qed.
