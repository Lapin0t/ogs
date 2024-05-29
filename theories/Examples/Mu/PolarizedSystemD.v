From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.
From OGS.Ctx Require Import All Ctx Covering Subset.
From OGS.ITree Require Import Event ITree Eq Delay Structure Properties.
From OGS.OGS Require Import Soundness. 
(*|
In this file we instanciate our OGS construction with the fully-dual polarized mu-mu-tilde
calculus 'System D' from P. Downen & Z. Ariola. The presentation may be slightly unusual
as we go for one-sided sequent. The only real divergence from the original calculus
is the addition of a restricted form of recursion, making the language non-normalizing. 

Types
=====

Type have polarities, basically whether their values are CBV-biased
or CBN-biased
|*)
Variant pol : Type := pos | neg .
(*| .. coq:: none |*)
Derive NoConfusion for pol.
(*
Equations pneg : pol -> pol :=
  pneg pos := neg ;
  pneg neg := pos .
*)
(*|
Syntax of types. We have a fully dual type system with:

- `0`, positive void (no constructor),
- `⊤`, negative unit (no destructor),
- `⊥`, negative void (one trivial destructor),
- `1`, positive unit (one trivial constructor),
- `A ⊗ B`, positive product (pairs with pattern-matching),
- `A ⅋ B`, negative sum (one binary destructor),
- `A ⊕ B`, positive sum (usual coproduct with injections),
- `A & B`, negative product (usual product with projections),
- `↓ A`, positive shift (thunking),
- `↑ A`, negative shift ('returners'),
- `⊖ A`, positive negation (approximately continuations accepting an `A`),
- `¬ A`, negative negation (approximately refutations of `A`).

We opt for an explicit treatment of polarity, by indexing the family of types.
|*)
Inductive ty0 : pol -> Type :=
| Zer : ty0 pos
| Top : ty0 neg
| One : ty0 pos
| Bot : ty0 neg
| Tens : ty0 pos -> ty0 pos -> ty0 pos
| Par : ty0 neg -> ty0 neg -> ty0 neg
| Or : ty0 pos -> ty0 pos -> ty0 pos
| And : ty0 neg -> ty0 neg -> ty0 neg
| ShiftP : ty0 neg -> ty0 pos
| ShiftN : ty0 pos -> ty0 neg
| NegP : ty0 neg -> ty0 pos
| NegN : ty0 pos -> ty0 neg
.
(*| .. coq:: none |*)
Derive Signature NoConfusion NoConfusionHom for ty0.
Declare Scope ty_scope.
Delimit Scope ty_scope with ty.
Bind Scope ty_scope with ty0.
(*||*)
Notation "0" := (Zer) : ty_scope .
Notation "1" := (One) : ty_scope .
Notation "⊤" := (Top) : ty_scope .
Notation "⊥" := (Bot) : ty_scope .
Notation "A ⊗ B" := (Tens A B) (at level 40) : ty_scope.
Notation "A ⅋ B" := (Par A B) (at level 40) : ty_scope .
Notation "A ⊕ B" := (Or A B) (at level 40) : ty_scope.
Notation "A & B" := (And A B) (at level 40) : ty_scope.
Notation "↓ A" := (ShiftP A) (at level 40) : ty_scope.
Notation "↑ A" := (ShiftN A) (at level 40) : ty_scope.
Notation "⊖ A" := (NegP A) (at level 5) : ty_scope .
Notation "¬ A" := (NegN A) (at level 5) : ty_scope .
(*|
As hinted above, we go for one-sided sequents. This enables to have only one context
instead of two, simplifying the theory of substitution. On the flip-side, as we still
need two kinds of variables, the 'normal' ones and the co-variables, our contexts will
not contain bare types but side-annotated types. A variable of type `A` will thus be
stored as `\`-A` in the context while a co-variable of type `A` will be stored as `\`-A`. 
|*)
Variant ty : Type :=
| VTy {p} : ty0 p -> ty
| KTy {p} : ty0 p -> ty
.
(*| .. coq:: none |*)
Derive NoConfusion NoConfusionHom for ty.
Bind Scope ty_scope with ty.
Open Scope ty_scope.
(*||*)
Notation "'`+' t" := (VTy t) (at level 5) : ty_scope .
Notation "'`-' t" := (KTy t) (at level 5) : ty_scope .

Equations t_neg : ty -> ty :=
  t_neg `+a := `-a ;
  t_neg `-a := `+a .
Notation "a †" := (t_neg a) (at level 5) : ty_scope.
(*|
Finally we define contexts as backward lists of side-annotated types.
|*)
Definition t_ctx : Type := Ctx.ctx ty.
(*| .. coq:: none |*)
Bind Scope ctx_scope with t_ctx.
(*|
Terms
=====

We define the well-typed syntax of the language with 3 mutually defined syntactic
categories: terms, weak head-normal forms and states ('language configurations' in
the paper).

Nothing should be too surprising. A first notable point is that by choosing to have an
explicit notion of 'side' of a variable, we can have a single construct
for both mu and mu-tilde. A second notable point is our new slightly exotic `RecL` and
`RecR` constructions. They allow arbitrary recursion at co-terms of positive types and
at terms of negative types. These polarity restrictions allow us to have minimal
disruption of the evaluation rules. 
|*)
Inductive term : t_ctx -> ty -> Type :=
| Mu {Γ A} : state (Γ ▶ₓ A†) -> term Γ A
| RecL {Γ} {A : ty0 pos} : term (Γ ▶ₓ `-A) `-A -> term Γ `-A
| RecR {Γ} {A : ty0 neg} : term (Γ ▶ₓ `+A) `+A -> term Γ `+A
| Whn {Γ A} : whn Γ A -> term Γ A
with whn : t_ctx -> ty -> Type :=
| Var {Γ A} : Γ ∋ A -> whn Γ A
| ZerL {Γ} : whn Γ `-0
| TopR {Γ} : whn Γ `+⊤
| OneR {Γ} : whn Γ `+1
| OneL {Γ} : state Γ -> whn Γ `-1
| BotR {Γ} : state Γ -> whn Γ `+⊥
| BotL {Γ} : whn Γ `-⊥
| TenR {Γ A B} : whn Γ `+A -> whn Γ `+B -> whn Γ `+(A ⊗ B)
| TenL {Γ A B} : state (Γ ▶ₓ `+A ▶ₓ `+B) -> whn Γ `-(A ⊗ B)
| ParR {Γ A B} : state (Γ ▶ₓ `-A ▶ₓ `-B) -> whn Γ `+(A ⅋ B)
| ParL {Γ A B} : whn Γ `-A -> whn Γ `-B -> whn Γ `-(A ⅋ B)
| OrR1 {Γ A B} : whn Γ `+A -> whn Γ `+(A ⊕ B)
| OrR2 {Γ A B} : whn Γ `+B -> whn Γ `+(A ⊕ B)
| OrL {Γ A B} : state (Γ ▶ₓ `+A) -> state (Γ ▶ₓ `+B) -> whn Γ `-(A ⊕ B)
| AndR {Γ A B} : state (Γ ▶ₓ `-A) -> state (Γ ▶ₓ `-B) -> whn Γ `+(A & B)
| AndL1 {Γ A B} : whn Γ `-A -> whn Γ `-(A & B)
| AndL2 {Γ A B} : whn Γ `-B -> whn Γ `-(A & B)
| ShiftPR {Γ A} : term Γ `+A -> whn Γ `+(↓ A)
| ShiftPL {Γ A} : state (Γ ▶ₓ `+A) -> whn Γ `-(↓ A)
| ShiftNR {Γ A} : state (Γ ▶ₓ `-A) -> whn Γ `+(↑ A)
| ShiftNL {Γ A} : term Γ `-A -> whn Γ `-(↑ A)
| NegPR {Γ A} : whn Γ `-A -> whn Γ `+(⊖ A)
| NegPL {Γ A} : state (Γ ▶ₓ `-A) -> whn Γ `-(⊖ A)
| NegNR {Γ A} : state (Γ ▶ₓ `+A) -> whn Γ `+(¬ A)
| NegNL {Γ A} : whn Γ `+A -> whn Γ `-(¬ A)
with state : t_ctx -> Type :=
| Cut {Γ} p {A : ty0 p} : term Γ `+A -> term Γ `-A -> state Γ
.

Definition Cut' {Γ A} : term Γ A -> term Γ A† -> state Γ :=
  match A with
  | `+A => fun t1 t2 => Cut _ t1 t2
  | `-A => fun t1 t2 => Cut _ t2 t1
  end .
(*| .. coq:: none |*)
Derive Signature NoConfusion NoConfusionHom for term.
Derive Signature NoConfusion NoConfusionHom for whn.
Derive Signature NoConfusion NoConfusionHom for state.

(*|
Values are not exactly weak head-normal forms, but depend on the polarity of the type.
As positive types have CBV evaluation, their values are weak head-normal forms, but their
co-values (evaluation contexts) are just any co-term (context) as they are delayed anyways.
Dually for negative types, values are delayed hence can be any term while co-values must
be weak head-normal form contexts.
|*)
Equations val : t_ctx -> ty -> Type :=
  val Γ (@VTy pos A) := whn Γ `+A ;
  val Γ (@KTy pos A) := term Γ `-A ;
  val Γ (@VTy neg A) := term Γ `+A ;
  val Γ (@KTy neg A) := whn Γ `-A .
Arguments val _ _ /.
(*|
We provide a 'smart-constructor' for variables, embedding variables in values.
|*)
Equations var : c_var ⇒₁ val :=
  var _ (@VTy pos _) i := Var i ;
  var _ (@KTy pos _) i := Whn (Var i) ;
  var _ (@VTy neg _) i := Whn (Var i) ;
  var _ (@KTy neg _) i := Var i .
#[global] Arguments var {Γ} [x] / i.
(*|
Renaming
========

Without surprise parallel renaming goes by a big mutual induction, shifting the renaming
apropriately while going under binders. Note the use of the internal substitution hom
to type it.
|*)
Equations t_rename : term ⇒₁ ⟦ c_var , term ⟧₁ :=
  t_rename _ _ (Mu c)    _ f := Mu (s_rename _ c _ (r_shift1 f)) ;
  t_rename _ _ (RecL t)  _ f := RecL (t_rename _ _ t _ (r_shift1 f)) ;
  t_rename _ _ (RecR t)  _ f := RecR (t_rename _ _ t _ (r_shift1 f)) ;
  t_rename _ _ (Whn v)   _ f := Whn (w_rename _ _ v _ f) ;
with w_rename : whn ⇒₁ ⟦ c_var , whn ⟧₁ :=
  w_rename _  _ (Var i)       _ f := Var (f _ i) ;
  w_rename _  _ (ZerL)        _ f := ZerL ;
  w_rename _  _ (TopR)        _ f := TopR ;
  w_rename _  _ (OneR)        _ f := OneR ;
  w_rename _  _ (OneL c)      _ f := OneL (s_rename _ c _ f) ;
  w_rename _  _ (BotR c)      _ f := BotR (s_rename _ c _ f) ;
  w_rename _  _ (BotL)        _ f := BotL ;
  w_rename _  _ (TenR v1 v2)  _ f := TenR (w_rename _ _ v1 _ f) (w_rename _ _ v2 _ f) ;
  w_rename _  _ (TenL c)      _ f := TenL (s_rename _ c _ (r_shift2 f)) ;
  w_rename _  _ (ParR c)      _ f := ParR (s_rename _ c _ (r_shift2 f)) ;
  w_rename _  _ (ParL k1 k2)  _ f := ParL (w_rename _ _ k1 _ f) (w_rename _ _ k2 _ f) ;
  w_rename _  _ (OrR1 v)      _ f := OrR1 (w_rename _ _ v _ f) ;
  w_rename _  _ (OrR2 v)      _ f := OrR2 (w_rename _ _ v _ f) ;
  w_rename _  _ (OrL c1 c2)   _ f := OrL (s_rename _ c1 _ (r_shift1 f))
                                         (s_rename _ c2 _ (r_shift1 f)) ;
  w_rename _  _ (AndR c1 c2)  _ f := AndR (s_rename _ c1 _ (r_shift1 f))
                                          (s_rename _ c2 _ (r_shift1 f)) ;
  w_rename _  _ (AndL1 k)     _ f := AndL1 (w_rename _ _ k _ f) ;
  w_rename _  _ (AndL2 k)     _ f := AndL2 (w_rename _ _ k _ f) ;
  w_rename _  _ (ShiftPR t)   _ f := ShiftPR (t_rename _ _ t _ f) ;
  w_rename _  _ (ShiftPL c)   _ f := ShiftPL (s_rename _ c _ (r_shift1 f)) ;
  w_rename _  _ (ShiftNR c)   _ f := ShiftNR (s_rename _ c _ (r_shift1 f)) ;
  w_rename _  _ (ShiftNL t)   _ f := ShiftNL (t_rename _ _ t _ f) ;
  w_rename _  _ (NegPR k)     _ f := NegPR (w_rename _ _ k _ f) ;
  w_rename _  _ (NegPL c)     _ f := NegPL (s_rename _ c _ (r_shift1 f)) ;
  w_rename _  _ (NegNR c)     _ f := NegNR (s_rename _ c _ (r_shift1 f)) ;
  w_rename _  _ (NegNL v)     _ f := NegNL (w_rename _ _ v _ f) ;
with s_rename : state ⇒₀ ⟦ c_var , state ⟧₀ :=
  s_rename _ (Cut _ v k) _ f := Cut _ (t_rename _ _ v _ f) (t_rename _ _ k _ f) .
(*|
We extend it to values...
|*)
Equations v_rename : val ⇒₁ ⟦ c_var , val ⟧₁ :=
  v_rename _ (@VTy pos a) := w_rename _ _ ;
  v_rename _ (@KTy pos a) := t_rename _ _ ;
  v_rename _ (@VTy neg a) := t_rename _ _ ;
  v_rename _ (@KTy neg a) := w_rename _ _ .
(*|
... provide a couple infix notations...
|*)
Notation "t ₜ⊛ᵣ r" := (t_rename _ _ t _ r%asgn) (at level 14).
Notation "w `ᵥ⊛ᵣ r" := (w_rename _ _ w _ r%asgn) (at level 14).
Notation "v ᵥ⊛ᵣ r" := (v_rename _ _ v _ r%asgn) (at level 14).
Notation "s ₛ⊛ᵣ r" := (s_rename _ s _ r%asgn) (at level 14).

(*|
... and extend it to assignments.
|*)
Definition a_ren {Γ1 Γ2 Γ3} : Γ1 =[val]> Γ2 -> Γ2 ⊆ Γ3 -> Γ1 =[val]> Γ3 :=
  fun f g _ i => v_rename _ _ (f _ i) _ g .
Arguments a_ren {_ _ _} _ _ _ _ /.
Notation "a ⊛ᵣ r" := (a_ren a r%asgn) (at level 14) : asgn_scope.
(*|
The following bunch of shifting functions will help us define parallel substitution.
|*)
Definition t_shift1 {Γ y} : term Γ ⇒ᵢ term (Γ ▶ₓ y)  := fun _ t => t ₜ⊛ᵣ r_pop.
Definition w_shift1 {Γ y} : whn Γ ⇒ᵢ whn (Γ ▶ₓ y)    := fun _ w => w `ᵥ⊛ᵣ r_pop.
Definition s_shift1 {Γ y} : state Γ -> state (Γ ▶ₓ y) := fun s => s ₛ⊛ᵣ r_pop.
Definition v_shift1 {Γ y} : val Γ ⇒ᵢ val (Γ ▶ₓ y)    := fun _ v => v ᵥ⊛ᵣ r_pop.
Definition v_shift2 {Γ y z} : val Γ ⇒ᵢ val (Γ ▶ₓ y ▶ₓ z) := fun _ v => v ᵥ⊛ᵣ (r_pop ᵣ⊛ r_pop).
Definition a_shift1 {Γ Δ} [y] (a : Γ =[val]> Δ) : (Γ ▶ₓ y) =[val]> (Δ ▶ₓ y)
  := [ fun _ i => v_shift1 _ (a _ i) ,ₓ var top ].
Definition a_shift2 {Γ Δ} [y z] (a : Γ =[val]> Δ) : (Γ ▶ₓ y ▶ₓ z) =[val]> (Δ ▶ₓ y ▶ₓ z)
  := [ [ fun _ i => v_shift2 _ (a _ i) ,ₓ var (pop top) ] ,ₓ var top ].
(*|
We also define two embeddings linking the various syntactical categories.
|*)
Equations v_of_w {Γ} : whn Γ ⇒ᵢ val Γ :=
  v_of_w (@VTy pos _) v := v ;
  v_of_w (@KTy pos _) u := Whn u ;
  v_of_w (@VTy neg _) u := Whn u ;
  v_of_w (@KTy neg _) k := k .

Equations t_of_v {Γ} : val Γ ⇒ᵢ term Γ :=
  t_of_v (@VTy pos _) v := Whn v ;
  t_of_v (@KTy pos _) u := u ;
  t_of_v (@VTy neg _) u := u ;
  t_of_v (@KTy neg _) k := Whn k .

(*|
Substitution
============

Having done with renaming, we reapply the same pattern to define parallel substitution.
Note that substituting a weak head-normal form with values may not yield a weak
head-normal form, but only a value!
|*)
Equations t_subst : term ⇒₁ ⟦ val , term ⟧₁ :=
  t_subst _ _ (Mu c)    _ f := Mu (s_subst _ c _ (a_shift1 f)) ;
  t_subst _ _ (RecL t)  _ f := RecL (t_subst _ _ t _ (a_shift1 f)) ;
  t_subst _ _ (RecR t)  _ f := RecR (t_subst _ _ t _ (a_shift1 f)) ;
  t_subst _ _ (Whn v)   _ f := t_of_v _ (w_subst _ _ v _ f) ;
with w_subst : whn ⇒₁ ⟦ val , val ⟧₁ :=
  w_subst _  _ (Var i)      _ f := f _ i ;
  w_subst _  _ (ZerL)       _ f := Whn ZerL ;
  w_subst _  _ (TopR)       _ f := Whn TopR ;
  w_subst _  _ (OneR)       _ f := OneR ;
  w_subst _  _ (OneL c)     _ f := Whn (OneL (s_subst _ c _ f)) ;
  w_subst _  _ (BotR c)     _ f := Whn (BotR (s_subst _ c _ f)) ;
  w_subst _  _ (BotL)       _ f := BotL ;
  w_subst _  _ (TenR v1 v2) _ f := TenR (w_subst _ _ v1 _ f) (w_subst _ _ v2 _ f) ;
  w_subst _  _ (TenL c)     _ f := Whn (TenL (s_subst _ c _ (a_shift2 f))) ;
  w_subst _  _ (ParR c)     _ f := Whn (ParR (s_subst _ c _ (a_shift2 f))) ;
  w_subst _  _ (ParL k1 k2) _ f := ParL (w_subst _ _ k1 _ f) (w_subst _ _ k2 _ f) ;
  w_subst _  _ (OrR1 v)     _ f := OrR1 (w_subst _ _ v _ f) ;
  w_subst _  _ (OrR2 v)     _ f := OrR2 (w_subst _ _ v _ f) ;
  w_subst _  _ (OrL c1 c2)  _ f := Whn (OrL (s_subst _ c1 _ (a_shift1 f))
                                            (s_subst _ c2 _ (a_shift1 f))) ;
  w_subst _  _ (AndR c1 c2) _ f := Whn (AndR (s_subst _ c1 _ (a_shift1 f))
                                             (s_subst _ c2 _ (a_shift1 f))) ;
  w_subst _  _ (AndL1 k)    _ f := AndL1 (w_subst _ _ k _ f) ;
  w_subst _  _ (AndL2 k)    _ f := AndL2 (w_subst _ _ k _ f) ;
  w_subst _  _ (ShiftPR t)  _ f := ShiftPR (t_subst _ _ t _ f) ;
  w_subst _  _ (ShiftPL c)  _ f := Whn (ShiftPL (s_subst _ c _ (a_shift1 f))) ;
  w_subst _  _ (ShiftNR c)  _ f := Whn (ShiftNR (s_subst _ c _ (a_shift1 f))) ;
  w_subst _  _ (ShiftNL t)  _ f := ShiftNL (t_subst _ _ t _ f) ;
  w_subst _  _ (NegPR k)    _ f := NegPR (w_subst _ _ k _ f) ;
  w_subst _  _ (NegPL c)    _ f := Whn (NegPL (s_subst _ c _ (a_shift1 f))) ;
  w_subst _  _ (NegNR c)    _ f := Whn (NegNR (s_subst _ c _ (a_shift1 f))) ;
  w_subst _  _ (NegNL v)    _ f := NegNL (w_subst _ _ v _ f) ;
with s_subst : state ⇒₀ ⟦ val , state ⟧₀ :=
   s_subst _ (Cut p v k) _ f := Cut p (t_subst _ _ v _ f) (t_subst _ _ k _ f) .

Notation "t `ₜ⊛ a" := (t_subst _ _ t _ a%asgn) (at level 30).
Notation "w `ᵥ⊛ a" := (w_subst _ _ w _ a%asgn) (at level 30).

Equations v_subst : val ⇒₁ ⟦ val , val ⟧₁ :=
  v_subst _ (@VTy pos a) v _ f := v `ᵥ⊛ f ;
  v_subst _ (@KTy pos a) t _ f := t `ₜ⊛ f ;
  v_subst _ (@VTy neg a) t _ f := t `ₜ⊛ f ;
  v_subst _ (@KTy neg a) k _ f := k `ᵥ⊛ f .
(*|
With this in hand we can instanciate the relevant part of substitution monoid and module
structures for values and states. This will provide us with the missing infix notations.
|*)
#[global] Instance val_m_monoid : subst_monoid val :=
  {| v_var := @var ; v_sub := v_subst |} .
#[global] Instance state_module : subst_module val state :=
  {| c_sub := s_subst |} .
(*|
We now define helpers for substituting the top one or top two variables from a context.
|*)
Definition asgn1 {Γ a} (v : val Γ a) : (Γ ▶ₓ a) =[val]> Γ := [ var ,ₓ v ] .
Definition asgn2 {Γ a b} (v1 : val Γ a) (v2 : val Γ b) : (Γ ▶ₓ a ▶ₓ b) =[val]> Γ
  := [ [ var ,ₓ v1 ] ,ₓ v2 ].

Arguments asgn1 {_ _} & _.
Arguments asgn2 {_ _ _} & _ _.

Notation "₁[ v ]" := (asgn1 v).
Notation "₂[ v1 , v2 ]" := (asgn2 v1 v2).
(*|
Observations
============

When defining (co-)patterns, we will enforce a form of focalisation, where no negative
variables are introduced. In this context, 'negative' is a new notion applying to
side-annotated types, mixing both type polarity and side annotation: a side-annotated
variable is positive iff it is a positive variable or a negative co-variable.
|*)
Equations is_neg : ty -> SProp :=
  is_neg (@VTy pos a) := sEmpty ;
  is_neg (@KTy pos a) := sUnit ;
  is_neg (@VTy neg a) := sUnit ;
  is_neg (@KTy neg a) := sEmpty .
(*|
We define negative types as a subset of types, and negative contexts as a subset of
contexts. Our generic infrastructure for contexts and variables really shines here as
the type of variables in a negative context is convertible to the type of variables in
the underlying context. See `Ctx/Subset.v`. 
|*)
Definition neg_ty : Type := sigS is_neg.
Definition neg_coe : neg_ty -> ty := sub_elt.
Global Coercion neg_coe : neg_ty >-> ty.

Definition neg_ctx : Type := ctxS ty t_ctx is_neg.
Definition neg_c_coe : neg_ctx -> ctx ty := sub_elt.
Global Coercion neg_c_coe : neg_ctx >-> ctx.
(*| .. coq:: none |*)
Bind Scope ctx_scope with neg_ctx.
Bind Scope ctx_scope with ctx.
(*|
We can now define patterns...
|*)
Inductive pat : ty -> Type :=
| PVarP (A : ty0 neg) : pat `+A
| PVarN (A : ty0 pos) : pat `-A
| POne : pat `+1
| PBot : pat `-⊥
| PTen {A B} : pat `+A -> pat `+B -> pat `+(A ⊗ B)
| PPar {A B} : pat `-A -> pat `-B -> pat `-(A ⅋ B)
| POr1 {A B} : pat `+A -> pat `+(A ⊕ B)
| POr2 {A B} : pat `+B -> pat `+(A ⊕ B)
| PAnd1 {A B} : pat `-A -> pat `-(A & B)
| PAnd2 {A B} : pat `-B -> pat `-(A & B)
| PShiftP A : pat `+(↓ A)
| PShiftN A : pat `-(↑ A)
| PNegP {A} : pat `-A -> pat `+(⊖ A)
| PNegN {A} : pat `+A -> pat `-(¬ A)
.
(*| .. coq:: none |*)
Derive Signature NoConfusion NoConfusionHom for pat.
(*|
... and their domain, i.e. the context they bind.
|*)
Equations p_dom {t} : pat t -> neg_ctx :=
  p_dom (PVarP A)    := ∅ₛ ▶ₛ {| sub_elt := `+A ; sub_prf := stt |} ;
  p_dom (PVarN A)    := ∅ₛ ▶ₛ {| sub_elt := `-A ; sub_prf := stt |} ;
  p_dom (POne)       := ∅ₛ ;
  p_dom (PBot)       := ∅ₛ ;
  p_dom (PTen p1 p2) := p_dom p1 +▶ₛ p_dom p2 ;
  p_dom (PPar p1 p2) := p_dom p1 +▶ₛ p_dom p2 ;
  p_dom (POr1 p)     := p_dom p ;
  p_dom (POr2 p)     := p_dom p ;
  p_dom (PAnd1 p)    := p_dom p ;
  p_dom (PAnd2 p)    := p_dom p ;
  p_dom (PShiftP A)  := ∅ₛ ▶ₛ {| sub_elt := `+A ; sub_prf := stt |} ;
  p_dom (PShiftN A)  := ∅ₛ ▶ₛ {| sub_elt := `-A ; sub_prf := stt |} ;
  p_dom (PNegP p)    := p_dom p ;
  p_dom (PNegN p)    := p_dom p .
(*|
We finally instanciate the observation structure. Note that our generic formalization
mostly cares about 'observations', that is co-patterns. As such we instanciate observations
by patterns at the dual type.
|*)
Definition obs_op : Oper ty neg_ctx :=
  {| o_op A := pat A† ; o_dom _ p := p_dom p |} .
(*|
Now come a rather tedious set of embeddings between syntactic categories related to
patterns. We start by embedding patterns into weak head-normal forms.
|*)
Equations w_of_p {a} (p : pat a) : whn (p_dom p) a :=
  w_of_p (PVarP _)    := Var top ;
  w_of_p (PVarN _)    := Var top ;
  w_of_p (POne)       := OneR ;
  w_of_p (PBot)       := BotL ;
  w_of_p (PTen p1 p2) := TenR (w_of_p p1 `ᵥ⊛ᵣ r_cat_l) (w_of_p p2 `ᵥ⊛ᵣ r_cat_r) ;
  w_of_p (PPar p1 p2) := ParL (w_of_p p1 `ᵥ⊛ᵣ r_cat_l) (w_of_p p2 `ᵥ⊛ᵣ r_cat_r) ;
  w_of_p (POr1 p)     := OrR1 (w_of_p p) ;
  w_of_p (POr2 p)     := OrR2 (w_of_p p) ;
  w_of_p (PAnd1 p)    := AndL1 (w_of_p p) ;
  w_of_p (PAnd2 p)    := AndL2 (w_of_p p) ;
  w_of_p (PShiftP _)  := ShiftPR (Whn (Var top)) ;
  w_of_p (PShiftN _)  := ShiftNL (Whn (Var top)) ;
  w_of_p (PNegP p)    := NegPR (w_of_p p) ;
  w_of_p (PNegN p)    := NegNL (w_of_p p) .
(*|
Now we explain how to split (some) weak head-normal forms into a pattern filled with
values. I am sorry in advance for your CPU-cycles wasted to typechecking these quite
hard dependent pattern matchings. We start off by two helpers for refuting impossible
variables in negative context, which because of the use of `SProp` give trouble to
`Equations` for deriving functional elimination principles if inlined.
|*)
Definition elim_var_p {Γ : neg_ctx} {A : ty0 pos} {X : Type} : Γ ∋ `+A -> X
  := fun i => match s_prf i with end .

Definition elim_var_n {Γ : neg_ctx} {A : ty0 neg} {X : Type} : Γ ∋ `-A -> X
  := fun i => match s_prf i with end .

Equations p_of_w_0p {Γ : neg_ctx} (A : ty0 pos) : whn Γ `+A -> pat `+A :=
  p_of_w_0p (0)     (Var i)      := elim_var_p i ;
  p_of_w_0p (1)     (Var i)      := elim_var_p i ;
  p_of_w_0p (A ⊗ B) (Var i)      := elim_var_p i ;
  p_of_w_0p (A ⊕ B) (Var i)      := elim_var_p i ;
  p_of_w_0p (↓ A)   (Var i)      := elim_var_p i ;
  p_of_w_0p (⊖ A)   (Var i)      := elim_var_p i ;
  p_of_w_0p (1)     (OneR)       := POne ;
  p_of_w_0p (A ⊗ B) (TenR v1 v2) := PTen (p_of_w_0p A v1) (p_of_w_0p B v2) ;
  p_of_w_0p (A ⊕ B) (OrR1 v)     := POr1 (p_of_w_0p A v) ;
  p_of_w_0p (A ⊕ B) (OrR2 v)     := POr2 (p_of_w_0p B v) ;
  p_of_w_0p (↓ A)   (ShiftPR _)  := PShiftP A ;
  p_of_w_0p (⊖ A)   (NegPR k)    := PNegP (p_of_w_0n A k) ;
with p_of_w_0n {Γ : neg_ctx} (A : ty0 neg) : whn Γ `-A -> pat `-A :=
  p_of_w_0n (⊤)     (Var i)      := elim_var_n i ;
  p_of_w_0n (⊥)     (Var i)      := elim_var_n i ;
  p_of_w_0n (A ⅋ B) (Var i)      := elim_var_n i ;
  p_of_w_0n (A & B) (Var i)      := elim_var_n i ;
  p_of_w_0n (↑ A)   (Var i)      := elim_var_n i ;
  p_of_w_0n (¬ A)   (Var i)      := elim_var_n i ;
  p_of_w_0n (⊥)     (BotL)       := PBot ;
  p_of_w_0n (A ⅋ B) (ParL k1 k2) := PPar (p_of_w_0n A k1) (p_of_w_0n B k2) ;
  p_of_w_0n (A & B) (AndL1 k)    := PAnd1 (p_of_w_0n A k) ;
  p_of_w_0n (A & B) (AndL2 k)    := PAnd2 (p_of_w_0n B k) ;
  p_of_w_0n (↑ A)   (ShiftNL _)  := PShiftN A ;
  p_of_w_0n (¬ A)   (NegNL v)    := PNegN (p_of_w_0p A v) .

Equations p_dom_of_w_0p {Γ : neg_ctx} (A : ty0 pos) (v : whn Γ `+A)
          : p_dom (p_of_w_0p A v) =[val]> Γ by struct A :=
  p_dom_of_w_0p (0)     (Var i)      := elim_var_p i ;
  p_dom_of_w_0p (1)     (Var i)      := elim_var_p i ;
  p_dom_of_w_0p (A ⊗ B) (Var i)      := elim_var_p i ;
  p_dom_of_w_0p (A ⊕ B) (Var i)      := elim_var_p i ;
  p_dom_of_w_0p (↓ A)   (Var i)      := elim_var_p i ;
  p_dom_of_w_0p (⊖ A)   (Var i)      := elim_var_p i ;
  p_dom_of_w_0p (1)     (OneR)       := a_empty ;
  p_dom_of_w_0p (A ⊗ B) (TenR v1 v2) := [ p_dom_of_w_0p A v1 , p_dom_of_w_0p B v2 ] ;
  p_dom_of_w_0p (A ⊕ B) (OrR1 v)     := p_dom_of_w_0p A v ;
  p_dom_of_w_0p (A ⊕ B) (OrR2 v)     := p_dom_of_w_0p B v ;
  p_dom_of_w_0p (↓ A)   (ShiftPR x)  := a_append a_empty x ;
  p_dom_of_w_0p (⊖ A)   (NegPR k)    := p_dom_of_w_0n A k ;
     with p_dom_of_w_0n {Γ : neg_ctx} (A : ty0 neg) (k : whn Γ `-A)
          : p_dom (p_of_w_0n A k) =[val]> Γ by struct A :=
  p_dom_of_w_0n (⊤)     (Var i)      := elim_var_n i ;
  p_dom_of_w_0n (⊥)     (Var i)      := elim_var_n i ;
  p_dom_of_w_0n (A ⅋ B) (Var i)      := elim_var_n i ;
  p_dom_of_w_0n (A & B) (Var i)      := elim_var_n i ;
  p_dom_of_w_0n (↑ A)   (Var i)      := elim_var_n i ;
  p_dom_of_w_0n (¬ A)   (Var i)      := elim_var_n i ;
  p_dom_of_w_0n (⊥)     (BotL)       := a_empty ;
  p_dom_of_w_0n (A ⅋ B) (ParL k1 k2) := [ p_dom_of_w_0n A k1 , p_dom_of_w_0n B k2 ] ;
  p_dom_of_w_0n (A & B) (AndL1 k)    := p_dom_of_w_0n A k ;
  p_dom_of_w_0n (A & B) (AndL2 k)    := p_dom_of_w_0n B k ;
  p_dom_of_w_0n (↑ A)   (ShiftNL x)  := a_append a_empty x ;
  p_dom_of_w_0n (¬ A)   (NegNL v)    := p_dom_of_w_0p A v .
(*|
We can now package up all these auxiliary functions into the following ones, abstracting
polarity and side-annotation.
|*)
Equations p_of_v {Γ : neg_ctx} A : val Γ A -> pat A :=
  p_of_v (@VTy pos A) v := p_of_w_0p A v ;
  p_of_v (@KTy pos A) _ := PVarN A ;
  p_of_v (@VTy neg A) _ := PVarP A ;
  p_of_v (@KTy neg A) k := p_of_w_0n A k .

Equations p_dom_of_v {Γ : neg_ctx} A (v : val Γ A) : p_dom (p_of_v A v) =[val]> Γ :=
  p_dom_of_v (@VTy pos A) v := p_dom_of_w_0p A v ;
  p_dom_of_v (@KTy pos A) x := [ ! ,ₓ x ] ;
  p_dom_of_v (@VTy neg A) x := [ ! ,ₓ x ] ;
  p_dom_of_v (@KTy neg A) k := p_dom_of_w_0n A k .

Definition v_split_p {Γ : neg_ctx} {A} (v : whn Γ `+A) : (obs_op # val) Γ `-A
  := (p_of_w_0p A v : o_op obs_op `-A) ⦇ p_dom_of_w_0p A v ⦈.

Definition v_split_n {Γ : neg_ctx} {A} (v : whn Γ `-A) : (obs_op # val) Γ `+A
  := (p_of_w_0n A v : o_op obs_op `+_) ⦇ p_dom_of_w_0n A v ⦈.
(*|
Evaluation
==========

With patterns and observations now in hand we prepare for the definition of evaluation
and define a shorthand for normal forms. 'Normal forms' are here understood---as in the
paper---in our slightly non-standard presentation of triplets of a variable, an
observation and an assignment.
|*)
Definition nf : Fam₀ ty neg_ctx := c_var ∥ₛ (obs_op # val).
(*|
Now the bulk of evaluation: the step function. Once again we are greatful for
`Equations` providing us with a justification for the fact that this complex
dependent pattern-matching is indeed total.
|*)
Equations eval_aux {Γ : neg_ctx} : state Γ -> (state Γ + nf Γ) :=
  eval_aux (Cut pos (Mu c)  (x))    := inl (c ₜ⊛ ₁[ x ]) ;
  eval_aux (Cut neg (x)     (Mu c)) := inl (c ₜ⊛ ₁[ x ]) ;

  eval_aux (Cut pos (Whn v) (Mu c))  := inl (c ₜ⊛ ₁[ v ]) ;
  eval_aux (Cut neg (Mu c)  (Whn k)) := inl (c ₜ⊛ ₁[ k ]) ;

  eval_aux (Cut pos (Whn v)  (RecL k)) := inl (Cut pos (Whn v) (k `ₜ⊛ ₁[ RecL k ])) ;
  eval_aux (Cut neg (RecR t) (Whn k))  := inl (Cut neg (t `ₜ⊛ ₁[ RecR t ]) (Whn k)) ;

  eval_aux (Cut pos (Whn v)       (Whn (Var i))) := inr (s_var_upg i ⋅ v_split_p v) ;
  eval_aux (Cut neg (Whn (Var i)) (Whn k))       := inr (s_var_upg i ⋅ v_split_n k) ;

  eval_aux (Cut pos (Whn (Var i)) (Whn _))       := elim_var_p i ;
  eval_aux (Cut neg (Whn _)       (Whn (Var i))) := elim_var_n i ;

  eval_aux (Cut pos (Whn (OneR))       (Whn (OneL c)))     := inl c ;
  eval_aux (Cut neg (Whn (BotR c))     (Whn (BotL)))       := inl c ;
  eval_aux (Cut pos (Whn (TenR v1 v2)) (Whn (TenL c)))     := inl (c ₜ⊛ ₂[ v1 , v2 ]) ;
  eval_aux (Cut neg (Whn (ParR c))     (Whn (ParL k1 k2))) := inl (c ₜ⊛ ₂[ k1 , k2 ]) ;
  eval_aux (Cut pos (Whn (OrR1 v))     (Whn (OrL c1 c2)))  := inl (c1 ₜ⊛ ₁[ v ]) ;
  eval_aux (Cut pos (Whn (OrR2 v))     (Whn (OrL c1 c2)))  := inl (c2 ₜ⊛ ₁[ v ]) ;
  eval_aux (Cut neg (Whn (AndR c1 c2)) (Whn (AndL1 k)))    := inl (c1 ₜ⊛ ₁[ k ]) ;
  eval_aux (Cut neg (Whn (AndR c1 c2)) (Whn (AndL2 k)))    := inl (c2 ₜ⊛ ₁[ k ]) ;
  eval_aux (Cut pos (Whn (ShiftPR x))  (Whn (ShiftPL c)))  := inl (c ₜ⊛ ₁[ x ]) ;
  eval_aux (Cut neg (Whn (ShiftNR c))  (Whn (ShiftNL x)))  := inl (c ₜ⊛ ₁[ x ]) ;
  eval_aux (Cut pos (Whn (NegPR k))    (Whn (NegPL c)))    := inl (c ₜ⊛ ₁[ k ]) ;
  eval_aux (Cut neg (Whn (NegNR c))    (Whn (NegNL v)))    := inl (c ₜ⊛ ₁[ v ]) .
(*|
Finally we define evaluation as the iteration of the step function in the Delay monad,
and also define application of an observation with arguments to a value.
|*)
Definition eval {Γ : neg_ctx} : state Γ -> delay (nf Γ)
  := iter_delay (fun c => Ret' (eval_aux c)).

Definition p_app {Γ A} (v : val Γ A) (m : pat A†) (e : p_dom m =[val]> Γ) : state Γ :=
  Cut' (t_of_v _ v) (t_of_v _ (w_of_p m `ᵥ⊛ e)) .
(*|
Metatheory
==========

Now comes a rather ugly part: the metatheory of our syntax. Comments will be rather more
sparse. For a thorough explaination of its structure, see `Examples/Lambda/CBVTyped.v`.
We will here be concerned with extensional equality preservation, identity and composition
laws for renaming and substitution, and also refolding lemmas for splitting and embedding
patterns. You are encouraged to just skip until line ~1300.
|*)
Scheme term_mut := Induction for term Sort Prop
  with whn_mut := Induction for whn Sort Prop
  with state_mut := Induction for state Sort Prop.

Record syn_ind_args
  (P_t : forall Γ A, term Γ A -> Prop)
  (P_w : forall Γ A, whn Γ A -> Prop)
  (P_s : forall Γ, state Γ -> Prop) :=
{
  ind_mu : forall Γ A s (H : P_s _ s), P_t Γ A (Mu s) ;
  ind_recp : forall Γ A t (H : P_t _ _ t), P_t Γ `-A (RecL t) ;
  ind_recn : forall Γ A t (H : P_t _ _ t), P_t Γ `+A (RecR t) ;
  ind_whn : forall Γ A w (H : P_w _ _ w), P_t Γ A (Whn w) ;
  ind_var : forall Γ A h, P_w Γ A (Var h) ;
  ind_zerl : forall Γ, P_w Γ `-0 ZerL ;
  ind_topr : forall Γ, P_w Γ `+⊤ TopR ;
  ind_oner : forall Γ, P_w Γ `+1 OneR ;
  ind_onel : forall Γ s, P_s Γ s -> P_w Γ `-1 (OneL s) ;
  ind_botr : forall Γ s, P_s Γ s -> P_w Γ `+⊥ (BotR s) ;
  ind_botl : forall Γ, P_w Γ `-⊥ BotL ;
  ind_tenr : forall Γ A B w1 (H1 : P_w _ _ w1) w2 (H2 : P_w _ _ w2), P_w Γ `+(A ⊗ B) (TenR w1 w2) ;
  ind_tenl : forall Γ A B s (H : P_s _ s), P_w Γ `-(A ⊗ B) (TenL s) ;
  ind_parr : forall Γ A B s (H : P_s _ s), P_w Γ `+(A ⅋ B) (ParR s) ;
  ind_parl : forall Γ A B w1 (H1 : P_w _ _ w1) w2 (H2 : P_w Γ `-B w2), P_w Γ `-(A ⅋ B) (ParL w1 w2) ;
  ind_orr1 : forall Γ A B w (H : P_w _ _ w), P_w Γ `+(A ⊕ B) (OrR1 w) ;
  ind_orr2 : forall Γ A B w (H : P_w _ _ w), P_w Γ `+(A ⊕ B) (OrR2 w) ;
  ind_orl : forall Γ A B s1 (H1 : P_s _ s1) s2 (H2 : P_s _ s2), P_w Γ `-(A ⊕ B) (OrL s1 s2) ;
  ind_andr : forall Γ A B s1 (H1 : P_s _ s1) s2 (H2 : P_s _ s2), P_w Γ `+(A & B) (AndR s1 s2) ;
  ind_andl1 : forall Γ A B w (H : P_w _ _ w), P_w Γ `-(A & B) (AndL1 w) ;
  ind_andl2 : forall Γ A B w (H : P_w _ _ w), P_w Γ `-(A & B) (AndL2 w) ;
  ind_shiftpr : forall Γ A t (H : P_t _ _ t), P_w Γ `+(↓ A) (ShiftPR t) ;
  ind_shiftpl : forall Γ A s (H : P_s _ s), P_w Γ `-(↓ A) (ShiftPL s) ;
  ind_shiftnr : forall Γ A s (H : P_s _ s), P_w Γ `+(↑ A) (ShiftNR s) ;
  ind_shiftnl : forall Γ A t (H : P_t _ _ t), P_w Γ `-(↑ A) (ShiftNL t) ;
  ind_negpr : forall Γ A w (H : P_w _ _ w), P_w Γ `+(⊖ A) (NegPR w) ;
  ind_negpl : forall Γ A s (H : P_s _ s), P_w Γ `-(⊖ A) (NegPL s) ;
  ind_negnr : forall Γ A s (H : P_s _ s), P_w Γ `+(¬ A) (NegNR s) ;
  ind_negnl : forall Γ A w (H : P_w _ _ w), P_w Γ `-(¬ A) (NegNL w) ;
  ind_cut : forall Γ p A t1 (H1 : P_t _ _ t1) t2 (H2 : P_t _ _ t2), P_s Γ (@Cut _ p A t1 t2)
} .

Lemma term_ind_mut P_t P_w P_s (H : syn_ind_args P_t P_w P_s) Γ A t : P_t Γ A t .
  destruct H; now apply (term_mut P_t P_w P_s).
Qed.

Lemma whn_ind_mut P_t P_w P_s (H : syn_ind_args P_t P_w P_s) Γ A w : P_w Γ A w .
  destruct H; now apply (whn_mut P_t P_w P_s).
Qed.

Lemma state_ind_mut P_t P_w P_s (H : syn_ind_args P_t P_w P_s) Γ s : P_s Γ s .
  destruct H; now apply (state_mut P_t P_w P_s).
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
  all: intros; cbn; f_equal; eauto.
  all: first [ apply H | apply H1 | apply H2 ]; auto.
  all: first [ apply r_shift1_eq | apply r_shift2_eq ]; auto.
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
  destruct a as [ [] | [] ].
  now apply w_ren_eq.
  now apply t_ren_eq.
  now apply t_ren_eq.
  now apply w_ren_eq.
Qed.

#[global] Instance a_ren_eq {Γ1 Γ2 Γ3}
  : Proper (asgn_eq _ _ ==> asgn_eq _ _ ==> asgn_eq _ _) (@a_ren Γ1 Γ2 Γ3).
  intros r1 r2 H1 a1 a2 H2 ? i; cbn; now rewrite H1, (v_ren_eq _ _ H2).
Qed.

#[global] Instance a_shift1_eq {Γ Δ A} : Proper (asgn_eq _ _ ==> asgn_eq _ _) (@a_shift1 Γ Δ A).
  intros ? ? H ? h.
  dependent elimination h; auto; cbn; now rewrite H.
Qed.

#[global] Instance a_shift2_eq {Γ Δ A B} : Proper (asgn_eq _ _ ==> asgn_eq _ _) (@a_shift2 Γ Δ A B).
  intros ? ? H ? v.
  do 2 (dependent elimination v; auto).
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
  all: first [ rewrite r_shift1_comp | rewrite r_shift2_comp ]; eauto.
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
  destruct A as [ [] | [] ].
  now apply w_ren_ren.
  now apply t_ren_ren.
  now apply t_ren_ren.
  now apply w_ren_ren.
Qed.

Definition t_ren_id_l_P Γ A (t : term Γ A) : Prop := t ₜ⊛ᵣ r_id = t.
Definition w_ren_id_l_P Γ A (v : whn Γ A) : Prop := v `ᵥ⊛ᵣ r_id = v.
Definition s_ren_id_l_P Γ (s : state Γ) : Prop := s ₛ⊛ᵣ r_id  = s.

Lemma ren_id_l_prf : syn_ind_args t_ren_id_l_P w_ren_id_l_P s_ren_id_l_P.
  econstructor.
  all: unfold t_ren_id_l_P, w_ren_id_l_P, s_ren_id_l_P.
  all: intros; cbn; f_equal; eauto.
  all: first [ rewrite r_shift1_id | rewrite r_shift2_id ]; eauto.
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
  destruct A as [ [] | [] ].
  now apply w_ren_id_l.
  now apply t_ren_id_l.
  now apply t_ren_id_l.
  now apply w_ren_id_l.
Qed.

Lemma v_ren_id_r {Γ Δ} (f : Γ ⊆ Δ) A (i : Γ ∋ A) : (var i) ᵥ⊛ᵣ f = var (f _ i).
  now destruct A as [ [] | [] ].
Qed.

Lemma a_shift1_id {Γ A} : @a_shift1 Γ Γ A var ≡ₐ var.
  intros [ [] | [] ] i; dependent elimination i; auto.
Qed.

Lemma a_shift2_id {Γ A B} : @a_shift2 Γ Γ A B var ≡ₐ var.
  intros ? v; cbn.
  do 2 (dependent elimination v; cbn; auto).
  now destruct a as [[]|[]].
Qed.

Arguments var : simpl never.
Lemma a_shift1_ren_r {Γ1 Γ2 Γ3 y} (f1 : Γ1 =[ val ]> Γ2) (f2 : Γ2 ⊆ Γ3)
      : a_shift1 (y:=y) (f1 ⊛ᵣ f2) ≡ₐ a_shift1 f1 ⊛ᵣ r_shift1 f2 .
  intros ? h; dependent elimination h; cbn.
  - now rewrite v_ren_id_r.
  - now unfold v_shift1; rewrite 2 v_ren_ren.
Qed.

Lemma a_shift2_ren_r {Γ1 Γ2 Γ3 y z} (f1 : Γ1 =[ val ]> Γ2) (f2 : Γ2 ⊆ Γ3)
      : a_shift2 (y:=y) (z:=z) (f1 ⊛ᵣ f2) ≡ₐ a_shift2 f1 ⊛ᵣ r_shift2 f2 .
  intros ? v; do 2 (dependent elimination v; cbn; [ now rewrite v_ren_id_r | ]).
  unfold v_shift2; now rewrite 2 v_ren_ren.
Qed.

Lemma a_shift1_ren_l {Γ1 Γ2 Γ3 y} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val]> Γ3)
  : a_shift1 (y:=y) (f1 ᵣ⊛ f2) ≡ₐ r_shift1 f1 ᵣ⊛ a_shift1 f2 .
  intros ? i; dependent elimination i; auto.
Qed.

Lemma a_shift2_ren_l {Γ1 Γ2 Γ3 y z} (f1 : Γ1 ⊆ Γ2) (f2 : Γ2 =[val]> Γ3)
      : a_shift2 (y:=y) (z:=z) (f1 ᵣ⊛ f2) ≡ₐ r_shift2 f1 ᵣ⊛ a_shift2 f2 .
  intros ? v; do 2 (dependent elimination v; auto).
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
  all: intros; cbn.
  all: match goal with
       | |- Whn _ = Whn _ => do 2 f_equal
       | _ => f_equal
       end .
  all: first [ apply H | apply H1 | apply H2 ]; auto.
  all: first [ apply a_shift1_eq | apply a_shift2_eq ]; auto.
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
  destruct a as [[]|[]].
  - now apply w_sub_eq.
  - now apply t_sub_eq.
  - now apply t_sub_eq.
  - now apply w_sub_eq.
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
    (v `ᵥ⊛ f1) ᵥ⊛ᵣ f2 = v `ᵥ⊛ (f1 ⊛ᵣ f2) .
Definition s_ren_sub_P Γ1 (s : state Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 ⊆ Γ3),
    (s ₜ⊛ f1) ₛ⊛ᵣ f2 = s ₜ⊛ (f1 ⊛ᵣ f2) .
Lemma ren_sub_prf : syn_ind_args t_ren_sub_P w_ren_sub_P s_ren_sub_P.
  econstructor.
  all: unfold t_ren_sub_P, w_ren_sub_P, s_ren_sub_P.
  all: intros; cbn.
  4: destruct A as [ [] | [] ]; cbn.
  all: match goal with
       | |- Whn _ = Whn _ => do 2 f_equal
       | _ => f_equal
       end ; eauto.
  all: first [ rewrite a_shift1_ren_r | rewrite a_shift2_ren_r ]; auto.
Qed.

Lemma t_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 ⊆ Γ3) A (t : term Γ1 A)
  : (t `ₜ⊛ f1) ₜ⊛ᵣ f2 = t `ₜ⊛ (f1 ⊛ᵣ f2) .
  now apply (term_ind_mut _ _ _ ren_sub_prf).
Qed.
Lemma w_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 ⊆ Γ3) A (v : whn Γ1 A)
  : (v `ᵥ⊛ f1) ᵥ⊛ᵣ f2 = v `ᵥ⊛ (f1 ⊛ᵣ f2) .
  now apply (whn_ind_mut _ _ _ ren_sub_prf).
Qed.
Lemma s_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 ⊆ Γ3) (s : state Γ1)
  : (s ₜ⊛ f1) ₛ⊛ᵣ f2 = s ₜ⊛ (f1 ⊛ᵣ f2) .
  now apply (state_ind_mut _ _ _ ren_sub_prf).
Qed.
Lemma v_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 ⊆ Γ3) A (v : val Γ1 A)
  : (v ᵥ⊛ f1) ᵥ⊛ᵣ f2 = v ᵥ⊛ (f1 ⊛ᵣ f2) .
  destruct A as [ [] | [] ]; cbn [ v_subst ].
  - now apply w_ren_sub.
  - now apply t_ren_sub.
  - now apply t_ren_sub.
  - now apply w_ren_sub.
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
  all: intros; cbn.
  all: match goal with
       | |- Whn _ = Whn _ => do 2 f_equal
       | _ => f_equal
       end ; eauto.
  all: first [ rewrite a_shift1_ren_l | rewrite a_shift2_ren_l ]; auto.
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
  destruct A as [ [] | [] ].
  - now apply w_sub_ren.
  - now apply t_sub_ren.
  - now apply t_sub_ren.
  - now apply w_sub_ren.
Qed.

Lemma v_sub_id_r {Γ Δ} (f : Γ =[val]> Δ) A (i : Γ ∋ A) : var i ᵥ⊛ f = f A i.
  destruct A as [ [] | [] ]; auto.
Qed.

Lemma a_shift1_comp {Γ1 Γ2 Γ3 A} (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 =[val]> Γ3)
  : @a_shift1 _ _ A (f1 ⊛ f2) ≡ₐ a_shift1 f1 ⊛ a_shift1 f2 .
  intros x i; dependent elimination i; cbn.
  - now rewrite v_sub_id_r.
  - now unfold v_shift1; rewrite v_ren_sub, v_sub_ren.
Qed.

Lemma a_shift2_comp {Γ1 Γ2 Γ3 A B} (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 =[val]> Γ3)
  : @a_shift2 _ _ A B (f1 ⊛ f2) ≡ₐ a_shift2 f1 ⊛ a_shift2 f2 .
  intros ? v; do 2 (dependent elimination v; cbn; [ now rewrite v_sub_id_r | ]).
  now unfold v_shift2; rewrite v_ren_sub, v_sub_ren.
Qed.

Definition t_sub_sub_P Γ1 A (t : term Γ1 A) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 =[val]> Γ3),
    (t `ₜ⊛ f1) `ₜ⊛ f2 = t `ₜ⊛ (f1 ⊛ f2) .
Definition w_sub_sub_P Γ1 A (v : whn Γ1 A) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 =[val]> Γ3),
    (v `ᵥ⊛ f1) ᵥ⊛ f2 = v `ᵥ⊛ (f1 ⊛ f2) .
Definition s_sub_sub_P Γ1 (s : state Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 =[val]> Γ3),
    (s ₜ⊛ f1) ₜ⊛ f2 = s ₜ⊛ (f1 ⊛ f2) .

Lemma sub_sub_prf : syn_ind_args t_sub_sub_P w_sub_sub_P s_sub_sub_P.
  econstructor.
  all: unfold t_sub_sub_P, w_sub_sub_P, s_sub_sub_P; intros; cbn.
  4: destruct A as [ [] | [] ]; cbn.
  all: match goal with
       | |- Whn _ = Whn _ => do 2 f_equal
       | _ => f_equal
       end ; eauto.
  all: first [ rewrite a_shift1_comp | rewrite a_shift2_comp ]; auto.
Qed.

Lemma t_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 =[val]> Γ3) A (t : term Γ1 A)
  : (t `ₜ⊛ f1) `ₜ⊛ f2 = t `ₜ⊛ (f1 ⊛ f2) .
  now apply (term_ind_mut _ _ _ sub_sub_prf).
Qed.
Lemma w_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 =[val]> Γ3) A (v : whn Γ1 A)
  : (v `ᵥ⊛ f1) ᵥ⊛ f2 = v `ᵥ⊛ (f1 ⊛ f2) .
  now apply (whn_ind_mut _ _ _ sub_sub_prf).
Qed.
Lemma s_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 =[val]> Γ3) (s : state Γ1)
  : (s ₜ⊛ f1) ₜ⊛ f2 = s ₜ⊛ (f1 ⊛ f2) .
  now apply (state_ind_mut _ _ _ sub_sub_prf).
Qed.
Lemma v_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ1 =[val]> Γ2) (f2 : Γ2 =[val]> Γ3) A (v : val Γ1 A)
  : (v ᵥ⊛ f1) ᵥ⊛ f2 = v ᵥ⊛ (f1 ⊛ f2) .
  destruct A as [ [] | [] ].
  - now apply w_sub_sub.
  - now apply t_sub_sub.
  - now apply t_sub_sub.
  - now apply w_sub_sub.
Qed.

Lemma a_comp_assoc {Γ1 Γ2 Γ3 Γ4} (u : Γ1 =[val]> Γ2) (v : Γ2 =[val]> Γ3) (w : Γ3 =[val]> Γ4)
           : (u ⊛ v) ⊛ w ≡ₐ u ⊛ (v ⊛ w).
  intros ? i; unfold a_comp; now apply v_sub_sub.
Qed.

Definition t_sub_id_l_P Γ A (t : term Γ A) : Prop := t `ₜ⊛ var = t.
Definition w_sub_id_l_P Γ A (v : whn Γ A) : Prop := v `ᵥ⊛ var = v_of_w _ v.
Definition s_sub_id_l_P Γ (s : state Γ) : Prop := s ₜ⊛ var = s.

Lemma sub_id_l_prf : syn_ind_args t_sub_id_l_P w_sub_id_l_P s_sub_id_l_P.
  econstructor.
  all: unfold t_sub_id_l_P, w_sub_id_l_P, s_sub_id_l_P; intros; cbn.
  4,5: destruct A as [ [] | [] ]; cbn.
  all: match goal with
       | |- Whn _ = Whn _ => do 2 f_equal
       | _ => f_equal
       end; eauto.
  all: first [ rewrite a_shift1_id | rewrite a_shift2_id ]; auto.
Qed.

Lemma t_sub_id_l {Γ} A (t : term Γ A) : t `ₜ⊛ var = t.
  now apply (term_ind_mut _ _ _ sub_id_l_prf).
Qed.
Lemma w_sub_id_l {Γ} A (v : whn Γ A) : v `ᵥ⊛ var = v_of_w _ v.
  now apply (whn_ind_mut _ _ _ sub_id_l_prf).
Qed.
Lemma s_sub_id_l {Γ} (s : state Γ) : s ₜ⊛ var = s.
  now apply (state_ind_mut _ _ _ sub_id_l_prf).
Qed.
Lemma v_sub_id_l {Γ} A (v : val Γ A) : v ᵥ⊛ var = v.
  destruct A as [ [] | [] ].
  - now apply w_sub_id_l.
  - now apply t_sub_id_l.
  - now apply t_sub_id_l.
  - now apply w_sub_id_l.
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

Lemma s_sub2_sub {Γ Δ A B} (f : Γ =[val]> Δ) (s : state (Γ ▶ₓ A ▶ₓ B)) u v
  : (s ₜ⊛ a_shift2 f) ₜ⊛ ₂[ u ᵥ⊛ f , v ᵥ⊛ f ] = (s ₜ⊛ ₂[ u, v ]) ₜ⊛ f .
  cbn; rewrite 2 s_sub_sub; apply s_sub_eq.
  intros ? v0; cbn.
  do 2 (dependent elimination v0; cbn; [ now rewrite v_sub_id_r | ]).
  unfold v_shift2; rewrite v_sub_ren, v_sub_id_r, <- v_sub_id_l.
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
  intros u1 u2 H; destruct A as [ [] | []]; cbn; now rewrite (w_sub_eq u1 u2 H).
Qed.

Definition refold_id_aux_P (Γ : neg_ctx) p : ty0 p -> Prop :=
  match p with
  | pos => fun A => forall (v : whn Γ `+A), w_of_p (p_of_w_0p _ v) `ᵥ⊛ p_dom_of_w_0p _ v = v
  | neg => fun A => forall (v : whn Γ `-A), w_of_p (p_of_w_0n _ v) `ᵥ⊛ p_dom_of_w_0n _ v = v
  end .

Lemma refold_id_aux {Γ p} A : refold_id_aux_P Γ p A .
  induction A; intros v.
  - dependent elimination v; destruct (s_prf c).
  - dependent elimination v; destruct (s_prf c).
  - dependent elimination v; [ destruct (s_prf c) | ]; auto.
  - dependent elimination v; [ destruct (s_prf c) | ]; auto.
  - dependent elimination v; [ destruct (s_prf c) | ].
    cbn; f_equal; rewrite w_sub_ren.
    rewrite <- IHA1; apply w_sub_eq; exact (a_cat_proj_l _ _).
    rewrite <- IHA2; apply w_sub_eq; exact (a_cat_proj_r _ _).
  - dependent elimination v; [ destruct (s_prf c) | ].
    cbn; f_equal; rewrite w_sub_ren.
    rewrite <- IHA1; apply w_sub_eq; exact (a_cat_proj_l _ _).
    rewrite <- IHA2; apply w_sub_eq; exact (a_cat_proj_r _ _).
  - dependent elimination v; [ destruct (s_prf c) | | ];
      cbn; f_equal; [ apply IHA1 | apply IHA2 ].
  - dependent elimination v; [ destruct (s_prf c) | | ];
      cbn; f_equal; [ apply IHA1 | apply IHA2 ].
  - dependent elimination v; [ destruct (s_prf c) | ]; cbn; f_equal.
  - dependent elimination v; [ destruct (s_prf c) | ]; cbn; f_equal.
  - dependent elimination v; [ destruct (s_prf c) | ].
    cbn; f_equal; apply IHA.
  - dependent elimination v; [ destruct (s_prf c) | ].
    cbn; f_equal; apply IHA.
Qed.

Lemma refold_id {Γ : neg_ctx} A (v : val Γ A)
  : w_of_p (p_of_v A v) `ᵥ⊛ p_dom_of_v A v = v.
  destruct A as [ [] A | [] A ]; auto; exact (refold_id_aux A v).
Qed.

Equations p_of_w_eq_aux_p {Γ : neg_ctx} (A : ty0 pos) (p : pat `+A) (e : p_dom p =[val]> Γ)
          : p_of_w_0p A (w_of_p p `ᵥ⊛ e) = p
          by struct p :=
  p_of_w_eq_aux_p (1)     (POne)       e := eq_refl ;
  p_of_w_eq_aux_p (A ⊗ B) (PTen p1 p2) e := f_equal2 PTen
        (eq_trans (f_equal _ (w_sub_ren _ _ _ _)) (p_of_w_eq_aux_p A p1 _))
        (eq_trans (f_equal _ (w_sub_ren _ _ _ _)) (p_of_w_eq_aux_p B p2 _)) ;
  p_of_w_eq_aux_p (A ⊕ B) (POr1 p)     e := f_equal POr1 (p_of_w_eq_aux_p A p e) ;
  p_of_w_eq_aux_p (A ⊕ B) (POr2 p)     e := f_equal POr2 (p_of_w_eq_aux_p B p e) ;
  p_of_w_eq_aux_p (↓ A)   (PShiftP _)  e := eq_refl ;
  p_of_w_eq_aux_p (⊖ A)   (PNegP p)    e := f_equal PNegP (p_of_w_eq_aux_n A p e) ;

with p_of_w_eq_aux_n {Γ : neg_ctx} (A : ty0 neg) (p : pat `-A) (e : p_dom p =[val]> Γ)
         : p_of_w_0n A (w_of_p p `ᵥ⊛ e) = p
         by struct p :=
  p_of_w_eq_aux_n (⊥)     (PBot)       e := eq_refl ;
  p_of_w_eq_aux_n (A ⅋ B) (PPar p1 p2) e := f_equal2 PPar
        (eq_trans (f_equal _ (w_sub_ren _ _ _ _)) (p_of_w_eq_aux_n A p1 _))
        (eq_trans (f_equal _ (w_sub_ren _ _ _ _)) (p_of_w_eq_aux_n B p2 _)) ;
  p_of_w_eq_aux_n (A & B) (PAnd1 p)    e := f_equal PAnd1 (p_of_w_eq_aux_n A p e) ;
  p_of_w_eq_aux_n (A & B) (PAnd2 p)    e := f_equal PAnd2 (p_of_w_eq_aux_n B p e) ;
  p_of_w_eq_aux_n (↑ A)   (PShiftN _)  e := eq_refl ;
  p_of_w_eq_aux_n (¬ A)   (PNegN p)    e := f_equal PNegN (p_of_w_eq_aux_p A p e) .

Definition p_dom_of_w_eq_P (Γ : neg_ctx) p : ty0 p -> Prop :=
  match p with
  | pos => fun A => forall (p : pat `+A) (e : p_dom p =[val]> Γ),
      rew [fun p => p_dom p =[ val ]> Γ] p_of_w_eq_aux_p A p e in p_dom_of_w_0p A (w_of_p p `ᵥ⊛ e) ≡ₐ e
  | neg => fun A => forall (p : pat `-A) (e : p_dom p =[val]> Γ),
      rew [fun p => p_dom p =[ val ]> Γ] p_of_w_eq_aux_n A p e in p_dom_of_w_0n A (w_of_p p `ᵥ⊛ e) ≡ₐ e
  end .

Lemma p_dom_of_v_eq {Γ p} A : p_dom_of_w_eq_P Γ p A .
  induction A; intros p e; dependent elimination p; cbn - [ r_cat_l r_cat_r ].
  - intros ? h; repeat (dependent elimination h; auto).
  - intros ? h; repeat (dependent elimination h; auto).
  - pose (H1 := w_sub_ren r_cat_l e `+A3 (w_of_p p)) .
    pose (H2 := w_sub_ren r_cat_r e `+B (w_of_p p0)) .
    pose (x1 := w_of_p p `ᵥ⊛ᵣ r_cat_l `ᵥ⊛ e).
    pose (x2 := w_of_p p0 `ᵥ⊛ᵣ r_cat_r `ᵥ⊛ e).
    change (w_sub_ren r_cat_l e _ _) with H1.
    change (w_sub_ren r_cat_r e _ _) with H2.
    change (_ `ᵥ⊛ᵣ r_cat_l `ᵥ⊛ e) with x1 in H1 |- *.
    change (_ `ᵥ⊛ᵣ r_cat_r `ᵥ⊛ e) with x2 in H2 |- *.
    rewrite H1, H2; clear H1 H2 x1 x2; cbn - [ r_cat_l r_cat_r ].
    pose (H1 := p_of_w_eq_aux_p A3 p (r_cat_l ᵣ⊛ e));
      change (p_of_w_eq_aux_p A3 _ _) with H1 in IHA1 |- *.
    pose (H2 := p_of_w_eq_aux_p B p0 (r_cat_r ᵣ⊛ e));
      change (p_of_w_eq_aux_p B _ _) with H2 in IHA2 |- *.
    transitivity ([ rew [fun p : pat `+A3 => p_dom p =[ val ]> Γ] H1
                     in p_dom_of_w_0p A3 (w_of_p p `ᵥ⊛ r_cat_l ᵣ⊛ e) ,
                    rew [fun p : pat `+B => p_dom p =[ val ]> Γ] H2
                     in p_dom_of_w_0p B (w_of_p p0 `ᵥ⊛ r_cat_r ᵣ⊛ e) ])%asgn.
    now rewrite <- H1, <- H2, eq_refl_map2_distr.
    refine (a_cat_uniq _ _ _ _ _); [ apply IHA1 | apply IHA2 ] .
  - pose (H1 := w_sub_ren r_cat_l e `-A4 (w_of_p p1)) .
    pose (H2 := w_sub_ren r_cat_r e `-B0 (w_of_p p2)) .
    pose (x1 := w_of_p p1 `ᵥ⊛ᵣ r_cat_l `ᵥ⊛ e).
    pose (x2 := w_of_p p2 `ᵥ⊛ᵣ r_cat_r `ᵥ⊛ e).
    change (w_sub_ren r_cat_l e _ _) with H1.
    change (w_sub_ren r_cat_r e _ _) with H2.
    change (_ `ᵥ⊛ᵣ r_cat_l `ᵥ⊛ e) with x1 in H1 |- *.
    change (_ `ᵥ⊛ᵣ r_cat_r `ᵥ⊛ e) with x2 in H2 |- *.
    rewrite H1, H2; clear H1 H2 x1 x2; cbn - [ r_cat_l r_cat_r ].
    pose (H1 := p_of_w_eq_aux_n A4 p1 (r_cat_l ᵣ⊛ e));
      change (p_of_w_eq_aux_n A4 _ _) with H1 in IHA1 |- *.
    pose (H2 := p_of_w_eq_aux_n B0 p2 (r_cat_r ᵣ⊛ e));
      change (p_of_w_eq_aux_n B0 _ _) with H2 in IHA2 |- *.
    transitivity ([ rew [fun p : pat `-A4 => p_dom p =[ val ]> Γ] H1
                     in p_dom_of_w_0n A4 (w_of_p p1 `ᵥ⊛ r_cat_l ᵣ⊛ e) ,
                    rew [fun p : pat `-B0 => p_dom p =[ val ]> Γ] H2
                     in p_dom_of_w_0n B0 (w_of_p p2 `ᵥ⊛ r_cat_r ᵣ⊛ e) ])%asgn.
    now rewrite <- H1, <- H2, eq_refl_map2_distr.
    refine (a_cat_uniq _ _ _ _ _); [ apply IHA1 | apply IHA2 ] .
  - match goal with | |- ?s ≡ₐ e => pose (xx := s); change (_ ≡ₐ e) with (xx ≡ₐ e) end .
    remember xx as xx'; unfold xx in Heqxx'; clear xx.
    rewrite (eq_trans Heqxx' (eq_sym (rew_map _ POr1 _ _))).
    apply IHA1.
  - match goal with | |- ?s ≡ₐ e => pose (xx := s); change (_ ≡ₐ e) with (xx ≡ₐ e) end .
    remember xx as xx'; unfold xx in Heqxx'; clear xx.
    rewrite (eq_trans Heqxx' (eq_sym (rew_map _ POr2 _ _))).
    apply IHA2.
  - match goal with | |- ?s ≡ₐ e => pose (xx := s); change (_ ≡ₐ e) with (xx ≡ₐ e) end .
    remember xx as xx'; unfold xx in Heqxx'; clear xx.
    rewrite (eq_trans Heqxx' (eq_sym (rew_map _ PAnd1 _ _))).
    apply IHA1.
  - match goal with | |- ?s ≡ₐ e => pose (xx := s); change (_ ≡ₐ e) with (xx ≡ₐ e) end .
    remember xx as xx'; unfold xx in Heqxx'; clear xx.
    rewrite (eq_trans Heqxx' (eq_sym (rew_map _ PAnd2 _ _))).
    apply IHA2.
  - intros ? v; repeat (dependent elimination v; auto).
  - intros ? v; repeat (dependent elimination v; auto).
  - match goal with | |- ?s ≡ₐ e => pose (xx := s); change (_ ≡ₐ e) with (xx ≡ₐ e) end .
    remember xx as xx'; unfold xx in Heqxx'; clear xx.
    rewrite (eq_trans Heqxx' (eq_sym (rew_map _ PNegP _ _))).
    apply IHA.
  - match goal with | |- ?s ≡ₐ e => pose (xx := s); change (_ ≡ₐ e) with (xx ≡ₐ e) end .
    remember xx as xx'; unfold xx in Heqxx'; clear xx.
    rewrite (eq_trans Heqxx' (eq_sym (rew_map _ PNegN _ _))).
    apply IHA.
Qed.

(* coq unification drives me crazy!! *)
Definition upg_vp {Γ} {A : ty0 pos} : whn Γ `+A  -> val Γ `+A := fun v => v.
Definition upg_kp {Γ} {A : ty0 pos} : term Γ `-A -> val Γ `-A := fun v => v.
Definition upg_vn {Γ} {A : ty0 neg} : term Γ `+A -> val Γ `+A := fun v => v.
Definition upg_kn {Γ} {A : ty0 neg} : whn Γ `-A  -> val Γ `-A := fun v => v.
Definition dwn_vp {Γ} {A : ty0 pos} : val Γ `+A -> whn Γ `+A  := fun v => v.
Definition dwn_kp {Γ} {A : ty0 pos} : val Γ `-A -> term Γ `-A := fun v => v.
Definition dwn_vn {Γ} {A : ty0 neg} : val Γ `+A -> term Γ `+A := fun v => v.
Definition dwn_kn {Γ} {A : ty0 neg} : val Γ `-A -> whn Γ `-A  := fun v => v.

Lemma nf_eq_split_p {Γ : neg_ctx} {A : ty0 pos} (i : Γ ∋ `-A) p γ
  : nf_eq (i ⋅ v_split_p (dwn_vp (w_of_p p `ᵥ⊛ γ)))
          (i ⋅ (p : o_op obs_op `-A) ⦇ γ ⦈).
  unfold v_split_p, dwn_vp; cbn.
  pose proof (p_dom_of_v_eq A p γ).
  pose (H' := p_of_w_eq_aux_p A p γ); fold H' in H.
  pose (a := p_dom_of_w_0p A (w_of_p p `ᵥ⊛ γ)); fold a in H |- *.
  remember a as a'; clear a Heqa'.
  revert a' H; rewrite H'; intros; now econstructor.
Qed.
Lemma nf_eq_split_n {Γ : neg_ctx} {A : ty0 neg} (i : Γ ∋ `+A) p γ
  : nf_eq (i ⋅ v_split_n (dwn_kn (w_of_p p `ᵥ⊛ γ)))
          (i ⋅ (p : o_op obs_op `+A) ⦇ γ ⦈).
  unfold v_split_n, dwn_kn; cbn.
  pose proof (p_dom_of_v_eq A p γ).
  pose (H' := p_of_w_eq_aux_n A p γ); fold H' in H.
  pose (a := p_dom_of_w_0n A (w_of_p p `ᵥ⊛ γ)); fold a in H |- *.
  remember a as a'; clear a Heqa'.
  revert a' H; rewrite H'; intros; now econstructor.
Qed.
(*|
Finally we can return to saner pursuits.

OGS Instanciation
=================

The notion of values and configurations we will pass to the generic OGS construction
are our mu-mu-tilde values and states, but restricted to negative typing contexts. As
such, while we have proven all the metatheory for arbitrary typing contexts, we still
need a tiny bit of work to provide the laws in this special case. Once again, thanks to
our tricky notion of subset context (`Ctx/Subset.v`), there is no need to cross a
complex isomorphism (between contexts of negative types and contexts of types where
all types are negative). We start by instanciating the substitution structures and
their laws.
|*)
Notation val_n := (val ∘ neg_c_coe).
Notation state_n := (state ∘ neg_c_coe).

#[global] Instance val_n_monoid : subst_monoid val_n .
  esplit.
  - intros Γ x i; exact (var i).
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
(*|
Variable assumptions, that is, lemmata related to decidability of a value being a variable
are easily proven inline.
|*)
#[global] Instance var_laws : var_assumptions val_n.
  esplit.
  - intros ? [[]|[]] ?? H; now dependent destruction H.
  - intros ? [[]|[]] v; dependent elimination v.
    10,13: dependent elimination w.
    all: try exact (Yes _ (Vvar _)).
    all: apply No; intro H; dependent destruction H.
  - intros ?? [[]|[]] ???; cbn in v; dependent induction v.
    all: try now dependent destruction X; exact (Vvar _).
    all: dependent induction w; dependent destruction X; exact (Vvar _).
Qed.
(*|
And we conclude the easy part by instanciating the relevant part of the language
machine.
|*)
#[global] Instance sysd_machine : machine val_n state_n obs_op :=
  {| Machine.eval := @eval ; oapp := @p_app |} .
(*|
It now suffices to prove the remaining assumptions on the language machine: that
evaluation respects substitution and that the 'bad-instanciation' relation has finite
chains. For this we pull in some tooling for coinductive reasoning.
|*)
From Coinduction Require Import coinduction lattice rel tactics.

Ltac refold_eval :=
  change (Structure.iter _ _ ?a) with (eval a);
  change (Structure.subst (fun pat : T1 => let 'T1_0 := pat in ?f) T1_0 ?u)
    with (bind_delay' u f).
(*|
Let's go.
|*)
#[global] Instance machine_law : machine_laws val_n state_n obs_op.
(*|
First we have easy lemmata on observation application.
|*)
  esplit.
  - intros; apply p_app_eq.
  - intros ?? [[]|[]] ????; cbn.
    1,4: change (?a `ₜ⊛ ?b) with (a ᵥ⊛ b); now rewrite (w_sub_sub _ _ _ _).
    all: change (?a `ᵥ⊛ ?b) with (a ᵥ⊛ b) at 1; now rewrite (w_sub_sub _ _ _ _).
(*|
Next we prove the core argument of OGS soundness: evaluating a substitution is like
evaluating the configuration, substituting the result and evaluating again.
While tedious the proof is basically direct, going by induction on the structure of
one-step evaluation.
|*)
  - cbn; intros Γ Δ; unfold comp_eq, it_eq; coinduction R CIH; intros c a.
    cbn; funelim (eval_aux c); try now destruct (s_prf i).
    + cbn; econstructor; refold_eval.
      change (?t `ₜ⊛ ?a) with (upg_kp t ᵥ⊛ a); rewrite s_sub1_sub.
      apply CIH.
    + cbn; econstructor; refold_eval.
      change (?t `ᵥ⊛ ?a) with (upg_vp t ᵥ⊛ a); rewrite s_sub1_sub.
      apply CIH.
    + cbn; econstructor; refold_eval.
      change (RecL (?t `ₜ⊛ a_shift1 ?a)) with (upg_kp (RecL t) ᵥ⊛ a); rewrite t_sub1_sub.
      apply CIH.
    + change (it_eqF _ ?RX ?RY _ _ _) with
        (it_eq_map ∅ₑ RX RY T1_0
           (eval (Cut _ (Whn (v `ᵥ⊛ a)) (a `- A i)))
           (eval (Cut _
              (Whn ((w_of_p (p_of_w_0p A v) `ᵥ⊛ nf_args (s_var_upg i ⋅ v_split_p v)) `ᵥ⊛ a))
              (var (s_var_upg i) `ₜ⊛ a)))).
      unfold nf_args, v_split_p, cut_r, fill_args.
      now rewrite (refold_id_aux A v).
    + cbn; econstructor; refold_eval; apply CIH.
    + cbn; econstructor; refold_eval.
      change (?v `ᵥ⊛ ?a) with (upg_vp v ᵥ⊛ a); rewrite s_sub2_sub.
      apply CIH.
    + cbn; econstructor; refold_eval.
      change (?v `ᵥ⊛ ?a) with (upg_vp v ᵥ⊛ a); rewrite s_sub1_sub.
      apply CIH.
    + cbn; econstructor; refold_eval.
      change (?v `ᵥ⊛ ?a) with (upg_vp v ᵥ⊛ a); rewrite s_sub1_sub.
      apply CIH.
    + cbn; econstructor; refold_eval.
      change (?v `ₜ⊛ ?a) with (upg_vn v ᵥ⊛ a); rewrite s_sub1_sub.
      apply CIH.
    + cbn; econstructor; refold_eval.
      change (?v `ᵥ⊛ ?a) with (upg_kn v ᵥ⊛ a); rewrite s_sub1_sub.
      apply CIH.
    + cbn; econstructor; refold_eval.
      change (?v `ₜ⊛ ?a) with (upg_vn v ᵥ⊛ a); rewrite s_sub1_sub.
      apply CIH.
    + cbn; econstructor; refold_eval.
      change (?v `ᵥ⊛ ?a) with (upg_kn v ᵥ⊛ a); rewrite s_sub1_sub.
      apply CIH.
    + cbn; econstructor; refold_eval.
      change (RecR (?t `ₜ⊛ a_shift1 ?a)) with (upg_vn (RecR t) ᵥ⊛ a); rewrite t_sub1_sub.
      apply CIH.
    + change (it_eqF _ ?RX ?RY _ _ _) with
        (it_eq_map ∅ₑ RX RY T1_0
           (eval (Cut _ (a `+ A i) (Whn (k `ᵥ⊛ a))))
           (eval (Cut _
              (var (s_var_upg i) `ₜ⊛ a)
              (Whn ((w_of_p (p_of_w_0n A k) `ᵥ⊛ nf_args (s_var_upg i ⋅ v_split_n k))
                      `ᵥ⊛ a))))).
      unfold nf_args, v_split_n, cut_r, fill_args.
      now rewrite (refold_id_aux A k).
    + cbn; econstructor; refold_eval; apply CIH.
    + cbn; econstructor; refold_eval.
      change (?v `ᵥ⊛ ?a) with (upg_kn v ᵥ⊛ a); rewrite s_sub2_sub.
      apply CIH.
    + cbn; econstructor; refold_eval.
      change (?v `ᵥ⊛ ?a) with (upg_kn v ᵥ⊛ a); rewrite s_sub1_sub.
      apply CIH.
    + cbn; econstructor; refold_eval.
      change (?v `ᵥ⊛ ?a) with (upg_kn v ᵥ⊛ a); rewrite s_sub1_sub.
      apply CIH.
    + cbn; econstructor; refold_eval.
      change (?v `ₜ⊛ ?a) with (upg_kp v ᵥ⊛ a); rewrite s_sub1_sub.
      apply CIH.
    + cbn; econstructor; refold_eval.
      change (?v `ᵥ⊛ ?a) with (upg_vp v ᵥ⊛ a); rewrite s_sub1_sub.
      apply CIH.
(*|
Next we prove that evaluating a normal form is just returning this normal form. This
goes by approximately induction on observations. 
|*)
  - cbn; intros ? [ A i [ o γ ]]; cbn; unfold p_app, nf_args, cut_r, fill_args.
    cbn in o; funelim (w_of_p o); simpl_depind; inversion eqargs.
    all: match goal with
         | H : _ = ?A† |- _ => destruct A; dependent destruction H
         end.
    1-2: unfold c_var in i; destruct (s_prf i).
    all: dependent destruction eqargs; cbn.
    all: apply it_eq_unstep; cbn -[w_of_p]; econstructor.
    1-2: now econstructor.
    all: match goal with
         | γ : dom ?p =[val_n]> _ |- _ => first [ exact (nf_eq_split_p _ p γ)
                                              | exact (nf_eq_split_n _ p γ) ]
         end.
(*|
Finally we prove the finite chain property. The proof here is quite tedious again, with
numerous cases, but it is still by brutally walking through the structure of one-step
evaluation and finding the needed redex.
|*)
  - intros A; econstructor; intros [ B m ] H; dependent elimination H;
      cbn [projT1 projT2] in i, i0.
    destruct y as [ [] | [] ].
    all: dependent elimination v; try now destruct (t0 (Vvar _)).
    all: clear t0.
    all: dependent elimination o; cbn in i0.
    all: match goal with
         | u : dom _ =[val_n]> _ |- _ =>
             cbn in i0;
             pose (vv := u _ Ctx.top); change (u _ Ctx.top) with vv in i0;
             remember vv as v'; clear u vv Heqv'; cbn in v'
         | _ => idtac
       end.
    7-18,25-36: apply it_eq_step in i0; now inversion i0.
    1-9,19-24: match goal with
       | t : term _ _ |- _ =>
           dependent elimination t;
           [ apply it_eq_step in i0; now inversion i0
           | apply it_eq_step in i0; now inversion i0
           | ]
       | _ => idtac
         end.
    all: 
      match goal with
      | t : evalₒ (Cut _ (Whn ?w) _) ≊ _ |- _ =>
          dependent elimination w;
          [ | apply it_eq_step in i0; now inversion i0 ]
      | t : evalₒ (Cut _ _ (Whn ?w)) ≊ _ |- _ =>
          dependent elimination w;
          [ | apply it_eq_step in i0; now inversion i0 ]
      | _ => idtac
      end.
    all:
      apply it_eq_step in i0; cbn in i0; dependent elimination i0; cbn in r_rel;
      apply noConfusion_inv in r_rel; unfold v_split_n,v_split_p in r_rel;
      cbn in r_rel; unfold NoConfusionHom_f_cut,s_var_upg in r_rel; cbn in r_rel;
      pose proof (H := f_equal pr1 r_rel); cbn in H; dependent destruction H;
      apply DepElim.pr2_uip in r_rel;
      pose proof (H := f_equal pr1 r_rel); cbn in H; dependent destruction H;
      apply DepElim.pr2_uip in r_rel; dependent destruction r_rel.
    all:
      econstructor; intros [ t o ] H; cbn in t,o; dependent elimination H;
      dependent elimination v;
      [ apply it_eq_step in i0; cbn in i0; now inversion i0
      | apply it_eq_step in i0; cbn in i0; now inversion i0 
      | ].
    all:
      match goal with
      | H : is_var (Whn ?w) -> _ |- _ =>
          dependent elimination w;
          try now destruct (H (Vvar _))
      end.
    all: apply it_eq_step in i0; cbn in i0; dependent elimination i0.
Qed.
(*|
Final theorem
=============

We have finished instanciating our generic OGS construction on the System D calculus. For
good measure we give here the concrete instanciation of the soundness theorem, stating
that bisimilarity of the OGS strategies substitution equivalence.
|*)
Definition subst_eq (Δ : neg_ctx) {Γ} : relation (state Γ) :=
  fun u v => forall (σ : Γ =[val]> Δ), evalₒ (u ₜ⊛ σ : state_n Δ) ≈ evalₒ (v ₜ⊛ σ : state_n Δ) .
Notation "x ≈⟦sub Δ ⟧≈ y" := (subst_eq Δ x y) (at level 50).

Theorem subst_correct (Δ : neg_ctx) {Γ : neg_ctx} (x y : state Γ)
  : x ≈⟦ogs Δ ⟧≈ y -> x ≈⟦sub Δ ⟧≈ y.
  exact (ogs_correction _ x y).
Qed.
(*|
Finally it does not cost much to recover the more standard CIU equivalence, which we
derive here for the case of terms (not co-terms).
|*)
Definition c_of_t {Γ : neg_ctx} {A : ty0 pos} (t : term Γ `+A)
           : state_n (Γ ▶ₛ {| sub_elt := `-A ; sub_prf := stt |}) :=
  Cut _ (t_shift1 _ t) (Whn (Var Ctx.top)) .
Notation "'name⁺'" := c_of_t.

Definition a_of_sk {Γ Δ : neg_ctx} {A : ty0 pos} (s : Γ =[val]> Δ) (k : term Δ `-A)
  : (Γ ▶ₛ {| sub_elt := `-A ; sub_prf := stt |}) =[val_n]> Δ :=
  [ s ,ₓ k : val Δ `-A ].

Lemma sub_csk {Γ Δ : neg_ctx} {A : ty0 pos} (t : term Γ `+A) (s : Γ =[val]> Δ)
  (k : term Δ `-A)
  : Cut _ (t `ₜ⊛ s) k = c_of_t t ₜ⊛ a_of_sk s k.
Proof.
  cbn; f_equal; unfold t_shift1; rewrite t_sub_ren; now apply t_sub_eq.
Qed.

Definition ciu_eq (Δ : neg_ctx) {Γ} {A : ty0 pos} : relation (term Γ `+A) :=
  fun u v =>
    forall (σ : Γ =[val]> Δ) (k : term Δ `-A),
      evalₒ (Cut _ (u `ₜ⊛ σ) k : state_n Δ) ≈ evalₒ (Cut _ (v `ₜ⊛ σ) k : state_n Δ) .
Notation "x ≈⟦ciu Δ ⟧⁺≈ y" := (ciu_eq Δ x y) (at level 50).

Theorem ciu_correct (Δ : neg_ctx) {Γ : neg_ctx} {A} (x y : term Γ `+A)
  : (name⁺ x) ≈⟦ogs Δ ⟧≈ (name⁺ y) -> x ≈⟦ciu Δ ⟧⁺≈ y.
  intros H σ k; rewrite 2 sub_csk.
  now apply sysD_subst_correct.
Qed.
