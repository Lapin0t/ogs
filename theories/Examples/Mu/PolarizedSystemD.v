From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel Ctx.
From OGS.ITree Require Import Event ITree Eq Delay Structure Properties.
From OGS.OGS Require Import Soundness.
Set Equations Transparent.
 
Variant pol : Type := pos | neg .
Derive NoConfusion for pol.

Equations pneg : pol -> pol :=
  pneg pos := neg ;
  pneg neg := pos .

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
Derive NoConfusion for ty0.
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
Notation "⊖ A" := (NegP A) (at level 40) : ty_scope .
Notation "¬ A" := (NegN A) (at level 40) : ty_scope .
Notation "A → B" := (¬ A ⅋ B)%ty (at level 40) : ty_scope.


Variant ty : Type :=
| VTy {p} : ty0 p -> ty
| KTy {p} : ty0 p -> ty
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
| Mu {Γ A} : state (Γ ▶ t_neg A) -> term Γ A
| RecL {Γ} {A : ty0 pos} : term (Γ ▶ t- A) (t- A) -> term Γ (t- A)
| RecR {Γ} {A : ty0 neg} : term (Γ ▶ t+ A) (t+ A) -> term Γ (t+ A)
| Whn {Γ A} : whn Γ A -> term Γ A
with whn : t_ctx -> ty -> Type :=
| Var {Γ A} : Γ ∋ A -> whn Γ A
| ZerL {Γ} : whn Γ (t- 0)
| TopR {Γ} : whn Γ (t+ ⊤)
| OneR {Γ} : whn Γ (t+ 1)
| OneL {Γ} : state Γ -> whn Γ (t- 1)
| BotR {Γ} : state Γ -> whn Γ (t+ ⊥)
| BotL {Γ} : whn Γ (t- ⊥)
| TenR {Γ A B} : whn Γ (t+ A) -> whn Γ (t+ B) -> whn Γ (t+ (A ⊗ B))
| TenL {Γ A B} : state (Γ ▶ t+ A ▶ t+ B) -> whn Γ (t- (A ⊗ B))
| ParR {Γ A B} : state (Γ ▶ t- A ▶ t- B) -> whn Γ (t+ (A ⅋ B))
| ParL {Γ A B} : whn Γ (t- A) -> whn Γ (t- B) -> whn Γ (t- (A ⅋ B))
| OrR1 {Γ A B} : whn Γ (t+ A) -> whn Γ (t+ (A ⊕ B))
| OrR2 {Γ A B} : whn Γ (t+ B) -> whn Γ (t+ (A ⊕ B))
| OrL {Γ A B} : state (Γ ▶ t+ A) -> state (Γ ▶ t+ B) -> whn Γ (t- (A ⊕ B))
| AndR {Γ A B} : state (Γ ▶ t- A) -> state (Γ ▶ t- B) -> whn Γ (t+ (A & B))
| AndL1 {Γ A B} : whn Γ (t- A) -> whn Γ (t- (A & B))
| AndL2 {Γ A B} : whn Γ (t- B) -> whn Γ (t- (A & B))
| ShiftPR {Γ A} : term Γ (t+ A) -> whn Γ (t+ (↓ A))
| ShiftPL {Γ A} : state (Γ ▶ t+ A) -> whn Γ (t- (↓ A))
| ShiftNR {Γ A} : state (Γ ▶ t- A) -> whn Γ (t+ (↑ A))
| ShiftNL {Γ A} : term Γ (t- A) -> whn Γ (t- (↑ A))
| NegPR {Γ A} : whn Γ (t- A) -> whn Γ (t+ (⊖ A))
| NegPL {Γ A} : state (Γ ▶ t- A) -> whn Γ (t- (⊖ A))
| NegNR {Γ A} : state (Γ ▶ t+ A) -> whn Γ (t+ (¬ A))
| NegNL {Γ A} : whn Γ (t+ A) -> whn Γ (t- (¬ A))
with state : t_ctx -> Type :=
| Cut {Γ} p {A : ty0 p} : term Γ (t+ A) -> term Γ (t- A) -> state Γ
.

Equations val : t_ctx -> ty -> Type :=
  val Γ (@VTy pos A) := whn Γ (t+ A) ;
  val Γ (@KTy pos A) := term Γ (t- A) ;
  val Γ (@VTy neg A) := term Γ (t+ A) ;
  val Γ (@KTy neg A) := whn Γ (t- A) .

Equations s_var {Γ} : has Γ ⇒ᵢ val Γ :=
  s_var (@VTy pos _) i := Var i ;
  s_var (@KTy pos _) i := Whn (Var i) ;
  s_var (@VTy neg _) i := Whn (Var i) ;
  s_var (@KTy neg _) i := Var i .

Definition r_shift3 {Γ Δ : t_ctx} {a b c} (f : Γ ⊆ Δ) : (Γ ▶ a ▶ b ▶ c) ⊆ (Δ ▶ a ▶ b ▶ c)
  := r_shift (r_shift (r_shift f)).

Equations t_rename {Γ Δ} : Γ ⊆ Δ -> term Γ ⇒ᵢ term Δ :=
  t_rename f _ (Mu c)    := Mu (s_rename (r_shift f) c) ;
  t_rename f _ (RecL t)  := RecL (t_rename (r_shift f) _ t) ;
  t_rename f _ (RecR t)  := RecR (t_rename (r_shift f) _ t) ;
  t_rename f _ (Whn v)   := Whn (w_rename f _ v) ;
with w_rename {Γ Δ} : Γ ⊆ Δ -> whn Γ ⇒ᵢ whn Δ :=
  w_rename f _ (Var i)       := Var (f _ i) ;
  w_rename f _ (ZerL)        := ZerL ;
  w_rename f _ (TopR)        := TopR ;
  w_rename f _ (OneR)        := OneR ;
  w_rename f _ (OneL c)      := OneL (s_rename f c) ;
  w_rename f _ (BotR c)      := BotR (s_rename f c) ;
  w_rename f _ (BotL)        := BotL ;
  w_rename f _ (TenR v1 v2)  := TenR (w_rename f _ v1) (w_rename f _ v2) ;
  w_rename f _ (TenL c)      := TenL (s_rename (r_shift2 f) c) ;
  w_rename f _ (ParR c)      := ParR (s_rename (r_shift2 f) c) ;
  w_rename f _ (ParL k1 k2)  := ParL (w_rename f _ k1) (w_rename f _ k2) ;
  w_rename f _ (OrR1 v)      := OrR1 (w_rename f _ v) ;
  w_rename f _ (OrR2 v)      := OrR2 (w_rename f _ v) ;
  w_rename f _ (OrL c1 c2)   := OrL (s_rename (r_shift f) c1) (s_rename (r_shift f) c2) ;
  w_rename f _ (AndR c1 c2)  := AndR (s_rename (r_shift f) c1) (s_rename (r_shift f) c2) ;
  w_rename f _ (AndL1 k)     := AndL1 (w_rename f _ k) ;
  w_rename f _ (AndL2 k)     := AndL2 (w_rename f _ k) ;
  w_rename f _ (ShiftPR t)   := ShiftPR (t_rename f _ t) ;
  w_rename f _ (ShiftPL c)   := ShiftPL (s_rename (r_shift f) c) ;
  w_rename f _ (ShiftNR c)   := ShiftNR (s_rename (r_shift f) c) ;
  w_rename f _ (ShiftNL t)   := ShiftNL (t_rename f _ t) ;
  w_rename f _ (NegPR k)     := NegPR (w_rename f _ k) ;
  w_rename f _ (NegPL c)     := NegPL (s_rename (r_shift f) c) ;
  w_rename f _ (NegNR c)     := NegNR (s_rename (r_shift f) c) ;
  w_rename f _ (NegNL v)     := NegNL (w_rename f _ v) ;
with s_rename {Γ Δ} : Γ ⊆ Δ -> state Γ -> state Δ :=
   s_rename f (Cut _ v k) := Cut _ (t_rename f _ v) (t_rename f _ k) .

Equations v_rename {Γ Δ} : Γ ⊆ Δ -> val Γ ⇒ᵢ val Δ :=
  v_rename f (@VTy pos a) v := w_rename f _ v ;
  v_rename f (@KTy pos a) t := t_rename f _ t ;
  v_rename f (@VTy neg a) t := t_rename f _ t ;
  v_rename f (@KTy neg a) k := w_rename f _ k .

Definition a_ren {Γ1 Γ2 Γ3} : Γ2 ⊆ Γ3 -> Γ1 =[val]> Γ2 -> Γ1 =[val]> Γ3 :=
  fun f g _ i => v_rename f _ (g _ i) .

Definition t_shift {Γ} [y] : term Γ ⇒ᵢ term (Γ ▶ y)  := @t_rename _ _ r_pop.
Definition w_shift {Γ} [y] : whn Γ ⇒ᵢ whn (Γ ▶ y)  := @w_rename _ _ r_pop.
Definition s_shift {Γ} [y] : state Γ -> state (Γ ▶ y) := @s_rename _ _ r_pop.
Definition v_shift {Γ} [y] : val Γ ⇒ᵢ val (Γ ▶ y)    := @v_rename _ _ r_pop.
Definition v_shift2 {Γ} [y z] : val Γ ⇒ᵢ val (Γ ▶ y ▶ z)  := @v_rename _ _ (r_pop ⊛ᵣ r_pop).
Definition v_shift3 {Γ} [x y z] : val Γ ⇒ᵢ val (Γ ▶ x ▶ y ▶ z)  := @v_rename _ _ (r_pop ⊛ᵣ r_pop ⊛ᵣ r_pop).

Definition a_shift {Γ Δ} [y] (a : Γ =[val]> Δ) : (Γ ▶ y) =[val]> (Δ ▶ y) :=
  a_append (fun _ i => v_shift _ (a _ i)) (s_var _ top).

Definition a_shift2 {Γ Δ} [y z] (a : Γ =[val]> Δ) : (Γ ▶ y ▶ z) =[val]> (Δ ▶ y ▶ z) :=
  a_append (a_append (fun _ i => v_shift2 _ (a _ i)) (s_var _ (pop (top)))) (s_var _ top).

Definition a_shift3 {Γ Δ} [x y z] (a : Γ =[val]> Δ) : (Γ ▶ x ▶ y ▶ z) =[val]> (Δ ▶ x ▶ y ▶ z) :=
  a_append (a_append (a_append (fun _ i => v_shift3 _ (a _ i))
                        (s_var _ (pop (pop top))))
              (s_var _ (pop top)))
    (s_var _ top).

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

Equations t_subst {Γ Δ} : Γ =[val]> Δ -> term Γ ⇒ᵢ term Δ :=
  t_subst f _ (Mu c)    := Mu (s_subst (a_shift f) c) ;
  t_subst f _ (RecL t)  := RecL (t_subst (a_shift f) _ t) ;
  t_subst f _ (RecR t)  := RecR (t_subst (a_shift f) _ t) ;
  t_subst f _ (Whn v)   := t_of_v _ (w_subst f _ v) ;
with w_subst {Γ Δ} : Γ =[val]> Δ -> whn Γ ⇒ᵢ val Δ :=
  w_subst f _ (Var i)      := f _ i ;
  w_subst f _ (ZerL)       := Whn ZerL ;
  w_subst f _ (TopR)       := Whn TopR ;
  w_subst f _ (OneR)       := OneR ;
  w_subst f _ (OneL c)     := Whn (OneL (s_subst f c)) ;
  w_subst f _ (BotR c)     := Whn (BotR (s_subst f c)) ;
  w_subst f _ (BotL)       := BotL ;
  w_subst f _ (TenR v1 v2) := TenR (w_subst f _ v1) (w_subst f _ v2) ;
  w_subst f _ (TenL c)     := Whn (TenL (s_subst (a_shift2 f) c)) ;
  w_subst f _ (ParR c)     := Whn (ParR (s_subst (a_shift2 f) c)) ;
  w_subst f _ (ParL k1 k2) := ParL (w_subst f _ k1) (w_subst f _ k2) ;
  w_subst f _ (OrR1 v)     := OrR1 (w_subst f _ v) ;
  w_subst f _ (OrR2 v)     := OrR2 (w_subst f _ v) ;
  w_subst f _ (OrL c1 c2)  := Whn (OrL (s_subst (a_shift f) c1) (s_subst (a_shift f) c2)) ;
  w_subst f _ (AndR c1 c2) := Whn (AndR (s_subst (a_shift f) c1) (s_subst (a_shift f) c2)) ;
  w_subst f _ (AndL1 k)    := AndL1 (w_subst f _ k) ;
  w_subst f _ (AndL2 k)    := AndL2 (w_subst f _ k) ;
  w_subst f _ (ShiftPR t)  := ShiftPR (t_subst f _ t) ;
  w_subst f _ (ShiftPL c)  := Whn (ShiftPL (s_subst (a_shift f) c)) ;
  w_subst f _ (ShiftNR c)  := Whn (ShiftNR (s_subst (a_shift f) c)) ;
  w_subst f _ (ShiftNL t)  := ShiftNL (t_subst f _ t) ;
  w_subst f _ (NegPR k)    := NegPR (w_subst f _ k) ;
  w_subst f _ (NegPL c)    := Whn (NegPL (s_subst (a_shift f) c)) ;
  w_subst f _ (NegNR c)    := Whn (NegNR (s_subst (a_shift f) c)) ;
  w_subst f _ (NegNL v)    := NegNL (w_subst f _ v) ;
with s_subst {Γ Δ} : Γ =[val]> Δ -> state Γ -> state Δ :=
   s_subst f (Cut p v k) := Cut p (t_subst f _ v) (t_subst f _ k) .

Equations v_subst {Γ Δ} : Γ =[val]> Δ -> val Γ ⇒ᵢ val Δ :=
  v_subst f (@VTy pos a) v := w_subst f _ v ;
  v_subst f (@KTy pos a) t := t_subst f _ t ;
  v_subst f (@VTy neg a) t := t_subst f _ t ;
  v_subst f (@KTy neg a) k := w_subst f _ k .

Definition a_comp {Γ1 Γ2 Γ3} : Γ2 =[val]> Γ3 -> Γ1 =[val]> Γ2 -> Γ1 =[val]> Γ3 :=
  fun f g _ i => v_subst f _ (g _ i) .

Definition ass1 {Γ a} (v : val Γ a) : (Γ ▶ a) =[val]> Γ := a_append s_var v .

Definition t_subst1 {Γ a b} u v := t_subst (@ass1 Γ a v) b u.
Definition w_subst1 {Γ a b} u v := w_subst (@ass1 Γ a v) b u.
Definition v_subst1 {Γ a b} u v := v_subst (@ass1 Γ a v) b u.
Definition s_subst1 {Γ a} u v := s_subst (@ass1 Γ a v) u.

Equations ass2 {Γ a b} (v1 : val Γ a) (v2 : val Γ b) : (Γ ▶ a ▶ b) =[val]> Γ :=
  ass2 v1 v2 _ top           := v2 ;
  ass2 v1 v2 _ (pop top)     := v1 ;
  ass2 v1 v2 _ (pop (pop i)) := s_var _ i .

Equations ass3 {Γ a b c} (v1 : val Γ a) (v2 : val Γ b) (v3 : val Γ c)
  : (Γ ▶ a ▶ b ▶ c) =[val]> Γ :=
  ass3 v1 v2 v3 _ top                 := v3 ;
  ass3 v1 v2 v3 _ (pop top)           := v2 ;
  ass3 v1 v2 v3 _ (pop (pop top))     := v1 ;
  ass3 v1 v2 v3 _ (pop (pop (pop i))) := s_var _ i .

Definition s_subst2 {Γ a b} s v1 v2 := s_subst (@ass2 Γ a b v1 v2) s .
Definition s_subst3 {Γ a b c} s v1 v2 v3 := s_subst (@ass3 Γ a b c v1 v2 v3) s .

Notation "u ₜ/[ v ]" := (t_subst1 u v) (at level 50, left associativity).
Notation "u ᵥ/[ v ]" := (v_subst1 u v) (at level 50, left associativity).
Notation "u ₛ/[ v ]" := (s_subst1 u v) (at level 50, left associativity).
Notation "u ₛ/[ v , w ]" := (s_subst2 u v w) (at level 50, left associativity).
Notation "u /ₛ[ v , w , z ]" := (s_subst3 u v w z) (at level 50, left associativity).

Equations is_neg : ty -> SProp :=
  is_neg (@VTy pos a) := sEmpty ;
  is_neg (@KTy pos a) := sUnit ;
  is_neg (@VTy neg a) := sUnit ;
  is_neg (@KTy neg a) := sEmpty .

Definition neg_ty : Type := sigS is_neg.
Definition neg_coe : neg_ty -> ty := sub_elt.
Global Coercion neg_coe : neg_ty >-> ty.

Definition neg_ctx : Type := ctx_s is_neg.
Definition neg_c_coe : neg_ctx -> ctx ty := sub_elt.
Global Coercion neg_c_coe : neg_ctx >-> ctx.

Bind Scope ctx_scope with neg_ctx.
Bind Scope ctx_scope with ctx.

Inductive pat : ty -> Type :=
| PVarP (A : ty0 neg) : pat (t+ A)
| PVarN (A : ty0 pos) : pat (t- A)
| POne : pat (t+ 1)
| PBot : pat (t- ⊥)
| PTen {A B} : pat (t+ A) -> pat (t+ B) -> pat (t+ (A ⊗ B))
| PPar {A B} : pat (t- A) -> pat (t- B) -> pat (t- (A ⅋ B))
| POr1 {A B} : pat (t+ A) -> pat (t+ (A ⊕ B))
| POr2 {A B} : pat (t+ B) -> pat (t+ (A ⊕ B))
| PAnd1 {A B} : pat (t- A) -> pat (t- (A & B))
| PAnd2 {A B} : pat (t- B) -> pat (t- (A & B))
| PShiftP A : pat (t+ (↓ A))
| PShiftN A : pat (t- (↑ A))
| PNegP {A} : pat (t- A) -> pat (t+ (⊖ A))
| PNegN {A} : pat (t+ A) -> pat (t- (¬ A))
.

Equations p_dom {t} : pat t -> neg_ctx :=
  p_dom (PVarP A)    := ∅ₛ ▶ₛ {| sub_elt := t+ A ; sub_prf := stt |} ;
  p_dom (PVarN A)    := ∅ₛ ▶ₛ {| sub_elt := t- A ; sub_prf := stt |} ;
  p_dom (POne)       := ∅ₛ ;
  p_dom (PBot)       := ∅ₛ ;
  p_dom (PTen p1 p2) := p_dom p1 +▶ₛ p_dom p2 ;
  p_dom (PPar p1 p2) := p_dom p1 +▶ₛ p_dom p2 ;
  p_dom (POr1 p)     := p_dom p ;
  p_dom (POr2 p)     := p_dom p ;
  p_dom (PAnd1 p)    := p_dom p ;
  p_dom (PAnd2 p)    := p_dom p ;
  p_dom (PShiftP A)  := ∅ₛ ▶ₛ {| sub_elt := t+ A ; sub_prf := stt |} ;
  p_dom (PShiftN A)  := ∅ₛ ▶ₛ {| sub_elt := t- A ; sub_prf := stt |} ;
  p_dom (PNegP p)    := p_dom p ;
  p_dom (PNegN p)    := p_dom p .

Definition pat' (Γ : t_ctx) : Type := sigT (fun A => prod (Γ ∋ A) (pat (t_neg A))).
Definition p_dom' Γ : pat' Γ -> neg_ctx := fun p => p_dom (snd (projT2 p)).

Equations w_of_p {a} (p : pat a) : whn (p_dom p) a :=
  w_of_p (PVarP _)    := Var top ;
  w_of_p (PVarN _)    := Var top ;
  w_of_p (POne)       := OneR ;
  w_of_p (PBot)       := BotL ;
  w_of_p (PTen p1 p2) := TenR (w_rename r_concat_l _ (w_of_p p1)) (w_rename r_concat_r _ (w_of_p p2)) ;
  w_of_p (PPar p1 p2) := ParL (w_rename r_concat_l _ (w_of_p p1)) (w_rename r_concat_r _ (w_of_p p2)) ;
  w_of_p (POr1 p)     := OrR1 (w_of_p p) ;
  w_of_p (POr2 p)     := OrR2 (w_of_p p) ;
  w_of_p (PAnd1 p)    := AndL1 (w_of_p p) ;
  w_of_p (PAnd2 p)    := AndL2 (w_of_p p) ;
  w_of_p (PShiftP _)  := ShiftPR (Whn (Var top)) ;
  w_of_p (PShiftN _)  := ShiftNL (Whn (Var top)) ;
  w_of_p (PNegP p)    := NegPR (w_of_p p) ;
  w_of_p (PNegN p)    := NegNL (w_of_p p) .

#[derive(eliminator=no)]
Equations p_of_w_0p {Γ : neg_ctx} (A : ty0 pos) : whn Γ (t+ A) -> pat (t+ A) :=
  p_of_w_0p (0)     (Var i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_of_w_0p (1)     (Var i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_of_w_0p (A ⊗ B) (Var i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_of_w_0p (A ⊕ B) (Var i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_of_w_0p (↓ A)  (Var i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_of_w_0p (⊖ A)   (Var i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_of_w_0p (1)     (OneR)       := POne ;
  p_of_w_0p (A ⊗ B) (TenR v1 v2) := PTen (p_of_w_0p A v1) (p_of_w_0p B v2) ;
  p_of_w_0p (A ⊕ B) (OrR1 v)     := POr1 (p_of_w_0p A v) ;
  p_of_w_0p (A ⊕ B) (OrR2 v)     := POr2 (p_of_w_0p B v) ;
  p_of_w_0p (↓ A)  (ShiftPR _)  := PShiftP A ;
  p_of_w_0p (⊖ A)   (NegPR k)    := PNegP (p_of_w_0n A k) ;
with p_of_w_0n {Γ : neg_ctx} (A : ty0 neg) : whn Γ (t- A) -> pat (t- A) :=
  p_of_w_0n (⊤)     (Var i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_of_w_0n (⊥)     (Var i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_of_w_0n (A ⅋ B) (Var i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_of_w_0n (A & B) (Var i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_of_w_0n (↑ A)  (Var i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_of_w_0n (¬ A)   (Var i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_of_w_0n (⊥)     (BotL)       := PBot ;
  p_of_w_0n (A ⅋ B) (ParL k1 k2) := PPar (p_of_w_0n A k1) (p_of_w_0n B k2) ;
  p_of_w_0n (A & B) (AndL1 k)    := PAnd1 (p_of_w_0n A k) ;
  p_of_w_0n (A & B) (AndL2 k)    := PAnd2 (p_of_w_0n B k) ;
  p_of_w_0n (↑ A)  (ShiftNL _)  := PShiftN A ;
  p_of_w_0n (¬ A)   (NegNL v)    := PNegN (p_of_w_0p A v) .

Equations p_of_v {Γ : neg_ctx} A : val Γ A -> pat A :=
  p_of_v (@VTy pos A) v := p_of_w_0p A v ;
  p_of_v (@KTy pos A) _ := PVarN A ;
  p_of_v (@VTy neg A) _ := PVarP A ;
  p_of_v (@KTy neg A) k := p_of_w_0n A k .

#[derive(eliminator=no)]
Equations p_dom_of_w_0p {Γ : neg_ctx} (A : ty0 pos) (v : whn Γ (t+ A)) : p_dom (p_of_w_0p A v) =[val]> Γ by struct v :=
  p_dom_of_w_0p (0)     (Var i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_dom_of_w_0p (1)     (Var i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_dom_of_w_0p (A ⊗ B) (Var i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_dom_of_w_0p (A ⊕ B) (Var i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_dom_of_w_0p (↓ A)  (Var i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_dom_of_w_0p (⊖ A)   (Var i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_dom_of_w_0p (1)     (OneR)       := a_empty ;
  p_dom_of_w_0p (A ⊗ B) (TenR v1 v2) := [ p_dom_of_w_0p A v1 , p_dom_of_w_0p B v2 ] ;
  p_dom_of_w_0p (A ⊕ B) (OrR1 v)     := p_dom_of_w_0p A v ;
  p_dom_of_w_0p (A ⊕ B) (OrR2 v)     := p_dom_of_w_0p B v ;
  p_dom_of_w_0p (↓ A)  (ShiftPR x)  := a_append a_empty x ;
  p_dom_of_w_0p (⊖ A)   (NegPR k)    := p_dom_of_w_0n A k ;
with p_dom_of_w_0n {Γ : neg_ctx} (A : ty0 neg) (k : whn Γ (t- A)) : p_dom (p_of_w_0n A k) =[val]> Γ by struct k :=
  p_dom_of_w_0n (⊤)     (Var i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_dom_of_w_0n (⊥)     (Var i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_dom_of_w_0n (A ⅋ B) (Var i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_dom_of_w_0n (A & B) (Var i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_dom_of_w_0n (↑ A)  (Var i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_dom_of_w_0n (¬ A)   (Var i) with (s_elt_upg i).(sub_prf) := { | ! } ;
  p_dom_of_w_0n (⊥)     (BotL)       := a_empty ;
  p_dom_of_w_0n (A ⅋ B) (ParL k1 k2) := [ p_dom_of_w_0n A k1 , p_dom_of_w_0n B k2 ] ;
  p_dom_of_w_0n (A & B) (AndL1 k)    := p_dom_of_w_0n A k ;
  p_dom_of_w_0n (A & B) (AndL2 k)    := p_dom_of_w_0n B k ;
  p_dom_of_w_0n (↑ A)  (ShiftNL x)  := a_append a_empty x ;
  p_dom_of_w_0n (¬ A)   (NegNL v)    := p_dom_of_w_0p A v .

Equations p_dom_of_v {Γ : neg_ctx} A (v : val Γ A) : p_dom (p_of_v A v) =[val]> Γ :=
  p_dom_of_v (@VTy pos A) v := p_dom_of_w_0p A v ;
  p_dom_of_v (@KTy pos A) x := a_append a_empty x ;
  p_dom_of_v (@VTy neg A) x := a_append a_empty x ;
  p_dom_of_v (@KTy neg A) k := p_dom_of_w_0n A k .

Definition nf0 (Γ : t_ctx) (A : ty) : Type := sigT (fun p : pat (t_neg A) => p_dom p =[val]> Γ) .
Definition nf (Γ : t_ctx) : Type := sigT (fun A => prod (Γ ∋ A) (nf0 Γ A)) .

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
  - transitivity (rew [fun p : pat (t_neg t) => p_dom p =[ val ]> Γ] p2 in a2); auto.
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

#[derive(eliminator=no)]
Equations eval_aux {Γ : neg_ctx} : state Γ -> (state Γ + nf Γ) :=
  eval_aux (Cut pos (Mu c)  (x))    := inl (c ₛ/[ x ]) ;
  eval_aux (Cut neg (x)     (Mu c)) := inl (c ₛ/[ x ]) ;

  eval_aux (Cut pos (Whn v) (Mu c))  := inl (c ₛ/[ v ]) ;
  eval_aux (Cut neg (Mu c)  (Whn k)) := inl (c ₛ/[ k ]) ;

  eval_aux (Cut pos (Whn v)  (RecL k)) := inl (Cut pos (Whn v) (k ₜ/[ RecL k ])) ;
  eval_aux (Cut neg (RecR t) (Whn k))  := inl (Cut neg (t ₜ/[ RecR t ]) (Whn k)) ;

  eval_aux (Cut pos (Whn v)       (Whn (Var i))) := inr (_ ,' (i , (p_of_w_0p _ v ,' p_dom_of_w_0p _ v))) ;
  eval_aux (Cut neg (Whn (Var i)) (Whn k))       := inr (_ ,' (i , (p_of_w_0n _ k ,' p_dom_of_w_0n _ k))) ;

  eval_aux (Cut pos (Whn (Var i)) (Whn _))       with (s_elt_upg i).(sub_prf) := { | (!) } ;
  eval_aux (Cut neg (Whn _)       (Whn (Var i))) with (s_elt_upg i).(sub_prf) := { | (!) } ;

  eval_aux (Cut pos (Whn (OneR))       (Whn (OneL c)))     := inl c ;
  eval_aux (Cut neg (Whn (BotR c))     (Whn (BotL)))       := inl c ;
  eval_aux (Cut pos (Whn (TenR v1 v2)) (Whn (TenL c)))     := inl (c ₛ/[ v1 , v2 ]) ;
  eval_aux (Cut neg (Whn (ParR c))     (Whn (ParL k1 k2))) := inl (c ₛ/[ k1 , k2 ]) ;
  eval_aux (Cut pos (Whn (OrR1 v))     (Whn (OrL c1 c2)))  := inl (c1 ₛ/[ v ]) ;
  eval_aux (Cut pos (Whn (OrR2 v))     (Whn (OrL c1 c2)))  := inl (c2 ₛ/[ v ]) ;
  eval_aux (Cut neg (Whn (AndR c1 c2)) (Whn (AndL1 k)))    := inl (c1 ₛ/[ k ]) ;
  eval_aux (Cut neg (Whn (AndR c1 c2)) (Whn (AndL2 k)))    := inl (c2 ₛ/[ k ]) ;
  eval_aux (Cut pos (Whn (ShiftPR x))  (Whn (ShiftPL c)))  := inl (c ₛ/[ x ]) ;
  eval_aux (Cut neg (Whn (ShiftNR c))  (Whn (ShiftNL x)))  := inl (c ₛ/[ x ]) ;
  eval_aux (Cut pos (Whn (NegPR k))    (Whn (NegPL c)))    := inl (c ₛ/[ k ]) ;
  eval_aux (Cut neg (Whn (NegNR c))    (Whn (NegNL v)))    := inl (c ₛ/[ v ]) .

Definition eval {Γ : neg_ctx} : state Γ -> delay (nf Γ)
  := iter_delay (fun c => Ret' (eval_aux c)).

Definition refold {Γ : neg_ctx} (n : nf Γ) : prod (Γ ∋ (projT1 n)) (val Γ (t_neg (projT1 n))) :=
  (fst (projT2 n) , w_subst (projT2 (snd (projT2 n))) _ (w_of_p (projT1 (snd (projT2 n))))) .

Definition Cut' {Γ A} : term Γ A -> term Γ (t_neg A) -> state Γ :=
  match A with
  | t+ A => fun t1 t2 => Cut _ t1 t2
  | t- A => fun t1 t2 => Cut _ t2 t1
  end .

Definition p_app {Γ A} (v : val Γ A) (m : pat (t_neg A)) (e : p_dom m =[val]> Γ) : state Γ :=
  Cut' (t_of_v _ v) (t_of_v _ (w_subst e _ (w_of_p m))) .

Scheme term_mut := Induction for term Sort Prop
  with whn_mut := Induction for whn Sort Prop
  with state_mut := Induction for state Sort Prop.

Record syn_ind_args
  (P_t : forall Γ A, term Γ A -> Prop)
  (P_w : forall Γ A, whn Γ A -> Prop)
  (P_s : forall Γ, state Γ -> Prop) :=
  {
    ind_mu : forall Γ A s (H : P_s _ s), P_t Γ A (Mu s) ;
    ind_recp : forall Γ A t (H : P_t _ _ t), P_t Γ (t- A) (RecL t) ;
    ind_recn : forall Γ A t (H : P_t _ _ t), P_t Γ (t+ A) (RecR t) ;
    ind_whn : forall Γ A w (H : P_w _ _ w), P_t Γ A (Whn w) ;
    ind_var : forall Γ A h, P_w Γ A (Var h) ;
    ind_zerl : forall Γ, P_w Γ (t- 0) ZerL ;
    ind_topr : forall Γ, P_w Γ (t+ ⊤) TopR ;
    ind_oner : forall Γ, P_w Γ (t+ 1) OneR ;
    ind_onel : forall Γ s, P_s Γ s -> P_w Γ (t- 1) (OneL s) ;
    ind_botr : forall Γ s, P_s Γ s -> P_w Γ (t+ ⊥) (BotR s) ;
    ind_botl : forall Γ, P_w Γ (t- ⊥) BotL ;
    ind_tenr : forall Γ A B w1 (H1 : P_w _ _ w1) w2 (H2 : P_w _ _ w2), P_w Γ (t+ (A ⊗ B)) (TenR w1 w2) ;
    ind_tenl : forall Γ A B s (H : P_s _ s), P_w Γ (t- (A ⊗ B)) (TenL s) ;
    ind_parr : forall Γ A B s (H : P_s _ s), P_w Γ (t+ (A ⅋ B)) (ParR s) ;
    ind_parl : forall Γ A B w1 (H1 : P_w _ _ w1) w2 (H2 : P_w Γ (t- B) w2), P_w Γ (t- (A ⅋ B)) (ParL w1 w2) ;
    ind_orr1 : forall Γ A B w (H : P_w _ _ w), P_w Γ (t+ (A ⊕ B)) (OrR1 w) ;
    ind_orr2 : forall Γ A B w (H : P_w _ _ w), P_w Γ (t+ (A ⊕ B)) (OrR2 w) ;
    ind_orl : forall Γ A B s1 (H1 : P_s _ s1) s2 (H2 : P_s _ s2), P_w Γ (t- (A ⊕ B)) (OrL s1 s2) ;
    ind_andr : forall Γ A B s1 (H1 : P_s _ s1) s2 (H2 : P_s _ s2), P_w Γ (t+ (A & B)) (AndR s1 s2) ;
    ind_andl1 : forall Γ A B w (H : P_w _ _ w), P_w Γ (t- (A & B)) (AndL1 w) ;
    ind_andl2 : forall Γ A B w (H : P_w _ _ w), P_w Γ (t- (A & B)) (AndL2 w) ;
    ind_shiftpr : forall Γ A t (H : P_t _ _ t), P_w Γ (t+ (↓ A)) (ShiftPR t) ;
    ind_shiftpl : forall Γ A s (H : P_s _ s), P_w Γ (t- (↓ A)) (ShiftPL s) ;
    ind_shiftnr : forall Γ A s (H : P_s _ s), P_w Γ (t+ (↑ A)) (ShiftNR s) ;
    ind_shiftnl : forall Γ A t (H : P_t _ _ t), P_w Γ (t- (↑ A)) (ShiftNL t) ;
    ind_negpr : forall Γ A w (H : P_w _ _ w), P_w Γ (t+ (⊖ A)) (NegPR w) ;
    ind_negpl : forall Γ A s (H : P_s _ s), P_w Γ (t- (⊖ A)) (NegPL s) ;
    ind_negnr : forall Γ A s (H : P_s _ s), P_w Γ (t+ (¬ A)) (NegNR s) ;
    ind_negnl : forall Γ A w (H : P_w _ _ w), P_w Γ (t- (¬ A)) (NegNL w) ;
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
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> t_rename f1 A t = t_rename f2 A t .
Definition w_ren_proper_P Γ A (v : whn Γ A) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> w_rename f1 A v = w_rename f2 A v .
Definition s_ren_proper_P Γ (s : state Γ) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> s_rename f1 s = s_rename f2 s .
Lemma ren_proper_prf : syn_ind_args t_ren_proper_P w_ren_proper_P s_ren_proper_P.
  econstructor.
  all: unfold t_ren_proper_P, w_ren_proper_P, s_ren_proper_P.
  all: intros; cbn; f_equal.
  all: try apply H; try apply H1; try apply H2.
  all: repeat apply r_shift_eq; auto.
Qed.

#[global] Instance t_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@t_rename Γ Δ).
  intros f1 f2 H1 a x y ->; now apply (term_ind_mut _ _ _ ren_proper_prf).
Qed.

#[global] Instance w_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@w_rename Γ Δ).
  intros f1 f2 H1 a x y ->; now apply (whn_ind_mut _ _ _ ren_proper_prf).
Qed.

#[global] Instance s_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> eq ==> eq) (@s_rename Γ Δ).
  intros f1 f2 H1 x y ->; now apply (state_ind_mut _ _ _ ren_proper_prf).
Qed.

#[global] Instance v_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> forall_relation (fun _ => eq ==> eq)) (@v_rename Γ Δ).
  intros f1 f2 H1 [ [] | [] ] v1 v2 H2.
  now apply w_ren_eq.
  now apply t_ren_eq.
  now apply t_ren_eq.
  now apply w_ren_eq.
Qed.

#[global] Instance a_ren_eq {Γ1 Γ2 Γ3}
  : Proper (ass_eq _ _ ==> ass_eq _ _ ==> ass_eq _ _) (@a_ren Γ1 Γ2 Γ3).
  intros r1 r2 H1 a1 a2 H2 ? i; apply (v_ren_eq _ _ H1), H2.
Qed.

#[global] Instance a_shift_eq {Γ Δ A} : Proper (ass_eq _ _ ==> ass_eq _ _) (@a_shift Γ Δ A).
  intros ? ? H ? h.
  dependent elimination h; auto; cbn; now rewrite H.
Qed.

#[global] Instance a_shift2_eq {Γ Δ A B} : Proper (ass_eq _ _ ==> ass_eq _ _) (@a_shift2 Γ Δ A B).
  intros ? ? H ? h.
  do 2 (dependent elimination h; auto).
  cbn; now rewrite H.
Qed.

Definition t_ren_ren_P Γ1 A (t : term Γ1 A) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2),
    t_rename f1 A (t_rename f2 A t) = t_rename (s_ren f1 f2) A t.
Definition w_ren_ren_P Γ1 A (v : whn Γ1 A) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2),
    w_rename f1 A (w_rename f2 A v) = w_rename (s_ren f1 f2) A v.
Definition s_ren_ren_P Γ1 (s : state Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2),
    s_rename f1 (s_rename f2 s) = s_rename (s_ren f1 f2) s.

Lemma ren_ren_prf : syn_ind_args t_ren_ren_P w_ren_ren_P s_ren_ren_P.
  econstructor.
  all: unfold t_ren_ren_P, w_ren_ren_P, s_ren_ren_P.
  all: intros; cbn; f_equal.
  all: unfold r_shift2; now repeat rewrite r_shift_comp.
Qed.

Lemma t_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) A (t : term Γ1 A)
  : t_rename f1 A (t_rename f2 A t) = t_rename (s_ren f1 f2) A t.
  now apply (term_ind_mut _ _ _ ren_ren_prf).
Qed.
Lemma w_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) A (v : whn Γ1 A)
  : w_rename f1 A (w_rename f2 A v) = w_rename (s_ren f1 f2) A v.
  now apply (whn_ind_mut _ _ _ ren_ren_prf).
Qed.
Lemma s_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) (s : state Γ1)
  : s_rename f1 (s_rename f2 s) = s_rename (s_ren f1 f2) s.
  now apply (state_ind_mut _ _ _ ren_ren_prf).
Qed.
Lemma v_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) A (v : val Γ1 A)
  : v_rename f1 A (v_rename f2 A v) = v_rename (s_ren f1 f2) A v.
  destruct A as [ [] | [] ].
  now apply w_ren_ren.
  now apply t_ren_ren.
  now apply t_ren_ren.
  now apply w_ren_ren.
Qed.

Definition t_ren_id_l_P Γ A (t : term Γ A) : Prop := t_rename r_id A t = t.
Definition w_ren_id_l_P Γ A (v : whn Γ A) : Prop := w_rename r_id A v = v.
Definition s_ren_id_l_P Γ (s : state Γ) : Prop := s_rename r_id s = s.

Lemma ren_id_l_prf : syn_ind_args t_ren_id_l_P w_ren_id_l_P s_ren_id_l_P.
  econstructor.
  all: unfold t_ren_id_l_P, w_ren_id_l_P, s_ren_id_l_P.
  all: intros; cbn; f_equal.
  all: unfold r_shift2; now repeat rewrite r_shift_id.
Qed.

Lemma t_ren_id_l {Γ} A (t : term Γ A) : t_rename r_id A t = t.
  now apply (term_ind_mut _ _ _ ren_id_l_prf).
Qed.
Lemma w_ren_id_l {Γ} A (v : whn Γ A) : w_rename r_id A v = v.
  now apply (whn_ind_mut _ _ _ ren_id_l_prf).
Qed.
Lemma s_ren_id_l {Γ} (s : state Γ) : s_rename r_id s = s.
  now apply (state_ind_mut _ _ _ ren_id_l_prf).
Qed.
Lemma v_ren_id_l {Γ} A (v : val Γ A) : v_rename r_id A v = v.
  destruct A as [ [] | [] ].
  now apply w_ren_id_l.
  now apply t_ren_id_l.
  now apply t_ren_id_l.
  now apply w_ren_id_l.
Qed.

Lemma v_ren_id_r {Γ Δ} (f : Γ ⊆ Δ) A (i : Γ ∋ A) : v_rename f A (s_var A i) = s_var A (f A i).
  destruct A as [ [] | [] ]; auto.
Qed.

Lemma a_shift_id {Γ A} : @a_shift Γ Γ A s_var ≡ₐ s_var.
  intros [ [] | [] ] i; dependent elimination i; auto.
Qed.

Lemma a_shift2_id {Γ A B} : @a_shift2 Γ Γ A B s_var ≡ₐ s_var.
  unfold a_shift2, v_shift2; intros ? h.
  do 2 (dependent elimination h; cbn; auto).
  now rewrite v_ren_id_r.
Qed.

Lemma a_shift_a_ren {Γ1 Γ2 Γ3 y} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[ val ]> Γ2)
      : a_shift (y:=y) (a_ren f1 f2) ≡ₐ a_ren (r_shift f1) (a_shift f2) .
  unfold r_shift, a_shift, a_ren, v_shift; intros ? h.
  dependent elimination h; cbn.
  - now rewrite v_ren_id_r.
  - now rewrite 2 v_ren_ren, a_append_pop.
Qed.

Lemma a_shift_s_ren {Γ1 Γ2 Γ3 y} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 ⊆ Γ2)
  : a_shift (y:=y) (s_ren f1 f2) ≡ₐ s_ren (a_shift f1) (r_shift f2) .
  intros ? i; dependent elimination i; auto.
Qed.

Lemma a_shift2_s_ren {Γ1 Γ2 Γ3 A B} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 ⊆ Γ2)
  : @a_shift2 _ _ A B (s_ren f1 f2) ≡ₐ s_ren (a_shift2 f1) (r_shift2 f2) .
  intros ? h; do 2 (dependent elimination h; auto).
Qed.

Lemma a_shift2_a_ren {Γ1 Γ2 Γ3 A B} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[ val ]> Γ2)
      : @a_shift2 _ _ A B (a_ren f1 f2) ≡ₐ a_ren (r_shift2 f1) (a_shift2 f2) .
  unfold r_shift2, r_shift, a_shift2, v_shift2, a_ren; intros ? h.
  do 2 (dependent elimination h; cbn; [ now rewrite v_ren_id_r | ]).
  rewrite 2 v_ren_ren; now apply v_ren_eq.
Qed.

Definition t_sub_proper_P Γ A (t : term Γ A) : Prop :=
  forall Δ (f1 f2 : Γ =[val]> Δ), f1 ≡ₐ f2 -> t_subst f1 A t = t_subst f2 A t .
Definition w_sub_proper_P Γ A (v : whn Γ A) : Prop :=
  forall Δ (f1 f2 : Γ =[val]> Δ), f1 ≡ₐ f2 -> w_subst f1 A v = w_subst f2 A v .
Definition s_sub_proper_P Γ (s : state Γ) : Prop :=
  forall Δ (f1 f2 : Γ =[val]> Δ), f1 ≡ₐ f2 -> s_subst f1 s = s_subst f2 s .

Lemma sub_proper_prf : syn_ind_args t_sub_proper_P w_sub_proper_P s_sub_proper_P.
  econstructor.
  all: unfold t_sub_proper_P, w_sub_proper_P, s_sub_proper_P.
  all: intros; cbn.
  all: match goal with
       | |- Whn _ = Whn _ => do 2 f_equal
       | _ => f_equal
       end .
  all: try apply H; try apply H1; try apply H2; auto.
  all: match goal with
       | |- a_shift _ ≡ₐ a_shift _ => now apply a_shift_eq
       | |- a_shift2 _ ≡ₐ a_shift2 _ => now apply a_shift2_eq
       end .
Qed.

#[global] Instance t_sub_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> forall_relation (fun _ => eq ==> eq)) (@t_subst Γ Δ).
  intros f1 f2 H1 a x y ->; now apply (term_ind_mut _ _ _ sub_proper_prf).
Qed.

#[global] Instance w_sub_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> forall_relation (fun _ => eq ==> eq)) (@w_subst Γ Δ).
  intros f1 f2 H1 a x y ->; now apply (whn_ind_mut _ _ _ sub_proper_prf).
Qed.

#[global] Instance s_sub_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> eq ==> eq) (@s_subst Γ Δ).
  intros f1 f2 H1 x y ->; now apply (state_ind_mut _ _ _ sub_proper_prf).
Qed.

#[global] Instance v_sub_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> forall_relation (fun _ => eq ==> eq)) (@v_subst Γ Δ).
  intros f1 f2 H1 [ [] | [] ] v1 v2 H2.
  - now apply w_sub_eq.
  - now apply t_sub_eq.
  - now apply t_sub_eq.
  - now apply w_sub_eq.
Qed.

#[global] Instance a_comp_eq {Γ1 Γ2 Γ3} : Proper (ass_eq _ _ ==> ass_eq _ _ ==> ass_eq _ _) (@a_comp Γ1 Γ2 Γ3).
  intros ? ? H1 ? ? H2 ? ?; apply v_sub_eq; [ apply H1 | apply H2 ].
Qed.

Definition t_ren_sub_P Γ1 A (t : term Γ1 A) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val]> Γ2),
    t_rename f1 A (t_subst f2 A t)
    = t_subst (a_ren f1 f2) A t .
Definition w_ren_sub_P Γ1 A (v : whn Γ1 A) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val]> Γ2),
    v_rename f1 A (w_subst f2 A v)
    = w_subst (a_ren f1 f2) A v .
Definition s_ren_sub_P Γ1 (s : state Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val]> Γ2),
    s_rename f1 (s_subst f2 s)
    = s_subst (a_ren f1 f2) s .
Lemma ren_sub_prf : syn_ind_args t_ren_sub_P w_ren_sub_P s_ren_sub_P.
  econstructor.
  all: unfold t_ren_sub_P, w_ren_sub_P, s_ren_sub_P.
  all: intros; cbn.
  4: destruct A as [ [] | [] ]; cbn.
  all: match goal with
       | |- Whn _ = Whn _ => do 2 f_equal
       | _ => f_equal
       end .
  all: try rewrite a_shift_a_ren; try rewrite a_shift2_a_ren; auto.
  all: try change (w_rename ?f ?a ?b) with (v_rename f a b).
  all: try apply H; try apply H1; try apply H2; auto.
Qed.

Lemma t_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val]> Γ2) A (t : term Γ1 A)
  : t_rename f1 A (t_subst f2 A t) = t_subst (a_ren f1 f2) A t.
  now apply (term_ind_mut _ _ _ ren_sub_prf).
Qed.
Lemma w_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val]> Γ2) A (v : whn Γ1 A)
  : v_rename f1 A (w_subst f2 A v) = w_subst (a_ren f1 f2) A v.
  now apply (whn_ind_mut _ _ _ ren_sub_prf).
Qed.
Lemma s_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val]> Γ2) (s : state Γ1)
  : s_rename f1 (s_subst f2 s) = s_subst (a_ren f1 f2) s.
  now apply (state_ind_mut _ _ _ ren_sub_prf).
Qed.
Lemma v_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[val]> Γ2) A (v : val Γ1 A)
  : v_rename f1 A (v_subst f2 A v) = v_subst (a_ren f1 f2) A v.
  destruct A as [ [] | [] ]; cbn [ v_subst ].
  - now apply w_ren_sub.
  - now apply t_ren_sub.
  - now apply t_ren_sub.
  - now apply w_ren_sub.
Qed.

Definition t_sub_ren_P Γ1 A (t : term Γ1 A) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 ⊆ Γ2),
    t_subst f1 A (t_rename f2 A t)
    = t_subst (s_ren f1 f2) A t .
Definition w_sub_ren_P Γ1 A (v : whn Γ1 A) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 ⊆ Γ2),
    w_subst f1 A (w_rename f2 A v)
    = w_subst (s_ren f1 f2) A v .
Definition s_sub_ren_P Γ1 (s : state Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 ⊆ Γ2),
    s_subst f1 (s_rename f2 s)
    = s_subst (s_ren f1 f2) s .

Lemma sub_ren_prf : syn_ind_args t_sub_ren_P w_sub_ren_P s_sub_ren_P.
  econstructor.
  all: unfold t_sub_ren_P, w_sub_ren_P, s_sub_ren_P.
  all: intros; cbn.
  all: match goal with
       | |- Whn _ = Whn _ => do 2 f_equal
       | _ => f_equal
       end .
  all: try rewrite a_shift_s_ren; try rewrite a_shift2_s_ren; auto.
Qed.

Lemma t_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 ⊆ Γ2) A (t : term Γ1 A)
  : t_subst f1 A (t_rename f2 A t) = t_subst (s_ren f1 f2) A t.
  now apply (term_ind_mut _ _ _ sub_ren_prf).
Qed.
Lemma w_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 ⊆ Γ2) A (v : whn Γ1 A)
  : w_subst f1 A (w_rename f2 A v) = w_subst (s_ren f1 f2) A v.
  now apply (whn_ind_mut _ _ _ sub_ren_prf).
Qed.
Lemma s_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 ⊆ Γ2) (s : state Γ1)
  : s_subst f1 (s_rename f2 s) = s_subst (s_ren f1 f2) s.
  now apply (state_ind_mut _ _ _ sub_ren_prf).
Qed.
Lemma v_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 ⊆ Γ2) A (v : val Γ1 A)
  : v_subst f1 A (v_rename f2 A v) = v_subst (s_ren f1 f2) A v.
  destruct A as [ [] | [] ].
  - now apply w_sub_ren.
  - now apply t_sub_ren.
  - now apply t_sub_ren.
  - now apply w_sub_ren.
Qed.

Lemma v_sub_id_r {Γ Δ} (f : Γ =[val]> Δ) A (i : Γ ∋ A) : v_subst f A (s_var A i) = f A i.
  destruct A as [ [] | [] ]; auto.
Qed.

Lemma a_shift_comp {Γ1 Γ2 Γ3 A} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2)
  : @a_shift _ _ A (a_comp f1 f2) ≡ₐ a_comp (a_shift f1) (a_shift f2) .
  intros x i; dependent elimination i; unfold a_shift, a_comp, v_shift; cbn.
  - now rewrite v_sub_id_r.
  - rewrite v_ren_sub, v_sub_ren; now apply v_sub_eq.
Qed.

Lemma a_shift2_comp {Γ1 Γ2 Γ3 A B} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2)
  : @a_shift2 _ _ A B (a_comp f1 f2) ≡ₐ a_comp (a_shift2 f1) (a_shift2 f2) .
  unfold a_shift2, v_shift2, a_comp; intros ? h.
  do 2 (dependent elimination h; cbn; [ now rewrite v_sub_id_r | ]).
  rewrite v_ren_sub, v_sub_ren; now apply v_sub_eq.
Qed.

Definition t_sub_sub_P Γ1 A (t : term Γ1 A) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2),
    t_subst f1 A (t_subst f2 A t) = t_subst (a_comp f1 f2) A t.
Definition w_sub_sub_P Γ1 A (v : whn Γ1 A) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2),
    v_subst f1 A (w_subst f2 A v) = w_subst (a_comp f1 f2) A v.
Definition s_sub_sub_P Γ1 (s : state Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2),
    s_subst f1 (s_subst f2 s) = s_subst (a_comp f1 f2) s.

Lemma sub_sub_prf : syn_ind_args t_sub_sub_P w_sub_sub_P s_sub_sub_P.
  econstructor.
  all: unfold t_sub_sub_P, w_sub_sub_P, s_sub_sub_P; intros; cbn.
  4: destruct A as [ [] | [] ]; cbn.
  all: match goal with
       | |- Whn _ = Whn _ => do 2 f_equal
       | _ => f_equal
       end .
  all: try rewrite a_shift_comp; try rewrite a_shift2_comp; auto.
  all: try change (w_subst ?f ?a ?b) with (v_subst f a b).
  all: try change (t_subst ?f ?a ?b) with (v_subst f a b).
  all: try apply H; try apply H1; try apply H2; auto.
Qed.

Lemma t_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2) A (t : term Γ1 A)
  : t_subst f1 A (t_subst f2 A t) = t_subst (a_comp f1 f2) A t.
  now apply (term_ind_mut _ _ _ sub_sub_prf).
Qed.
Lemma w_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2) A (v : whn Γ1 A)
  : v_subst f1 A (w_subst f2 A v) = w_subst (a_comp f1 f2) A v.
  now apply (whn_ind_mut _ _ _ sub_sub_prf).
Qed.
Lemma s_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2) (s : state Γ1)
  : s_subst f1 (s_subst f2 s) = s_subst (a_comp f1 f2) s.
  now apply (state_ind_mut _ _ _ sub_sub_prf).
Qed.
Lemma v_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ2 =[val]> Γ3) (f2 : Γ1 =[val]> Γ2) A (v : val Γ1 A)
  : v_subst f1 A (v_subst f2 A v) = v_subst (a_comp f1 f2) A v.
  destruct A as [ [] | [] ].
  - now apply w_sub_sub.
  - now apply t_sub_sub.
  - now apply t_sub_sub.
  - now apply w_sub_sub.
Qed.

Lemma a_comp_assoc {Γ1 Γ2 Γ3 Γ4} (u : Γ3 =[val]> Γ4) (v : Γ2 =[val]> Γ3) (w : Γ1 =[val]> Γ2)
           : a_comp u (a_comp v w) ≡ₐ a_comp (a_comp u v) w .
  intros ? i; unfold a_comp; now apply v_sub_sub.
Qed.

Definition t_sub_id_l_P Γ A (t : term Γ A) : Prop := t_subst s_var A t = t.
Definition w_sub_id_l_P Γ A (v : whn Γ A) : Prop := w_subst s_var A v = v_of_w A v.
Definition s_sub_id_l_P Γ (s : state Γ) : Prop := s_subst s_var s = s.

Lemma sub_id_l_prf : syn_ind_args t_sub_id_l_P w_sub_id_l_P s_sub_id_l_P.
  econstructor.
  all: unfold t_sub_id_l_P, w_sub_id_l_P, s_sub_id_l_P; intros; cbn.
  4,5: destruct A as [ [] | [] ]; cbn.
  all: match goal with
       | |- Whn _ = Whn _ => do 2 f_equal
       | _ => f_equal
       end; auto.
  all: try rewrite a_shift_id; try rewrite a_shift2_id; auto.
Qed.

Lemma t_sub_id_l {Γ} A (t : term Γ A) : t_subst s_var A t = t.
  now apply (term_ind_mut _ _ _ sub_id_l_prf).
Qed.
Lemma w_sub_id_l {Γ} A (v : whn Γ A) : w_subst s_var A v = v_of_w A v.
  now apply (whn_ind_mut _ _ _ sub_id_l_prf).
Qed.
Lemma s_sub_id_l {Γ} (s : state Γ) : s_subst s_var s = s.
  now apply (state_ind_mut _ _ _ sub_id_l_prf).
Qed.
Lemma v_sub_id_l {Γ} A (v : val Γ A) : v_subst s_var A v = v.
  destruct A as [ [] | [] ].
  - now apply w_sub_id_l.
  - now apply t_sub_id_l.
  - now apply t_sub_id_l.
  - now apply w_sub_id_l.
Qed.

Lemma sub1_sub {Γ Δ A} (f : Γ =[val]> Δ) (v : val Γ A) :
  a_comp (ass1 (v_subst f A v)) (a_shift f) ≡ₐ a_comp f (ass1 v).
  intros ? h; dependent elimination h.
  - unfold a_comp; cbn; now rewrite v_sub_id_r.
  - unfold a_comp, a_shift, v_shift; cbn.
    rewrite v_sub_ren, v_sub_id_r.
    apply v_sub_id_l.
Qed.

Lemma sub1_ren {Γ Δ A} (f : Γ ⊆ Δ) (v : val Γ A) :
  ass1 (v_rename f A v) ⊛ᵣ r_shift f ≡ₐ a_ren f (ass1 v) .
  intros ? h; dependent elimination h; auto.
  unfold a_ren, ass1; cbn; now rewrite v_ren_id_r.
Qed.

Lemma v_sub1_sub {Γ Δ A B} (f : Γ =[val]> Δ) (v : val Γ A) (w : val (Γ ▶ A) B)
  : v_subst (a_shift f) B w ᵥ/[ v_subst f A v ] = v_subst f B (w ᵥ/[ v ]) .
  unfold v_subst1; rewrite 2 v_sub_sub.
  apply v_sub_eq; auto.
  now rewrite sub1_sub.
Qed.

Lemma v_sub1_ren {Γ Δ A B} (f : Γ ⊆ Δ) (v : val Γ A) (w : val (Γ ▶ A) B)
  : v_rename (r_shift f) B w ᵥ/[ v_rename f A v ] = v_rename f B (w ᵥ/[ v ]) .
  unfold v_subst1; rewrite v_sub_ren, v_ren_sub.
  apply v_sub_eq; auto.
  now rewrite sub1_ren.
Qed.

Lemma s_sub1_sub {Γ Δ A} (f : Γ =[val]> Δ) (v : val Γ A) (s : state (Γ ▶ A))
  : s_subst (a_shift f) s ₛ/[ v_subst f A v ] = s_subst f (s ₛ/[ v ]) .
  unfold s_subst1; now rewrite 2 s_sub_sub, sub1_sub.
Qed.

Lemma s_sub2_sub {Γ Δ A B} (f : Γ =[val]> Δ) (s : state (Γ ▶ A ▶ B)) u v
  : s_subst (a_shift2 f) s ₛ/[ v_subst f A u , v_subst f B v ] = s_subst f (s ₛ/[ u , v ]) .
  unfold s_subst2; rewrite 2 s_sub_sub; apply s_sub_eq; auto.
  intros ? h; unfold a_comp, a_shift2, v_shift2.
  do 2 (dependent elimination h; cbn; [ now rewrite v_sub_id_r | ]).
  rewrite v_sub_ren, v_sub_id_r, <- v_sub_id_l.
  now apply v_sub_eq.
Qed.

Lemma s_sub1_ren {Γ Δ A} (f : Γ ⊆ Δ) (v : val Γ A) (s : state (Γ ▶ A))
  : s_rename (r_shift f) s ₛ/[ v_rename f A v ] = s_rename f (s ₛ/[ v ]) .
  unfold s_subst1; now rewrite s_sub_ren, s_ren_sub, sub1_ren.
Qed.

Lemma t_sub1_sub {Γ Δ A B} (f : Γ =[val]> Δ) (v : val Γ A) (t : term (Γ ▶ A) B)
  : t_subst (a_shift f) B t ₜ/[ v_subst f A v ] = t_subst f B (t ₜ/[ v ]) .
  unfold t_subst1; rewrite 2 t_sub_sub.
  apply t_sub_eq; auto.
  rewrite sub1_sub; reflexivity.
Qed.

Lemma t_sub1_ren {Γ Δ A B} (f : Γ ⊆ Δ) (v : val Γ A) (t : term (Γ ▶ A) B)
  : t_rename (r_shift f) B t ₜ/[ v_rename f A v ] = t_rename f B (t ₜ/[ v ]) .
  unfold t_subst1; rewrite t_sub_ren, t_ren_sub.
  apply t_sub_eq; auto.
  now rewrite sub1_ren.
Qed.

#[global] Instance p_app_eq {Γ A} (v : val Γ A) (m : pat (t_neg A)) : Proper (ass_eq _ _ ==> eq) (p_app v m) .
  intros u1 u2 H; destruct A as [ [] | []]; cbn; now erewrite (w_sub_eq u1 u2 H).
Qed.

Definition refold_id_aux_P (Γ : neg_ctx) p : ty0 p -> Prop :=
  match p with
  | pos => fun A => forall (v : whn Γ (t+ A)), w_subst (p_dom_of_w_0p A v) (t+ A) (w_of_p (p_of_w_0p A v)) = v
  | neg => fun A => forall (v : whn Γ (t- A)), w_subst (p_dom_of_w_0n A v) (t- A) (w_of_p (p_of_w_0n A v)) = v
  end .

Lemma refold_id_aux {Γ p} A : refold_id_aux_P Γ p A .
  induction A; intros v.
  - dependent elimination v.
    pose (nope := (s_elt_upg h).(sub_prf)); dependent elimination nope.
  - dependent elimination v.
    pose (nope := (s_elt_upg h).(sub_prf)); dependent elimination nope.
  - dependent elimination v.
    pose (nope := (s_elt_upg h).(sub_prf)); dependent elimination nope.
    reflexivity.
  - dependent elimination v.
    pose (nope := (s_elt_upg h).(sub_prf)); dependent elimination nope.
    reflexivity.
  - dependent elimination v.
    pose (nope := (s_elt_upg h).(sub_prf)); dependent elimination nope.
    change (w_subst _ _ _) with
      (w_subst ([ p_dom_of_w_0p A0 w , p_dom_of_w_0p B w0 ]) _
         (TenR (w_rename r_concat_l _ (w_of_p (p_of_w_0p A0 w)))
               (w_rename r_concat_r _ (w_of_p (p_of_w_0p B w0))))); cbn.
    rewrite 2 w_sub_ren.
    erewrite (w_sub_eq _ _ (s_eq_cat_l _ _)); auto.
    erewrite (w_sub_eq _ _ (s_eq_cat_r _ _)); auto.
    f_equal; [ apply IHA1 | apply IHA2 ].
  - dependent elimination v.
    pose (nope := (s_elt_upg h).(sub_prf)); dependent elimination nope.
    change (w_subst _ _ _) with
      (w_subst ([ p_dom_of_w_0n A5 w1 , p_dom_of_w_0n B2 w2 ]) _
         (ParL (w_rename r_concat_l _ (w_of_p (p_of_w_0n A5 w1)))
               (w_rename r_concat_r _ (w_of_p (p_of_w_0n B2 w2))))); cbn.
    rewrite 2 w_sub_ren.
    erewrite (w_sub_eq _ _ (s_eq_cat_l _ _)); auto.
    erewrite (w_sub_eq _ _ (s_eq_cat_r _ _)); auto.
    f_equal; [ apply IHA1 | apply IHA2 ].
  - dependent elimination v.
    pose (nope := (s_elt_upg h).(sub_prf)); dependent elimination nope.
    exact (f_equal OrR1 (IHA1 w3)).
    exact (f_equal OrR2 (IHA2 w4)).
  - dependent elimination v.
    pose (nope := (s_elt_upg h).(sub_prf)); dependent elimination nope.
    exact (f_equal AndL1 (IHA1 w5)).
    exact (f_equal AndL2 (IHA2 w6)).
  - dependent elimination v.
    pose (nope := (s_elt_upg h).(sub_prf)); dependent elimination nope.
    reflexivity.
  - dependent elimination v.
    pose (nope := (s_elt_upg h).(sub_prf)); dependent elimination nope.
    reflexivity.
  - dependent elimination v.
    pose (nope := (s_elt_upg h).(sub_prf)); dependent elimination nope.
    exact (f_equal NegPR (IHA w7)).
  - dependent elimination v.
    pose (nope := (s_elt_upg h).(sub_prf)); dependent elimination nope.
    exact (f_equal NegNL (IHA w8)).
Qed.

Lemma refold_id {Γ : neg_ctx} A (v : val Γ A)
  : w_subst (p_dom_of_v A v) A (w_of_p (p_of_v A v)) = v.
  destruct A as [ [] A | [] A ].
  - apply (refold_id_aux A v).
  - reflexivity.
  - reflexivity.
  - apply (refold_id_aux A v).
Qed.

Lemma var_inj {Γ A} (i j : Γ ∋ A) (H : s_var A i = s_var A j) : i = j .
  destruct A as [ [] | [] ] ; now dependent induction H.
Qed.

From Coinduction Require Import coinduction lattice rel tactics.
From OGS.Utils Require Import Psh Rel.
From OGS.ITree Require Import ITree Eq Structure.

(* the final version we would like to have in the hypothesis, in terms of [p_app] *)
Definition then_eval1 {Γ Δ : neg_ctx} (e : Γ =[val]> Δ) (n : nf Γ) : delay (nf Δ)
  := eval (p_app (e _ (fst (projT2 n))) (projT1 (snd (projT2 n))) (a_comp e (projT2 (snd (projT2 n))))) .

(* the clean version with simplified substitutions we would like to have in the proof *)
Definition then_eval2 {Γ Δ : neg_ctx} (e : Γ =[val]> Δ) (n : nf Γ) : delay (nf Δ) :=
  let '(i , v) := refold n in
  eval (Cut' (t_of_v _ (e _ i)) (t_of_v _ (v_subst e _ v))).

(* both are the same thing up to substitution shenenigans *)
Lemma then_eval_eq {Γ Δ : neg_ctx} (e : Γ =[val]> Δ) (n : nf Γ) : then_eval1 e n ≊ then_eval2 e n.
  unfold then_eval1, then_eval2, p_app, refold.
  now rewrite <- w_sub_sub.
Qed.

(* we can prove the hypothesis:

    eval (c / e) == eval c >>= λ n => eval (⌊ n ⌋ / e)
*)

Lemma fmap_comp_eq {Γ} {u v : delay (nf Γ)} : u ≋ v -> fmap_delay (pat_of_nf Γ) u ≊ fmap_delay (pat_of_nf Γ) v .
  intro H.
  unfold it_eq; revert u v H; coinduction L CIH; intros u v H.
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

Lemma clean_hyp {Γ Δ : neg_ctx} (c : state Γ) (e : Γ =[val]> Δ)
   : eval (s_subst e c) ≊ bind_delay' (eval c) (then_eval1 e) .
  transitivity (bind_delay' (eval c) (then_eval2 e)); cycle 1.
  apply (proj1 (t_gfp (it_eq_map ∅ₑ (eqᵢ _)) _ _ _)).
  eapply (it_eq_up2bind_t (eqᵢ _)); econstructor; auto.
  intros [] ? ? <-; symmetry; exact (then_eval_eq e x1).
  unfold iter_delay, it_eq, bind.
  revert Γ c e; coinduction L CIH; intros Γ c e.
  dependent elimination c.
  destruct p.
  - dependent elimination t0.
    + cbn; econstructor.
      change (t_subst e (t- A) t1) with (v_subst e (t- A) t1).
      rewrite s_sub1_sub; apply CIH.
    + dependent elimination t1.
      * cbn; econstructor.
        change (w_subst e (t+ A) w) with (v_subst e (t+ A) w).
        rewrite s_sub1_sub; apply CIH.
      * cbn; econstructor.
        change (RecL (t_subst (a_shift e) (t- ?A) t0)) with (t_subst e (t- A) (RecL t0)).
        change (t_subst ?f (t- ?A) ?w) with (v_subst f (t- A) w) at 2.
        rewrite t_sub1_sub; apply CIH.
      * dependent elimination w.
        -- pose (nope := (s_elt_upg h).(sub_prf)); dependent elimination nope.
        -- dependent elimination w0.
           ++ unfold eval at 2; cbn -[eval then_eval2].
              unfold then_eval2; simp eval_aux; cbn -[eval].
              rewrite (refold_id_aux 1).
              now change (it_eqF _ ?RX ?RY _ (observe ?a) (_observe ?b)) with (it_eq_map ∅ₑ RX RY T1_0 a b).
           ++ cbn; econstructor; apply CIH.
        -- dependent elimination w0.
           ++ unfold eval at 2; cbn -[eval then_eval2].
              unfold then_eval2; simp eval_aux; cbn -[eval].
              rewrite (refold_id_aux (A1 ⊗ B0)).
              now change (it_eqF _ ?RX ?RY _ (observe ?a) (_observe ?b)) with (it_eq_map ∅ₑ RX RY T1_0 a b).
           ++ cbn; econstructor.
              change (w_subst ?f (t+ ?A) ?w) with (v_subst f (t+ A) w).
              rewrite s_sub2_sub; apply CIH.
        -- dependent elimination w0.
           ++ unfold eval at 2; cbn -[eval then_eval2].
              unfold then_eval2; simp eval_aux; cbn -[eval].
              rewrite (refold_id_aux (A5 ⊕ B4)).
              now change (it_eqF _ ?RX ?RY _ (observe ?a) (_observe ?b)) with (it_eq_map ∅ₑ RX RY T1_0 a b).
           ++ cbn; econstructor.
              change (w_subst ?f (t+ ?A) ?w) with (v_subst f (t+ A) w).
              rewrite s_sub1_sub; apply CIH.
        -- dependent elimination w0.
           ++ unfold eval at 2; cbn -[eval then_eval2].
              unfold then_eval2; simp eval_aux; cbn -[eval].
              rewrite (refold_id_aux (A6 ⊕ B5)).
              now change (it_eqF _ ?RX ?RY _ (observe ?a) (_observe ?b)) with (it_eq_map ∅ₑ RX RY T1_0 a b).
           ++ cbn; econstructor.
              change (w_subst ?f (t+ ?A) ?w) with (v_subst f (t+ A) w).
              rewrite s_sub1_sub; apply CIH.
        -- dependent elimination w0.
           ++ unfold eval at 2; cbn -[eval then_eval2].
              unfold then_eval2; simp eval_aux; cbn -[eval].
              rewrite (refold_id_aux (↓ A11)).
              now change (it_eqF _ ?RX ?RY _ (observe ?a) (_observe ?b)) with (it_eq_map ∅ₑ RX RY T1_0 a b).
           ++ cbn; econstructor.
              change (Whn (ShiftPL (s_subst _ _))) with (t_subst e (t- _) (Whn (ShiftPL s7))).
              change (t_subst ?f ?A ?w) with (v_subst f A w).
              rewrite s_sub1_sub; apply CIH.
        -- dependent elimination w0.
           ++ unfold eval at 2; cbn -[eval then_eval2].
              unfold then_eval2; simp eval_aux; cbn -[eval].
              rewrite (refold_id_aux (⊖ A15)).
              now change (it_eqF _ ?RX ?RY _ (observe ?a) (_observe ?b)) with (it_eq_map ∅ₑ RX RY T1_0 a b).
           ++ cbn; econstructor.
              change (w_subst ?f (t- ?A) ?w) with (v_subst f (t- A) w).
              rewrite s_sub1_sub; apply CIH.
  - dependent elimination t1.
    + cbn; econstructor.
      change (t_subst e (t+ A) t0) with (v_subst e (t+ A) t0).
      rewrite s_sub1_sub; apply CIH.
    + dependent elimination t0.
      * cbn; econstructor.
        change (w_subst e (t- A) w) with (v_subst e (t- A) w).
        rewrite s_sub1_sub; apply CIH.
      * cbn; econstructor.
        change (RecR (t_subst (a_shift e) (t+ ?A) t1)) with (t_subst e (t+ A) (RecR t1)).
        change (t_subst ?f (t+ ?A) ?w) with (v_subst f (t+ A) w) at 2.
        rewrite t_sub1_sub; apply CIH.
      * dependent elimination w.
        -- pose (nope := (s_elt_upg h).(sub_prf)); dependent elimination nope.
        -- dependent elimination w0.
           ++ unfold eval at 2; cbn -[eval then_eval2].
              unfold then_eval2; simp eval_aux; cbn -[eval].
              now change (it_eqF _ ?RX ?RY _ (observe ?a) (_observe ?b)) with (it_eq_map ∅ₑ RX RY T1_0 a b).
           ++ cbn; econstructor; apply CIH.
        -- dependent elimination w0.
           ++ unfold eval at 2; cbn -[eval then_eval2].
              unfold then_eval2; simp eval_aux; cbn -[eval].
              rewrite 2 w_sub_ren.
              erewrite (w_sub_eq _ _ (s_eq_cat_l _ _)); auto.
              erewrite (w_sub_eq _ _ (s_eq_cat_r _ _)); auto.
              rewrite (refold_id_aux A4).
              rewrite (refold_id_aux B3).
              now change (it_eqF _ ?RX ?RY _ (observe ?a) (_observe ?b)) with (it_eq_map ∅ₑ RX RY T1_0 a b).
           ++ cbn; econstructor.
              change (w_subst ?f (t- ?A) ?w) with (v_subst f (t- A) w).
              rewrite s_sub2_sub; apply CIH.
        -- dependent elimination w0.
           ++ unfold eval at 2; cbn -[eval then_eval2].
              unfold then_eval2; simp eval_aux; cbn -[eval].
              rewrite (refold_id_aux A9).
              now change (it_eqF _ ?RX ?RY _ (observe ?a) (_observe ?b)) with (it_eq_map ∅ₑ RX RY T1_0 a b).
           ++ cbn; econstructor.
              change (w_subst ?f (t- ?A) ?w) with (v_subst f (t- A) w).
              rewrite s_sub1_sub; apply CIH.
        -- dependent elimination w0.
           ++ unfold eval at 2; cbn -[eval then_eval2].
              unfold then_eval2; simp eval_aux; cbn -[eval].
              rewrite (refold_id_aux B9).
              now change (it_eqF _ ?RX ?RY _ (observe ?a) (_observe ?b)) with (it_eq_map ∅ₑ RX RY T1_0 a b).
           ++ cbn; econstructor.
              change (w_subst ?f (t- ?A) ?w) with (v_subst f (t- A) w).
              rewrite s_sub1_sub; apply CIH.
        -- dependent elimination w0.
           ++ unfold eval at 2; cbn -[eval then_eval2].
              unfold then_eval2; simp eval_aux; cbn -[eval].
              now change (it_eqF _ ?RX ?RY _ (observe ?a) (_observe ?b)) with (it_eq_map ∅ₑ RX RY T1_0 a b).
           ++ cbn; econstructor.
              change (Whn (ShiftNR (s_subst _ _))) with (t_subst e (t+ _) (Whn (ShiftNR s8))).
              change (t_subst ?f ?A ?w) with (v_subst f A w).
              rewrite s_sub1_sub; apply CIH.
        -- dependent elimination w0.
           ++ unfold eval at 2; cbn -[eval then_eval2].
              unfold then_eval2; simp eval_aux; cbn -[eval].
              rewrite (refold_id_aux A18).
              now change (it_eqF _ ?RX ?RY _ (observe ?a) (_observe ?b)) with (it_eq_map ∅ₑ RX RY T1_0 a b).
           ++ cbn; econstructor.
              change (w_subst ?f (t+ ?A) ?w) with (v_subst f (t+ A) w).
              rewrite s_sub1_sub; apply CIH.
Qed.

Definition is_var {Γ A} (v : val Γ A) : Type := sigT (fun i : Γ ∋ A => v = s_var A i) .
Definition is_var_get {Γ A} {v : val Γ A} (p : is_var v) : Γ ∋ A := projT1 p .

Lemma is_var_dec {Γ A} (v : val Γ A) : is_var v + (is_var v -> False) .
  destruct A as [ [] A | [] A ].
  2,3: dependent elimination v; [ apply inr; intros [ i H ]; inversion H | | ].
  all: try dependent elimination v; try dependent elimination w.
  all: try now (apply inr; intros [ i H ]; inversion H).
  all: apply inl; econstructor; auto.
Qed.

Equations p_of_w_eq_aux_p {Γ : neg_ctx} (A : ty0 pos) (p : pat (t+ A)) (e : p_dom p =[val]> Γ)
          : p_of_w_0p A (w_subst e (t+ A) (w_of_p p) : whn Γ (t+ A)) = p
          by struct p :=
  p_of_w_eq_aux_p (1)     (POne)       e := eq_refl ;
  p_of_w_eq_aux_p (A ⊗ B) (PTen p1 p2) e := f_equal2 PTen
        (eq_trans (f_equal _ (w_sub_ren _ _ _ _)) (p_of_w_eq_aux_p A p1 _))
        (eq_trans (f_equal _ (w_sub_ren _ _ _ _)) (p_of_w_eq_aux_p B p2 _)) ;
  p_of_w_eq_aux_p (A ⊕ B) (POr1 p)     e := f_equal POr1 (p_of_w_eq_aux_p A p e) ;
  p_of_w_eq_aux_p (A ⊕ B) (POr2 p)     e := f_equal POr2 (p_of_w_eq_aux_p B p e) ;
  p_of_w_eq_aux_p (↓ A)  (PShiftP _)  e := eq_refl ;
  p_of_w_eq_aux_p (⊖ A)   (PNegP p)    e := f_equal PNegP (p_of_w_eq_aux_n A p e) ;

     with p_of_w_eq_aux_n {Γ : neg_ctx} (A : ty0 neg) (p : pat (t- A)) (e : p_dom p =[val]> Γ)
         : p_of_w_0n A (w_subst e (t- A) (w_of_p p) : whn Γ (t- A)) = p
         by struct p :=
  p_of_w_eq_aux_n (⊥)     (PBot)       e := eq_refl ;
  p_of_w_eq_aux_n (A ⅋ B) (PPar p1 p2) e := f_equal2 PPar
        (eq_trans (f_equal _ (w_sub_ren _ _ _ _)) (p_of_w_eq_aux_n A p1 _))
        (eq_trans (f_equal _ (w_sub_ren _ _ _ _)) (p_of_w_eq_aux_n B p2 _)) ;
  p_of_w_eq_aux_n (A & B) (PAnd1 p)    e := f_equal PAnd1 (p_of_w_eq_aux_n A p e) ;
  p_of_w_eq_aux_n (A & B) (PAnd2 p)    e := f_equal PAnd2 (p_of_w_eq_aux_n B p e) ;
  p_of_w_eq_aux_n (↑ A)  (PShiftN _)  e := eq_refl ;
  p_of_w_eq_aux_n (¬ A)   (PNegN p)    e := f_equal PNegN (p_of_w_eq_aux_p A p e) .

Definition p_dom_of_w_eq_P (Γ : neg_ctx) p : ty0 p -> Prop :=
  match p with
  | pos => fun A => forall (p : pat (t+ A)) (e : p_dom p =[val]> Γ),
      rew [fun p => p_dom p =[ val ]> Γ] p_of_w_eq_aux_p A p e in p_dom_of_w_0p A (w_subst e (t+ A) (w_of_p p)) ≡ₐ e
  | neg => fun A => forall (p : pat (t- A)) (e : p_dom p =[val]> Γ),
      rew [fun p => p_dom p =[ val ]> Γ] p_of_w_eq_aux_n A p e in p_dom_of_w_0n A (w_subst e (t- A) (w_of_p p)) ≡ₐ e
  end .

Lemma p_dom_of_v_eq {Γ p} A : p_dom_of_w_eq_P Γ p A .

  induction A; intros p e; dependent elimination p; cbn.
  - intros ? h; repeat (dependent elimination h; auto).
  - intros ? h; repeat (dependent elimination h; auto).
  - change (p_dom_of_w_0p _ (TenR ?v1 ?v2)) with ([ p_dom_of_w_0p A3 v1 , p_dom_of_w_0p B0 v2 ]).
    pose (H1 := w_sub_ren e r_concat_l (t+ A3) (w_of_p p)) .
    pose (H2 := w_sub_ren e r_concat_r (t+ B0) (w_of_p p0)) .
    pose (x1 := w_subst e (t+ A3) (w_rename r_concat_l (t+ A3) (w_of_p p))).
    pose (x2 := w_subst e (t+ B0) (w_rename r_concat_r (t+ B0) (w_of_p p0))).
    change (w_sub_ren e r_concat_l _ _) with H1.
    change (w_sub_ren e r_concat_r _ _) with H2.
    change (w_subst e (t+ A3) _) with x1 in H1 |- *.
    change (w_subst e (t+ B0) _) with x2 in H2 |- *.
    rewrite H1, H2; clear H1 H2 x1 x2; cbn.
    pose (H1 := p_of_w_eq_aux_p A3 p (e ⊛ᵣ r_concat_l)); change (p_of_w_eq_aux_p A3 _ _) with H1 in IHA1 |- *.
    pose (H2 := p_of_w_eq_aux_p B0 p0 (e ⊛ᵣ r_concat_r)); change (p_of_w_eq_aux_p B0 _ _) with H2 in IHA2 |- *.
    transitivity ([ rew [fun p : pat (t+ A3) => p_dom p =[ val ]> Γ] H1
                     in p_dom_of_w_0p A3 (w_subst (e ⊛ᵣ r_concat_l) (t+ A3) (w_of_p p)) ,
                    rew [fun p : pat (t+ B0) => p_dom p =[ val ]> Γ] H2
                     in p_dom_of_w_0p B0 (w_subst (e ⊛ᵣ r_concat_r) (t+ B0) (w_of_p p0)) ]).
    now rewrite <- H1, <- H2, eq_refl_map2_distr.
    apply s_eq_cover_uniq; [ apply IHA1 | apply IHA2 ] .
  - change (p_dom_of_w_0n _ (ParL ?v1 ?v2)) with ([ p_dom_of_w_0n _ v1 , p_dom_of_w_0n _ v2 ]).
    pose (H1 := w_sub_ren e r_concat_l (t- A4) (w_of_p p1)) .
    pose (H2 := w_sub_ren e r_concat_r (t- B1) (w_of_p p2)) .
    pose (x1 := w_subst e (t- A4) (w_rename r_concat_l (t- A4) (w_of_p p1))).
    pose (x2 := w_subst e (t- B1) (w_rename r_concat_r (t- B1) (w_of_p p2))).
    change (w_sub_ren e r_concat_l _ _) with H1.
    change (w_sub_ren e r_concat_r _ _) with H2.
    change (w_subst e (t- A4) _) with x1 in H1 |- *.
    change (w_subst e (t- B1) _) with x2 in H2 |- *.
    rewrite H1, H2; clear H1 H2 x1 x2; cbn.
    pose (H1 := p_of_w_eq_aux_n A4 p1 (e ⊛ᵣ r_concat_l)); change (p_of_w_eq_aux_n A4 _ _) with H1 in IHA1 |- *.
    pose (H2 := p_of_w_eq_aux_n B1 p2 (e ⊛ᵣ r_concat_r)); change (p_of_w_eq_aux_n B1 _ _) with H2 in IHA2 |- *.
    transitivity ([ rew [fun p : pat (t- A4) => p_dom p =[ val ]> Γ] H1
                     in p_dom_of_w_0n A4 (w_subst (e ⊛ᵣ r_concat_l) (t- A4) (w_of_p p1)) ,
                    rew [fun p : pat (t- B1) => p_dom p =[ val ]> Γ] H2
                     in p_dom_of_w_0n B1 (w_subst (e ⊛ᵣ r_concat_r) (t- B1) (w_of_p p2)) ]).
    now rewrite <- H1, <- H2, eq_refl_map2_distr.
    apply s_eq_cover_uniq; [ apply IHA1 | apply IHA2 ] .
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
  - intros ? h; repeat (dependent elimination h; auto).
  - intros ? h; repeat (dependent elimination h; auto).
  - match goal with | |- ?s ≡ₐ e => pose (xx := s); change (_ ≡ₐ e) with (xx ≡ₐ e) end .
    remember xx as xx'; unfold xx in Heqxx'; clear xx.
    rewrite (eq_trans Heqxx' (eq_sym (rew_map _ PNegP _ _))).
    apply IHA.
  - match goal with | |- ?s ≡ₐ e => pose (xx := s); change (_ ≡ₐ e) with (xx ≡ₐ e) end .
    remember xx as xx'; unfold xx in Heqxx'; clear xx.
    rewrite (eq_trans Heqxx' (eq_sym (rew_map _ PNegN _ _))).
    apply IHA.
Qed.

Lemma eval_nf_ret {Γ : neg_ctx} (u : nf Γ) : eval (p_app (s_var _ (fst (projT2 u))) (projT1 (snd (projT2 u))) (projT2 (snd (projT2 u)))) ≋ ret_delay u .
  unfold eval, iter_delay.
  rewrite iter_unfold.
  unfold comp_eq. apply it_eq_unstep; cbn.
  change (iter _ T1_0 ?x) with (iter_delay (fun c : state Γ => Ret' (eval_aux c)) x).
  destruct u as [ A [ i [ m γ ]]]; simpl t_neg in m; cbn [ fst snd projT1 projT2 ].
  unfold p_app.
  funelim (w_of_p m); cbn.
  - simpl_depind.
    destruct A0; inversion eqargs; clear - H0.
    revert t i m γ eqargs; rewrite <- H0; intros t i.
    pose (nope := (s_elt_upg i).(sub_prf)); dependent elimination nope.
  - simpl_depind.
    destruct A; inversion eqargs; clear - H0.
    revert t i m γ eqargs; rewrite <- H0; intros t i.
    pose (nope := (s_elt_upg i).(sub_prf)); dependent elimination nope.
  - simpl_depind.
    destruct A; inversion eqargs; cbn in eqargs.
    revert t i m γ eqargs H1 H2; rewrite <- H0; intros t i m γ eqargs H1 H2.
    dependent elimination H1; dependent elimination H2.
    rewrite (YesUIP _ _ _ eqargs eq_refl); clear eqargs.
    cbn; econstructor.
    unshelve econstructor; auto.
    split; [ reflexivity | unshelve econstructor; auto ].
    intros ? h; dependent elimination h.
  - simpl_depind.
    destruct A; inversion eqargs; cbn in eqargs.
    revert t i m γ eqargs H1 H2; rewrite <- H0; intros t i m γ eqargs H1 H2.
    dependent elimination H1; dependent elimination H2.
    rewrite (YesUIP _ _ _ eqargs eq_refl); clear eqargs.
    cbn; econstructor.
    unshelve econstructor; auto.
    split; [ reflexivity | unshelve econstructor; auto ].
    intros ? h; dependent elimination h.
  - simpl_depind.
    destruct A; inversion eqargs; cbn in eqargs.
    revert t i m γ eqargs H3 H4; rewrite <- H2; intros t i m γ eqargs H3 H4.
    dependent elimination H3; dependent elimination H4.
    rewrite (YesUIP _ _ _ eqargs eq_refl); clear eqargs.
    cbn; econstructor.
    unshelve econstructor; auto.
    split; [ reflexivity | unshelve econstructor; cbn ].
    apply (p_of_w_eq_aux_p _ (PTen p1 p2)).
    apply (p_dom_of_v_eq (_ ⊗ _) (PTen p1 p2)).
  - simpl_depind.
    destruct A; inversion eqargs; cbn in eqargs.
    revert t i m γ eqargs H3 H4; rewrite <- H2; intros t i m γ eqargs H3 H4.
    dependent elimination H3; dependent elimination H4.
    rewrite (YesUIP _ _ _ eqargs eq_refl); clear eqargs.
    cbn; econstructor.
    unshelve econstructor; auto.
    split; [ reflexivity | unshelve econstructor; cbn ].
    apply (p_of_w_eq_aux_n _ (PPar p1 p2)).
    apply (p_dom_of_v_eq (_ ⅋ _) (PPar p1 p2)).
  - simpl_depind.
    destruct A; inversion eqargs; cbn in eqargs.
    revert t i m γ eqargs H2 H3; rewrite <- H1; intros t i m γ eqargs H2 H3.
    dependent elimination H2; dependent elimination H3.
    rewrite (YesUIP _ _ _ eqargs eq_refl); clear eqargs.
    cbn; econstructor.
    unshelve econstructor; auto.
    split; [ reflexivity | unshelve econstructor; cbn ].
    apply (p_of_w_eq_aux_p _ (POr1 p)).
    apply (p_dom_of_v_eq (_ ⊕ _) (POr1 p)).
  - simpl_depind.
    destruct A; inversion eqargs; cbn in eqargs.
    revert t i m γ eqargs H2 H3; rewrite <- H1; intros t i m γ eqargs H2 H3.
    dependent elimination H2; dependent elimination H3.
    rewrite (YesUIP _ _ _ eqargs eq_refl); clear eqargs.
    cbn; econstructor.
    unshelve econstructor; auto.
    split; [ reflexivity | unshelve econstructor; cbn ].
    apply (p_of_w_eq_aux_p _ (POr2 p)).
    apply (p_dom_of_v_eq (_ ⊕ _) (POr2 p)).
  - simpl_depind.
    destruct A; inversion eqargs; cbn in eqargs.
    revert t i m γ eqargs H2 H3; rewrite <- H1; intros t i m γ eqargs H2 H3.
    dependent elimination H2; dependent elimination H3.
    rewrite (YesUIP _ _ _ eqargs eq_refl); clear eqargs.
    cbn; econstructor.
    unshelve econstructor; auto.
    split; [ reflexivity | unshelve econstructor; cbn ].
    apply (p_of_w_eq_aux_n _ (PAnd1 p)).
    apply (p_dom_of_v_eq (_ & _) (PAnd1 p)).
  - simpl_depind.
    destruct A; inversion eqargs; cbn in eqargs.
    revert t i m γ eqargs H2 H3; rewrite <- H1; intros t i m γ eqargs H2 H3.
    dependent elimination H2; dependent elimination H3.
    rewrite (YesUIP _ _ _ eqargs eq_refl); clear eqargs.
    cbn; econstructor.
    unshelve econstructor; auto.
    split; [ reflexivity | unshelve econstructor; cbn ].
    apply (p_of_w_eq_aux_n _ (PAnd2 p)).
    apply (p_dom_of_v_eq (_ & _) (PAnd2 p)).
  - simpl_depind.
    destruct A; inversion eqargs; cbn in eqargs.
    revert t i m γ eqargs H1 H2; rewrite <- H0; intros t i m γ eqargs H1 H2.
    dependent elimination H1; dependent elimination H2.
    rewrite (YesUIP _ _ _ eqargs eq_refl); clear eqargs.
    cbn; econstructor.
    unshelve econstructor; auto.
    split; [ reflexivity | unshelve econstructor; auto ].
    apply (p_dom_of_v_eq (↓ _) (PShiftP _)).
  - simpl_depind.
    destruct A; inversion eqargs; cbn in eqargs.
    revert t i m γ eqargs H1 H2; rewrite <- H0; intros t i m γ eqargs H1 H2.
    dependent elimination H1; dependent elimination H2.
    rewrite (YesUIP _ _ _ eqargs eq_refl); clear eqargs.
    cbn; econstructor.
    unshelve econstructor; auto.
    split; [ reflexivity | unshelve econstructor; auto ].
    apply (p_dom_of_v_eq (↑ _) (PShiftN _)).
  - simpl_depind.
    destruct A; inversion eqargs; cbn in eqargs.
    revert t i m γ eqargs H2 H3; rewrite <- H1; intros t i m γ eqargs H2 H3.
    dependent elimination H2; dependent elimination H3.
    rewrite (YesUIP _ _ _ eqargs eq_refl); clear eqargs.
    cbn; econstructor.
    unshelve econstructor; auto.
    split; [ reflexivity | unshelve econstructor; cbn ].
    apply (p_of_w_eq_aux_p _ (PNegP p)).
    apply (p_dom_of_v_eq (⊖ _) (PNegP p)).
  - simpl_depind.
    destruct A; inversion eqargs; cbn in eqargs.
    revert t i m γ eqargs H2 H3; rewrite <- H1; intros t i m γ eqargs H2 H3.
    dependent elimination H2; dependent elimination H3.
    rewrite (YesUIP _ _ _ eqargs eq_refl); clear eqargs.
    cbn; econstructor.
    unshelve econstructor; auto.
    split; [ reflexivity | unshelve econstructor; cbn ].
    apply (p_of_w_eq_aux_n _ (PNegN p)).
    apply (p_dom_of_v_eq (¬ _) (PNegN p)).
Qed.

Lemma foo {I : Type} {E : event I I} {X : psh I} {LX LY : relᵢ X X}
  : Subrelationᵢ LX LY -> Subrelationᵢ (it_eq (E:=E) LX) (it_eq (E:=E) LY) .
  intros H1 i a b H2.
  unfold it_eq; revert i a b H2; coinduction L CIH; intros i a b H2.
  apply it_eq_step in H2; cbn in *.
  remember (observe a) as oa; clear Heqoa a.
  remember (observe b) as ob; clear Heqob b.
  dependent elimination H2.
  - econstructor; now apply H1.
  - econstructor; now apply CIH.
  - econstructor; intro; now apply CIH.
Qed.

Lemma clean_hyp_ren {Γ Δ : neg_ctx} (c : state Γ) (e : Γ ⊆ Δ)
   : eval (s_rename e c) ≋ fmap_delay (n_rename e) (eval c) .
  rewrite <- (s_sub_id_l c) at 1.
  rewrite s_ren_sub.
  unfold comp_eq.
  etransitivity.
  eapply (foo (LX := eqᵢ _)).
  intros ? ? ? ->; now apply nf_eq_rfl.
  exact (clean_hyp c (a_ren e s_var)).
  remember (eval c) as t; clear Heqt c.
  unfold then_eval1.
  unfold fmap_delay, bind_delay'.
  rewrite bind_ret.
  apply (proj1 (t_gfp (it_eq_map ∅ₑ (fun _ : T1 => nf_eq)) _ _ _)).
  eapply (it_eq_up2bind_t (eqᵢ _)); econstructor; auto.
  intros [] u v ->.
  destruct v as [ x [ i [ m e' ] ] ]; cbn in *.
  unfold n_rename; cbn.
  unfold a_ren at 1; rewrite v_ren_id_r.
  rewrite (eval_nf_ret (x ,' (e x i , (m ,' a_comp (a_ren e s_var) e')))).
  change (gfp _ _ ?a ?b) with (it_eq (fun _ : T1 => nf_eq) a b).
  apply it_eq_unstep.
  econstructor.
  unshelve econstructor; auto; cbn.
  unshelve econstructor; auto; cbn.
  unshelve econstructor; auto; cbn.
  clear; intros ? i.
  unfold a_comp, a_ren; cbn.
  erewrite (v_sub_eq _ (s_var ⊛ᵣ e)); auto.
  now rewrite <- v_sub_ren, v_sub_id_l.
  intros ? j; now rewrite v_ren_id_r.
Qed.

Variant head_inst_nostep (u : sigT (fun A => pat (t_neg A))) : sigT (fun A => pat (t_neg A)) -> Prop :=
| HeadInst {Γ : neg_ctx} {A} (v : val Γ A) (m : pat (t_neg A)) (e : p_dom m =[val]> Γ)
      (p : is_var v -> False) (i : Γ ∋ (projT1 u : ty))
      (H : fmap_delay (pat_of_nf Γ) (eval (p_app v m e)) ≊ ret_delay ((projT1 u : ty) ,' (i , projT2 u)))
      : head_inst_nostep u (A ,' m) .

Lemma eval_app_not_var : well_founded head_inst_nostep .
  intros A; econstructor; intros [ B m ] H; dependent elimination H; cbn in *.
  destruct A0 as [ [] | [] ].
  1,3: cycle 1.
  all: dependent elimination v; try now destruct (p (_ ,' eq_refl)).
  all: clear p.
  all: dependent elimination m0; cbn in H.
  all: match goal with
       | u : assignment _ (neg_c_coe (p_dom (PVarN _))) _ |- _ =>
           cbn in H;
           pose (vv := e _ Ctx.top); change (e _ Ctx.top) with vv in H;
           remember vv as v'; clear e vv Heqv'; cbn in v'
       | _ => idtac
       end.
  all: match goal with
       | u : assignment _ (neg_c_coe (p_dom (PVarP _))) _ |- _ =>
           cbn in H;
           pose (vv := e _ Ctx.top); change (e _ Ctx.top) with vv in H;
           remember vv as v'; clear e vv Heqv'; cbn in v'
       | _ => idtac
       end.
  1-12,25-36: apply it_eq_step in H; now inversion H.
  1-12: match goal with
       | t : term _ (t- _) |- _ =>
           dependent elimination t;
           [ apply it_eq_step in H; now inversion H | apply it_eq_step in H; now inversion H | ]
       | _ => idtac
       end.
  13-24: match goal with
       | t : term _ (t+ _) |- _ =>
           dependent elimination t;
           [ apply it_eq_step in H; now inversion H | apply it_eq_step in H; now inversion H | ]
       | _ => idtac
       end.
  1-12: match goal with
       | w : whn _ (t- _) |- _ =>
           dependent elimination w;
           [ | apply it_eq_step in H; now inversion H ];
           try now destruct (p (_ ,' eq_refl))
       | _ => idtac
       end.
  13-24: match goal with
       | w : whn _ (t+ _) |- _ =>
           dependent elimination w;
           [ | apply it_eq_step in H; now inversion H ];
           try now destruct (p (_ ,' eq_refl))
       | _ => idtac
       end.
   all: apply it_eq_step in H; cbn in H; simp eval_aux in H; dependent elimination H.
   all: cbn in r_rel; inversion_sigma r_rel as [ H1 H2 ].
   all: revert m i H2; rewrite <- H1; intros m i H2; inversion_clear H2; cbn; clear.
   all: econstructor; intros [ A ee ] H; dependent elimination H; cbn in *.
   all: dependent elimination v; [ apply it_eq_step in H; now inversion H | apply it_eq_step in H; now inversion H | ].
  1-12: match goal with
       | w : whn _ (t- _) |- _ =>
           dependent elimination w;
           [ | apply it_eq_step in H; now inversion H ];
           try now destruct (p (_ ,' eq_refl))
       | _ => idtac
       end.
  now destruct (p1 (_ ,' eq_refl)).
  1-12: match goal with
       | w : whn _ (t+ _) |- _ =>
           dependent elimination w;
           [ | apply it_eq_step in H; now inversion H ];
           try now destruct (p (_ ,' eq_refl))
       | _ => idtac
       end.
Qed.

#[local] Instance sysD_typ  : baseT := {| typ := neg_ty |}.

#[local] Instance sysD_spec : observation_structure :=
  {| obs A := pat (t_neg (neg_coe A)) ;
     dom _ p := ctx_s_to (p_dom p) |} .

Definition state' (Γ : ctx neg_ty) : Type := state (ctx_s_from Γ).
Definition val' (Γ : ctx neg_ty) (a : neg_ty) : Type := val (ctx_s_from Γ) a.(sub_elt).

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

Definition from_has_L {Γ : ctx neg_ty} {t} (i : Γ ∋ t) : ctx_s_from Γ ∋ t.(sub_elt) .
  unfold ctx_s_from; destruct (ctx_s_to_inv Γ).
  exact (from_has_F i).
Defined.

Definition to_has_L {Γ : ctx neg_ty} {t} (i : ctx_s_from Γ ∋ t) : Γ ∋ s_elt_upg i .
  unfold s_elt_upg; unfold ctx_s_from in *; destruct (ctx_s_to_inv Γ).
  exact (to_has_F i).
Defined.

Lemma from_to_has_L {Γ : ctx neg_ty} {t} (i : ctx_s_from Γ ∋ t) : from_has_L (to_has_L i) = i .
  unfold from_has_L, to_has_L, s_elt_upg; unfold ctx_s_from in *.
  destruct (ctx_s_to_inv Γ).
  unfold from_has_F.
  pose proof (s_has_map_view_simpl (f := fun x : neg_ty => x) (i := i)).
  pose (xx := view_s_has_map (fun x : neg_ty => x) a (s_map_has (fun x : neg_ty => x) a i)).
  change (view_s_has_map _ _ _) with xx in H |- *.
  now rewrite H.
Qed.

Lemma to_from_has_L {Γ : ctx neg_ty} {t} (i : Γ ∋ t) : to_has_L (from_has_L i) = i .
  unfold to_has_L, from_has_L; unfold ctx_s_from.
  destruct (ctx_s_to_inv Γ).
  apply to_from_has_F.
Qed.

Definition r_from_to_l {Γ : neg_ctx} : ctx_s_from (ctx_s_to Γ) ⊆ Γ :=
  fun _ i => from_has_F (to_has_L i) .

Definition r_from_to_r {Γ : neg_ctx} : Γ ⊆ ctx_s_from (ctx_s_to Γ) :=
  fun _ i => from_has_L (to_has_F i) .

Lemma r_from_to_lr {Γ : neg_ctx} : r_from_to_l ⊛ᵣ r_from_to_r ≡ₐ @r_id _ Γ .
  intros ? i.
  refine (rew <- [fun x : ctx_s_to Γ ∋ s_elt_upg _ => from_has_F x = i ] to_from_has_L (to_has_F i) in _).
  exact (from_to_has_F i).
Qed.

Lemma r_from_to_rl {Γ : neg_ctx} : r_from_to_r ⊛ᵣ r_from_to_l ≡ₐ @r_id _ (ctx_s_from (ctx_s_to Γ)) .
  intros ? i.
  refine (rew <- [fun x : ctx_s_to Γ ∋ s_elt_upg _ => from_has_L x = i ] to_from_has_F (to_has_L i) in _).
  exact (from_to_has_L i).
Qed.

Definition r_to_from_l {Γ : ctx neg_ty} : ctx_s_to (ctx_s_from Γ) ⊆ Γ :=
  fun _ i => to_has_L (from_has_F i) .

Definition r_to_from_r {Γ : ctx neg_ty} : Γ ⊆ ctx_s_to (ctx_s_from Γ) :=
  fun _ i => to_has_F (from_has_L i) .

Lemma r_to_from_lr {Γ : ctx neg_ty} : r_to_from_l ⊛ᵣ r_to_from_r ≡ₐ @r_id _ Γ .
  intros ? i.
  refine (rew <- [fun x : ctx_s_from Γ ∋ a.(sub_elt) => to_has_L x = i ] from_to_has_F (from_has_L i) in _).
  exact (to_from_has_L i).
Qed.

Lemma r_to_from_rl {Γ : ctx neg_ty} : r_to_from_r ⊛ᵣ r_to_from_l ≡ₐ @r_id _ (ctx_s_to (ctx_s_from Γ)) .
  intros ? i.
  refine (rew <- [fun x : ctx_s_from Γ ∋ a.(sub_elt) => to_has_F x = i ] from_to_has_L (from_has_F i) in _).
  exact (to_from_has_F i).
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
  fun _ i => u _ (from_has_L i) .

#[global] Instance to_BB_proper {Γ1 Γ2} : Proper (ass_eq _ _ ==> ass_eq _ _) (@to_BB Γ1 Γ2).
  intros ? ? H ? i; exact (H _ (from_has_L i)).
Qed.

Definition from_BB {Γ1 Γ2} (u : Γ1 =[val']> Γ2) : ctx_s_from Γ1 =[val]> ctx_s_from Γ2 :=
  fun _ i => u _ (to_has_L i).

#[global] Instance from_BB_proper {Γ1 Γ2} : Proper (ass_eq _ _ ==> ass_eq _ _) (@from_BB Γ1 Γ2).
  intros u1 u2 H ? i; exact (H _ (to_has_L i)).
Qed.

Lemma to_from_BB {Γ1 Γ2} (u : Γ1 =[val']> Γ2) : to_BB (from_BB u) ≡ₐ u .
  unfold to_BB, from_BB.
  intros ? i; f_equal.
  apply to_from_has_L.
Qed.

Lemma from_to_BB {Γ1 Γ2} (u : ctx_s_from Γ1 =[val]> ctx_s_from Γ2) : from_BB (to_BB u) ≡ₐ u .
  unfold to_BB, from_BB.
  intros ? i; f_equal.
  apply from_to_has_L.
Qed.

Definition to_BF {Γ1 : ctx neg_ty} {Γ2 : neg_ctx} (u : ctx_s_from Γ1 =[val]> Γ2) : Γ1 =[val']> ctx_s_to Γ2 :=
  to_FF u ⊛ᵣ r_to_from_r.

#[global] Instance to_BF_proper {Γ1 Γ2} : Proper (ass_eq _ _ ==> ass_eq _ _) (@to_BF Γ1 Γ2).
  intros u1 u2 H ? i; apply (to_FF_proper _ _ H _ _).
Qed.

Definition from_BF {Γ1 : ctx neg_ty} {Γ2 : neg_ctx} (u : Γ1 =[val']> ctx_s_to Γ2) : ctx_s_from Γ1 =[val]> Γ2 :=
  from_FF (u ⊛ᵣ r_to_from_l) .

#[global] Instance from_BF_proper {Γ1 Γ2} : Proper (ass_eq _ _ ==> ass_eq _ _) (@from_BF Γ1 Γ2).
  intros u1 u2 H ? i; unfold from_BF.
  apply from_FF_proper; now rewrite H.
Qed.

Lemma from_BB_to_FF {Δ Γ : neg_ctx} (e : Γ =[ val ]> Δ) : a_ren r_from_to_l (from_BB (to_FF e)) ≡ₐ e ⊛ᵣ r_from_to_l .
  unfold from_BB, to_FF, to_FB, a_ren, s_map; cbn; intros ? i.
  now rewrite v_ren_ren, r_from_to_lr, v_ren_id_l.
Qed.

Definition ugly_var {Γ} : Γ =[val']> Γ := fun _ i => s_var _ (from_has_L i) .

Lemma from_BB_var {Γ} : from_BB (@ugly_var Γ) ≡ₐ s_var .
  unfold from_BB, from_FB, ugly_var, ctx_s_from, s_ren, s_map, from_has_L, to_has_L, r_to_from_l, s_elt_upg.
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
  unfold ugly_var, from_has_L, from_has_F in H.
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

Lemma ugly_var_dec {Γ x} (v : val' Γ x) : sigT (fun i : Γ ∋ x => v = ugly_var x i)
                                          + (sigT (fun i : Γ ∋ x => v = ugly_var x i) -> False) .
 destruct (is_var_dec v); [ apply inl | apply inr ].
 + unfold val' in v; unfold ugly_var, from_has_L; unfold ctx_s_from in *.
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
   exact (from_has_L x0 ,' e).
Qed.

Lemma ugly_is_var_ren {Γ1 Γ2 x} (v : val' Γ1 x) (e : Γ1 ⊆ Γ2) :
  sigT (fun i : Γ2 ∋ x => v_subst (from_BB (ugly_var ⊛ᵣ e)) (sub_elt x) v = ugly_var x i) ->
  sigT (fun i : Γ1 ∋ x => v = ugly_var x i) .
  intros p; unfold val' in v.
  destruct p as [ i H ].
  destruct x as [ [ [] A | [] A ] p ].
  all: try now destruct p.
  all: dependent elimination v; try now inversion H.
  all: dependent induction w; cbn in *; try now inversion H.
  all: apply (substS (fun p => sigT (fun i0 : Γ1 ∋ {| sub_elt := _ ; sub_prf := p |} => Whn (Var h) = Whn (Var (from_has_L i0)))) ((ctx_s_from Γ1).(sub_prf) _ h) p).
  all: exact (to_has_L h ,' f_equal (fun h => Whn (Var h)) (eq_sym (from_to_has_L h))).
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
  sigT (fun t : neg_ty => prod (Γ ∋ t) (sigT (fun m : pat (t_neg t) => ctx_s_to (p_dom m) =[ val' ]> Γ ))) :=
  (_ ,' (to_has_L (fst (projT2 u)) , (projT1 (snd (projT2 u)) ,' to_FB (projT2 (snd (projT2 u)))))) .

#[local] Instance sysD_val  : baseV := {| Subst.val := val' |}.
#[local] Instance sysD_conf : baseC := {| Subst.conf := state' |}.

#[local] Instance sysD_val_mon : subst_monoid _ :=
  {| v_var := @ugly_var ;
     v_sub := fun _ _ a _ v => v_subst (from_BB a) _ v |} .

#[local] Instance sysD_val_laws : subst_monoid_laws .
  econstructor.
  - intros Γ Δ u1 u2 H1 i v1 v2 H2.
    apply v_sub_eq; auto.
    now rewrite H1.
  - intros Γ1 Γ2 u ? i; cbn.
    etransitivity.
    unfold ugly_var, from_has_L; apply v_sub_id_r.
    unfold from_BB, from_has_F, r_to_from_l, s_elt_upg, ctx_s_from, to_has_L.
    destruct (ctx_s_to_inv Γ1); cbn.
    pose (xx := view_s_has_map (fun x : sigS is_neg => x) a0 i).
    fold xx; now destruct xx.
  - intros Γ1 Γ2 u ? i; cbn.
    etransitivity.
    apply v_sub_eq; [ apply from_BB_var | reflexivity ].
    apply v_sub_id_l.
  - intros Γ1 Γ2 Γ3 Γ4 p q r ? i; cbn.
    rewrite v_sub_sub.
    apply v_sub_eq; auto.
Qed.

#[local] Instance sysD_conf_mod : subst_module _ _ :=
  {| c_sub := fun _ _ a s => s_subst (from_BB a) s |} .

#[local] Instance sysD_conf_laws : subst_module_laws .
  econstructor.
  - intros Γ Δ u1 u2 H1 s1 s2 H2; cbn.
    apply s_sub_eq; auto.
    now rewrite H1.
  - intros Γ c; cbn.
    rewrite from_BB_var.
    apply s_sub_id_l.
  - intros Γ1 Γ2 Γ3 u v c; cbn.
    rewrite s_sub_sub.
    apply s_sub_eq; auto.
Qed.

#[local] Instance sysD_var_laws : var_assumptions.
  econstructor.
  - exact @ugly_var_inj.
  - exact @ugly_var_dec.
  - exact @ugly_is_var_ren.
Qed.

Lemma to_comp_eq {Γ} (u v : delay (nf (ctx_s_from Γ))) (H : u ≋ v) :
  Obs.comp_eq (fmap_delay to_nf u) (fmap_delay to_nf v) .
  unfold Obs.comp_eq, fmap_delay.
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

Definition from_pat_L {Γ : ctx neg_ty} : sigT (fun x : neg_ty => prod (Γ ∋ x) (pat (t_neg x))) -> pat' (ctx_s_from Γ) :=
  fun u => (_ ,' (from_has_L (fst (projT2 u)) , snd (projT2 u))) .

Definition from_pat_F {Γ : neg_ctx} : sigT (fun x : neg_ty => prod (ctx_s_to Γ ∋ x) (pat (t_neg x))) -> pat' Γ :=
  fun u => (_ ,' (from_has_F (fst (projT2 u)) , snd (projT2 u))) .

Definition to_pat {Γ : ctx neg_ty} : pat' (ctx_s_from Γ) -> sigT (fun x : neg_ty => prod (Γ ∋ x) (pat (t_neg x))) :=
  fun u => (_ ,' (to_has_L (fst (projT2 u)) , snd (projT2 u))) .

Lemma from_to_pat_F {Γ : neg_ctx} (x y : nf (ctx_s_from (ctx_s_to Γ))) (H : x = y)
  : from_pat_F (obs'_of_nf' _ (to_nf x)) = pat_of_nf _ (n_rename r_from_to_l y) .
  now rewrite H.
Qed.

#[local] Instance sysD_machine : machine :=
  {| Machine.eval := fun _ c => fmap_delay to_nf (eval c) ;
     Machine.app := fun _ _ v m e => p_app v m (from_FB e) |} .

#[local] Instance sysD_machine_law : machine_laws.
  econstructor; unfold sysD_spec, sysD_val in *; cbn in *.
  - intros Γ x v m u1 u2 H.
    destruct x as [ [ [] | [] ] neg ]; cbn in *; try now destruct neg.
    all: do 2 f_equal; apply w_sub_eq; [ now rewrite H | reflexivity ].
  - intros Γ1 Γ2 x e v m r; cbn.
    destruct x as [ [ [] | [] ] neg]; cbn in *; try now destruct neg.
    all: do 2 f_equal; change (w_subst ?u ?t) with (v_subst u t); rewrite v_sub_sub.
    all: apply v_sub_eq; auto.
  - intros Γ Δ c e .
    unfold Obs.comp_eq, fmap_delay.
    etransitivity.
    unshelve eapply fmap_eq. 5: exact (clean_hyp c (from_BB e)).
    exact ((fun _ => to_nf)).
    intros ? u v ->; unshelve econstructor; auto.
    unfold bind_delay', then_eval1.
    rewrite fmap_bind_com, bind_fmap_com.
    apply (proj1 (t_gfp (it_eq_map ∅ₑ (fun _ : T1 => Obs.nf'_eq)) _ _ _)).
    eapply (it_eq_up2bind_t (eqᵢ _)); econstructor; auto.
    intros [] u v ->.
    change (gfp _ _ ?a ?b) with (Obs.comp_eq a b).
    apply to_comp_eq.
    erewrite p_app_eq; auto.
    now rewrite <- (from_to_FB (projT2 (snd (projT2 v)))).
  - intros Γ [ x [ j [ m γ ] ] ] ; cbn in *.
    pose proof (eval_nf_ret ((x : ty) ,' (from_has_L j , (m ,' from_FB γ)))); cbn in H.
    apply to_comp_eq in H.
    rewrite H; clear H.
    unfold Obs.comp_eq; apply it_eq_unstep; cbn; econstructor.
    unshelve econstructor; auto; cbn.
    unshelve econstructor; auto; cbn.
    + exact (to_from_has_L _).
    + unshelve econstructor; auto; cbn.
      apply to_from_FB.
  - intros [ [ t H ] p ]; simpl in p.
    pose (u := (t ,' p) : sigT (fun t : ty => pat (t_neg t))); simpl in u.
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
      (*unfold Spec.eval_to_msg in i0.*)
      destruct x as [ t m ]; cbn in *.
      unshelve econstructor.
      + clear - Γ ; exact (ctx_s_from Γ).
      + clear - v ; exact v.
      + clear - e ; exact (from_FB e).
      + exact (from_has_L i).
      + intros []; apply p. (*; unfold Spec.is_var, Spec.v_var.*)
        apply (substS (fun u => sigT (fun i1 : Γ ∋ {| sub_elt := t; sub_prf := u |} => v = ugly_var {| sub_elt := t; sub_prf := u |} i1)) ((ctx_s_from Γ).(sub_prf) _ x)).
        refine (to_has_L x ,' _).
        rewrite e0; unfold ugly_var; f_equal; symmetry.
        apply from_to_has_L.
      + cbn in *.
        eapply (fmap_eq (RY := eqᵢ _) (fun _ => from_pat_L) (fun _ => from_pat_L)) in i0; [ | intros ? ? ? ->; auto ].
        unfold eval_to_obs, Machine.eval in i0; cbn in i0; unfold fmap_delay in i0.
        rewrite 2 fmap_fmap_com in i0.
        transitivity (((fun (_ : T1) (x : nf (ctx_s_from Γ)) => from_pat_L (obs'_of_nf' Γ (to_nf x))) <$>
        eval (p_app v m (from_FB e)))).
        unfold fmap_delay.
        eapply fmap_eq; auto.
        ** intros [] n1 n2 H'; cbn.
           destruct n1 as [ x1 [ i1 [ m1 γ1 ]] ].
           destruct n2 as [ x2 [ i2 [ m2 γ2 ]] ].
           destruct H' as [ H2 [ H3 [ H4 _ ] ] ]; cbn in *.
           unfold Obs.obs'_of_nf', pat_of_nf, from_pat_L; cbn.
           revert i1 m1 γ1 H3 H4; rewrite H2; clear H2 x1; intros i1 m1 γ1 H3 H4; cbn in H3,H4.
           now rewrite H3, H4, from_to_has_L.
        ** rewrite i0; clear.
           apply it_eq_unstep; cbn; econstructor; reflexivity.
    * clear - H3; cbn in H3.
      change ({| sub_elt := sub_elt (projT1 y); sub_prf := sub_prf (projT1 y) |}) with (projT1 y) in H3.
      assert (H4 : (projT1 y,' projT2 y) = y) ; [ | rewrite H4 in H3; exact H3 ].
      clear; destruct y; cbn in *.
      reflexivity.
Qed.

Definition sem_act (Δ Γ : neg_ctx) : Type := ogs_act (ctx_s_to Δ) (∅ ▶ ctx_s_to Γ) .
Definition sem_pas (Δ Γ : neg_ctx) : Type := ogs_pas (ctx_s_to Δ) (∅ ▶ ctx_s_to Γ) .

Definition ugly_state {Γ : neg_ctx} (c : state Γ) : state (ctx_s_from (ctx_s_to Γ)) :=
  match ctx_s_to_inv (ctx_s_to Γ) as f in (fiber _ b) return (b = ctx_s_to Γ -> state (fib_extr f)) with
  | Fib a => fun H => rew <- [state ∘ coe_ctx] ctx_s_to_inj H in c
  end eq_refl .

Definition from_to_state {Γ : neg_ctx} (c : state Γ) : state (ctx_s_from (ctx_s_to Γ)) :=
  s_rename r_from_to_r c .

Definition interp_act_s Δ {Γ : neg_ctx} (c : state Γ) : sem_act Δ Γ :=
  m_strat (∅ ▶ ctx_s_to Γ) (inj_init_act (ctx_s_to Δ) (from_to_state c)) .
Notation "⟦ t ⟧ₛ" := (interp_act_s _ t) .

Definition ogs_weq_act Δ {Γ} : relation (sem_act Δ Γ) := fun u v => u ≈ v .
Notation "u ≈[ Δ ]≈ v" := (ogs_weq_act Δ u v) (at level 40).

Definition eval_to_msg {Γ : neg_ctx} (c : state Γ) : delay (pat' Γ) :=
  fmap_delay (pat_of_nf Γ) (eval c) .

Definition subst_eq (Δ : neg_ctx) {Γ} : relation (state Γ) :=
  fun u v => forall (σ : Γ =[val]> Δ), eval_to_msg (s_subst σ u) ≈ eval_to_msg (s_subst σ v) .

Theorem sysD_subst_correct (Δ : neg_ctx) {Γ : neg_ctx} (x y : state Γ)
  : ⟦ x ⟧ₛ ≈[ Δ ]≈ ⟦ y ⟧ₛ -> subst_eq Δ x y .
  intros H σ.
  apply (ogs_correction (M := sysD_machine)
            (ctx_s_to Δ)
            (from_to_state x)
            (from_to_state y)) in H.
  specialize (H (to_FF σ)).

  unfold eval_in_env, eval_to_msg, eval_to_obs in H ; cbn in H.

  unshelve eapply (fmap_weq (RY := eqᵢ _) (fun _ : T1 => from_pat_F) (fun _ : T1 => from_pat_F) _ _ _ _) in H.
  intros [] ? ? ->; auto.

  unfold fmap_delay in H.
  rewrite 4 fmap_fmap_com in H.
  rewrite 2 (fmap_eq (RY := eqᵢ _) _ _ (fun _ a b H => from_to_pat_F a b H) _ _ _ (reflexivity _)) in H.
  rewrite <- 2 (fmap_fmap_com (g := fun _ : T1 => pat_of_nf Δ) (f := fun _ : T1 => n_rename r_from_to_l)) in H.
  fold (fmap_delay (pat_of_nf Δ)) in H.
  fold (fmap_delay (n_rename (Δ := Δ) r_from_to_l)) in H.
  rewrite <- 2 (fmap_comp_eq (clean_hyp_ren _ _)) in H.
  rewrite 2 s_ren_sub in H.
  rewrite 2 (s_sub_eq _ _ (from_BB_to_FF σ) _ _ eq_refl) in H.
  unfold from_to_state in H.
  rewrite <- 2 s_sub_ren, 2 s_ren_ren in H.
  rewrite 2 (s_ren_eq _ _ (r_from_to_lr) _ _ eq_refl) in H.
  rewrite 2 s_ren_id_l in H.
  exact H.
Qed.

Definition c_of_t_p {Γ : neg_ctx} {x : ty0 pos} (t : term Γ (t+ x)) : state (Γ ▶ₛ {| sub_elt := t- x ; sub_prf := stt |}) :=
  Cut _ (t_shift _ t) (Whn (Var Ctx.top)) .
Notation "⟦ t ⟧ₚ" := (interp_act_s _ (c_of_t_p t)) .

Definition a_of_sk_p {Γ Δ : neg_ctx} {x : ty0 pos} (s : Γ =[val]> Δ) (k : term Δ (t- x))
  : (Γ ▶ₛ {| sub_elt := t- x ; sub_prf := stt |}) =[val]> Δ :=
  a_append s (k : val Δ (t- x)) .

Lemma sub_csk_p {Γ Δ : neg_ctx} {x : ty0 pos} (t : term Γ (t+ x)) (s : Γ =[val]> Δ) (k : term Δ (t- x))
              : Cut _ (t_subst s _ t) k = s_subst (a_of_sk_p s k) (c_of_t_p t) .
  cbn; f_equal.
  unfold t_shift; rewrite t_sub_ren.
  now apply t_sub_eq.
Qed.

Definition ciu_p_eq (Δ : neg_ctx) {Γ} {x : ty0 pos} : relation (term Γ (t+ x)) :=
  fun u v => forall (σ : Γ =[val]> Δ) (k : term Δ (t- x)),
      eval_to_msg (Cut _ (t_subst σ _ u) k) ≈ eval_to_msg (Cut _ (t_subst σ _ v) k) .

Theorem sysD_ciu_p_correct (Δ : neg_ctx) {Γ : neg_ctx} {t} (x y : term Γ (t+ t))
  : ⟦ x ⟧ₚ ≈[ Δ ]≈ ⟦ y ⟧ₚ -> ciu_p_eq Δ x y .
  intros H σ k.
  rewrite 2 sub_csk_p.
  now apply sysD_subst_correct.
Qed.

Definition ciu_n_eq (Δ : neg_ctx) {Γ} {x : ty0 neg} : relation (term Γ (t- x)) :=
  fun u v => forall (σ : Γ =[val]> Δ) (k : term Δ (t+ x)),
      eval_to_msg (Cut _ k (t_subst σ _ u)) ≈ eval_to_msg (Cut _ k (t_subst σ _ v)) .

Definition c_of_t_n {Γ : neg_ctx} {x : ty0 neg} (t : term Γ (t- x)) : state (Γ ▶ₛ {| sub_elt := t+ x ; sub_prf := stt |}) :=
  Cut _ (Whn (Var Ctx.top)) (t_shift _ t) .
Notation "⟦ t ⟧ₙ" := (interp_act_s _ (c_of_t_n t)) .

Definition a_of_sk_n {Γ Δ : neg_ctx} {x : ty0 neg} (s : Γ =[val]> Δ) (k : term Δ (t+ x))
  : (Γ ▶ₛ {| sub_elt := t+ x ; sub_prf := stt |}) =[val]> Δ :=
  a_append s (k : val Δ (t+ x)) .

Lemma sub_csk_n {Γ Δ : neg_ctx} {x : ty0 neg} (t : term Γ (t- x)) (s : Γ =[val]> Δ) (k : term Δ (t+ x))
              : Cut _ k (t_subst s _ t) = s_subst (a_of_sk_n s k) (c_of_t_n t) .
  cbn; f_equal.
  unfold t_shift; rewrite t_sub_ren.
  now apply t_sub_eq.
Qed.

Theorem sysD_ciu_n_correct (Δ : neg_ctx) {Γ : neg_ctx} {t} (x y : term Γ (t- t))
  : ⟦ x ⟧ₙ ≈[ Δ ]≈ ⟦ y ⟧ₙ -> ciu_n_eq Δ x y .
  intros H σ k.
  rewrite 2 sub_csk_n.
  now apply sysD_subst_correct.
Qed.
