From OGS Require Import Prelude.
From OGS.Utils Require Import Rel.
From OGS.Ctx Require Import All Ctx Covering.

Inductive fin : nat -> Type :=
| FZe {n} : fin (S n)
| FSu {n} : fin n -> fin (S n)
.

Inductive c_exists {X} (P : X -> Prop) : ctx X -> Prop :=
| top {Γ x} : P x -> c_exists P (Γ ▶ₓ x)
| pop {Γ x} : c_exists P Γ -> c_exists P (Γ ▶ₓ x)
.

Inductive ty : nat -> Type :=
| TVar {n} : fin n -> ty n
| TArr {n} : ty n -> ty n -> ty n
| TAll {n} : ty (S n) -> ty n
.

Definition TAsgn (X : nat -> Type) (m n : nat) := fin m -> X n .
Definition TRen := TAsgn fin. 
Definition TSub := TAsgn ty. 

Equations ty_a_append {X m n} : TAsgn X m n -> X n -> TAsgn X (S m) n :=
  ty_a_append r x FZe     := x ;
  ty_a_append r x (FSu i) := r i .

Definition f_shift1 {m n} (r : TRen m n) : TRen (S m) (S n)
  := ty_a_append (FSu ∘ r) FZe .

Equations ty_ren {m n} : ty m -> TRen m n -> ty n :=
  ty_ren (TVar i)   r := TVar (r i) ;
  ty_ren (TArr a b) r := TArr (ty_ren a r) (ty_ren b r) ;
  ty_ren (TAll a)   r := TAll (ty_ren a (f_shift1 r)) .

Definition ty_shift1 {m n} (s : TSub m n)
  : TSub (S m) (S n)
  := ty_a_append (fun i => ty_ren (s i) FSu) (TVar FZe) .

Equations ty_sub {m n} : ty m -> TSub m n -> ty n :=
  ty_sub (TVar i)   s := s i ;
  ty_sub (TArr a b) s := TArr (ty_sub a s) (ty_sub b s) ;
  ty_sub (TAll a)   s := TAll (ty_sub a (ty_shift1 s)) .

Record in_ctx (X : nat -> Type) := InC { dom : nat ; elt : X dom }. 
#[global] Arguments InC {X d} t : rename.
#[global] Arguments dom {X}.
#[global] Arguments elt {X}.
Derive NoConfusion NoConfusionHom for in_ctx.

Definition strict (X : nat -> Type) (n : nat) := forall z, TRen n z -> X z.
Definition s_ren {X m n} (r : TRen m n) (s : strict X m) : strict X n
  := fun z k => s z (k ∘ r).
Definition s_extr {X n} (s : strict X n) : X n := s n (fun i => i).

Definition sty := strict ty.

Definition fty := in_ctx sty.
Definition wctx := in_ctx (fun n => ctx (sty n)).

Definition c_ren {m n} (r : TRen m n) (ts : ctx (wty m))
  : ctx (wty n) 
  := c_map (w_ren r) ts .

Record w_has (Γ : wctx) (t : fty) := {
  has_dom : TRen t.(dom) Γ.(dom) ;
  has_elt : c_exists (fun w : wty _ => t.(elt) _ has_dom = wextr w) Γ.(elt) ;
}.

Definition w_emp : wctx := {| dom := O ; elt := ∅ₓ%ctx |}.

Lemma w_emp_case {t} : w_has w_emp t -> T0 .
Proof. intros [ d e ]; cbn in *; dependent elimination e. Qed.

Definition Ren (Γ Δ : wctx) := forall t, w_has Γ t -> w_has Δ t .
Record span (Γ Δ : wctx) := {
  s_src : wctx ;
  s_ren_l : Ren s_src Γ ;
  s_ren_r : Ren s_src Δ ;
}.
#[global] Arguments s_src {Γ Δ}.
#[global] Arguments s_ren_l {Γ Δ}.
#[global] Arguments s_ren_r {Γ Δ}.

Definition pullback {Γ Δ} (S : span Γ Δ) : wctx.
  destruct S as [ S ren_l ren_r ].
