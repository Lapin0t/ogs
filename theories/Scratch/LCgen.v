From ExtLib.Data Require Import Nat Fin List Unit.
From Coq Require Import Logic.
Import EqNotations.
From Equations Require Import Equations.

From OGS Require Import EventD CatD ITreeD Utils RecD AngelicD.

Set Primitive Projections.
Set Equations Transparent.

Variant polarity : Type := Pos | Neg.

Definition type_spec := event polarity polarity.

Section LCgen.
Variable T : type_spec.

(* types, indexed by polarity *)
Inductive ty' (p : polarity) : Type :=
  Ty' (s : qry T p) (k : forall r, ty' (nxt T s r)) : ty' p.

(* types, any polarity *)
Variant ty : Type := 
  Ty (p : polarity) (s : qry T p) (k : forall r, ty' (nxt T s r)) : ty.

Definition ctx : Type := list ty.
Notation "Γ ▶ x" := (x :: Γ) (at level 20).

Inductive has : ctx -> ty -> Type :=
| top {Γ x} : has (Γ ▶ x) x
| pop {Γ x y} : has Γ x -> has (Γ ▶ y) x.

Notation "Γ ∋ t" := (has Γ t) (at level 30).
Definition pop' {Γ} : forall t, Γ ∋ t -> (Γ ▶ t) ∋ t := fun _ => pop.

Record lang_spec : Type := {
(* positive terms are defined by their introductions *)
pos_intro_r : ty' Pos -> Type ;
neg_elim_r : ty' Neg -> Type ;
(*elim_r : ty -> Type ;

(* set of premises *)
intro_p : forall t, intro_r t -> Type ;
(* context extension for premises (binders) *)
intro_c : forall t (r : intro_r t), intro_p t r -> ctx ;
(* type for premises *)
intro_t : forall t (r : intro_r t), intro_p t r -> ty ;

elim_p : forall t, elim_r t -> Type ;
  elim_t : forall t, elim_r t -> *)
}.
