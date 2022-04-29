From Equations Require Import Equations.
Set Equations Transparent.

Import Coq.Init.Logic.EqNotations. (* rew syntax *)

From ExtLib.Data Require Import Nat Fin.
From OGS.Utils Require Import Prelude.

Derive Signature for fin.

(** Weakening for finite sets *)
Equations f_inj {m n} : fin m -> fin (m + n) :=
  @f_inj (S m) _ (F0)   := F0 ;
  @f_inj (S m) _ (FS i) := FS (f_inj i) .

(** Vectors, ie length-indexed lists *)
Inductive vec (X : Type) : nat -> Type :=
| Vnil : vec X 0
| Vcon {n} : X -> vec X n -> vec X (S n)
.
Arguments Vnil {X}.
Arguments Vcon {X n} x xs.

(** Safe index lookup *)
Equations v_get {X n} (xs : vec X n) : fin n -> X :=
  v_get (Vcon x xs) F0     := x ;
  v_get (Vcon x xs) (FS i) := v_get xs i .
Notation "xs '[ i ]" := (v_get xs i) (at level 10).

(** Vector concatenation *)
Equations v_cat {X m n} (xs : vec X m) (ys : vec X n) : vec X (m + n) :=
  v_cat Vnil        ys := ys ;
  v_cat (Vcon x xs) ys := Vcon x (v_cat xs ys) .
Notation "xs ++ ys" := (v_cat xs ys).

Equations v_inj_cat {X m n} (xs : vec X m) (ys : vec X n) (i : fin m)
          : xs '[i] = (xs ++ ys) '[f_inj i] :=
  v_inj_cat (Vcon x xs) ys (F0)   := eq_refl ;
  v_inj_cat (Vcon x xs) ys (FS i) := v_inj_cat xs ys i .

(** Partial (multi?)functions ∀ x : X, A x, with domain defined by a vector. *)
Definition ffun {X} (A : X -> Type) (n : nat) (xs : vec X n) : Type :=
  forall i : fin n, A (xs '[i]).

Section ffun.
  Context {X : Type} {A : X -> Type}.

  (** Join partial functions *)
  Equations ff_cat {m n} xs {ys} (f : ffun A m xs) (g : ffun A n ys)
            : ffun A (m + n) (v_cat xs ys) :=
    ff_cat Vnil        f g i      := g i ;
    ff_cat (Vcon x xs) f g F0     := f F0 ;
    ff_cat (Vcon x xs) f g (FS i) := ff_cat xs (f ∘ FS) g i .

  (** Concatenation preserves pointwise relations *)
  Equations ff_cat_lem {m n} (P : forall x, A x -> A x -> Prop)
            xs {ys} {f0 f1 : ffun A m xs} {g0 g1 : ffun A n ys}
            (Hf : forall i, P (xs '[i]) (f0 i) (f1 i))
            (Hg : forall i, P (ys '[i]) (g0 i) (g1 i))
            : forall i, P ((v_cat xs ys) '[i]) (ff_cat xs f0 g0 i)
                                          (ff_cat xs f1 g1 i)
    :=
      ff_cat_lem P Vnil        Hf Hg i      := Hg i ;
      ff_cat_lem P (Vcon _ xs) Hf Hg (F0)   := Hf F0 ;
      ff_cat_lem P (Vcon _ xs) Hf Hg (FS i) := ff_cat_lem P xs (Hf ∘ FS) Hg i.

  (** Same inj_cat lemma, now for ffun *)
  Equations ff_inj_cat {m n} xs {ys} (f : ffun A m xs) (g : ffun A n ys) (i : fin m)
            : ff_cat xs f g (f_inj i) = rew (v_inj_cat xs ys i) in f i :=
    ff_inj_cat (Vcon x xs) f g (F0)   := eq_refl ;
    ff_inj_cat (Vcon x xs) f g (FS i) := ff_inj_cat xs (f ∘ FS) g i .
End ffun.

(** Basically the ffun is finite universal quantification, fsum is
    finite existential quantification *)
Definition fsum {X} (A : X -> Type) n (xs : vec X n) : Type :=
  { i : fin n & A (xs '[i]) }.

(** Lifting of the weakening *)
Definition fs_inj {X A m n} {xs : vec X m} {ys : vec X n}
           (a : fsum A m xs) : fsum A (m + n) (v_cat xs ys) :=
  existT _ (f_inj (projT1 a)) (rew [A] (v_inj_cat xs ys (projT1 a)) in projT2 a).

Section ffun2.
  Context {I X : Type} {A : X -> Type}.

  Definition ffun2 (ii : forall x, A x -> I) (B : I -> Type) : forall n, vec X n -> Type :=
    ffun (fun x => forall a : A x, B (ii x a)).

  (* WIP uncurrying stuff
  Definition ffun2' (ii : forall x, A x -> I) (B : I -> Type) n (xs : vec X n) : Type :=
    forall a : fsum A n xs, B (ii _ (projT2 a)).    

  Definition ff2_app {ii B n xs} : ffun2 ii B n xs -> ffun2' ii B n xs :=
    fun f a => f (projT1 a) (projT2 a).
  Definition ff2_curry {ii B n xs} : ffun2' ii B n xs -> ffun2 ii B n xs :=
    fun f i a => f (existT _ i a).

  (* half-curried version of ff_cat, don't ask why *)
  Definition ff2_cat {ii B m n} xs ys (f : ffun2' ii B m xs)
             (g : ffun2 ii B n ys) : ffun2 ii B (m + n) (v_cat xs ys) :=
    ff_cat xs (ff2_curry f) g.
  *)

  (* this now has a different rewrite pattern than the same lemma on ffun *)
  (* WIP later
  Equations ff2_inj_cat {ii B m n} xs {ys}
            (f : ffun2 ii B m xs) (g : ffun2 ii B n ys)
            (i : fin m) (a : A (xs '[i]))
            : ff_cat xs f g (f_inj i) a = rew (v_inj_lem xs ys i) in f i :=
    ff2_inj_cat := _ .
   *)
End ffun2.
