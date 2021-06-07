Set Universe Polymorphism.

From ExtLib.Data Require Import Nat Fin.
From ITree Require Import ITree Events.Dependent.

From Equations Require Import Equations.

(******************)
(* misc notations *)

#[global] Notation endo T := (T -> T).
#[global] Notation "f ∘ g" := (Basics.compose f g) (at level 60) : function_scope. 
Definition compose {A : Type} {B : A -> Type} {C : forall a, B a -> Type}
           (g : forall a (b : B a), C _ b)
           (f : forall a, B a)
           : forall a, C _ (f a) := fun a => g _ (f a).
#[global] Notation "f ∘' g" := (compose f g) (at level 60) : function_scope. 

Definition tau {E R} (t : itree E R) : itree E R := Tau t.

(***************)
(* Finite sets *)

Variant T0 := .
Variant T1 := t1_0.
Variant T2 := t2_0 | t2_1.
Variant T3 := t3_0 | t3_1 | t3_2.

Definition ex_falso {A : Type} (bot : T0) : A := match bot with end.


(********************************)
(* Couple lemma on list/vec/fin *)

Equations l_get {X} (xs : list X) : fin (length xs) -> X :=
  l_get (cons x xs) F0     := x ;
  l_get (cons x xs) (FS i) := l_get xs i.

Notation "xs .[ i ]" := (l_get xs i) (at level 10).

Equations l_acc {X} (n : nat) (f : fin n -> X) : list X :=
  l_acc O     f := nil ;
  l_acc (S n) f := cons (f F0) (l_acc n (f ∘ FS)).

Equations len_acc {X} n (f : fin n -> X) : length (l_acc n f) = n :=
  len_acc O     f := eq_refl ;
  len_acc (S n) f := f_equal S (len_acc n (f ∘ FS)).

Equations dvec {X} (ty : X -> Type) (xs : list X) : Type :=
  dvec ty nil := T1 ;
  dvec ty (cons x xs) := ty x * dvec ty xs.
Transparent dvec.

Equations d_get {X ty} (c : list X) (d : dvec ty c) (i : fin (length c)) : ty (l_get c i) :=
  d_get (cons t ts) r F0     := fst r ;
  d_get (cons t ts) r (FS i) := d_get ts (snd r) i.

(********************************************************)
(* Dependent version of stuff in ITree.Interp.Recursion *)

Arguments depE : clear implicits.  (* index is usually hard to infer *)

Equations dcalling' {A B} {F : Type -> Type}
          (f : forall a, itree F (B a)) : depE A B ~> itree F :=
dcalling' f _ (Dep a) := f a.

Definition drec {E : Type -> Type} {A B}
           (body : forall a, itree (depE A B +' E) (B a)) :
  forall a, itree E (B a) :=
  fun a => mrec (dcalling' body) (Dep a).

Definition dcall {E A B} (a : A) : itree (depE A B +' E) (B a) :=
  ITree.trigger (inl1 (Dep a)).

Declare Scope indexed_scope.
Open Scope indexed_scope.
Delimit Scope indexed_scope with indexed.

Variant prod1 (D E : Type -> Type) : Type -> Type :=
| pair1 : forall {X Y}, D X -> E Y -> prod1 D E (X * Y).

#[global] Notation "D *' E" := (prod1 D E) (at level 50).

(* (covariant) presheaves *)
Definition psh (I : Type) : Type := I -> Type.

(* pointwise arrows *)
Definition arrᵢ {I} (X Y : psh I) : Type := forall {i}, X i -> Y i.
#[global] Infix "⇒ᵢ" := (arrᵢ) (at level 20) : indexed_scope.

(* pointwise coproduct *)
Definition sumᵢ {I} (X Y : psh I) : psh I := fun i => (X i + Y i)%type.
Infix "+ᵢ" := (sumᵢ) (at level 20) : indexed_scope.

(* pointwise arrows between F G : endo (psh I) *)
Notation "F ⟹ G" := (forall X : psh _, F X ⇒ᵢ G X) (at level 30).


Inductive fiber {A B} (f : A -> B) : B -> Type := Fib a : fiber f (f a).
Arguments Fib {A B f}.
Derive NoConfusion for fiber.

(* These two functions actually form an isomorphism (extensionally)
      (fiber f ⇒ᵢ X) ≅ (∀ a → X (f a))
 *)
Definition fiber_ext {A B} {f : A -> B} {b : B} : fiber f b -> A :=
  fun '(Fib a) => a.
Definition fiber_coh {A B} {f : A -> B} {b : B} :
    forall p : fiber f b, f (fiber_ext p) = b :=
  fun '(Fib _) => eq_refl.
Definition fiber_mk {A B} {f : A -> B} a : forall b (p : f a = b), fiber f b :=
  eq_rect (f a) (fiber f) (Fib a).
 
Definition fiber_into {A B} {f : A -> B} X (h : forall a, X (f a)) : fiber f ⇒ᵢ X :=
  fun _ '(Fib a) => h a.
Definition fiber_from {A B} {f : A -> B} X (h : fiber f ⇒ᵢ X) a : X (f a) :=
  h _ (Fib a).

Notation "X @ i" := (fiber (fun (_ : X) => i)) (at level 20) : indexed_scope.
Definition pin {I X} (i : I) : X -> (X @ i) i := Fib.
Definition pin_from {I X Y} {i : I} : ((X @ i) ⇒ᵢ Y) -> (X -> Y i) := fiber_from _.
Definition pin_into {I X Y} {i : I} : (X -> Y i) -> (X @ i ⇒ᵢ Y) := fiber_into _.
