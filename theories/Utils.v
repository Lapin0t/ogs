Set Universe Polymorphism.

From ExtLib.Data Require Import Nat Fin.

From Equations Require Import Equations.

(******************)
(* misc notations *)

#[global] Notation endo T := (T -> T).
  
#[global] Notation "f ∘ g" := (Basics.compose f g) (at level 40, left associativity) : function_scope.  
Definition compose {A : Type} {B : A -> Type} {C : forall a, B a -> Type}
           (g : forall a (b : B a), C _ b)
           (f : forall a, B a)
           : forall a, C _ (f a) := fun a => g _ (f a).
#[global] Notation "f ∘' g" := (compose f g) (at level 60) : function_scope. 

Notation "a ,& b" := (existT _ a b) (at level 30).
(*Notation "'ex' a" := (existT _ _ a) (at level 30).*)

Definition uncurry2 {A B : Type} {C : A -> B -> Type}
                    (f : forall a b, C a b) (i : A * B) :=
  f (fst i) (snd i).
Definition curry2 {A B : Type} {C : A -> B -> Type}
                  (f : forall i, C (fst i) (snd i)) a b :=
  f (a , b).

Definition uncurry2' {A : Type} {B : A -> Type} {C : forall a, B a -> Type}
                    (f : forall a b, C a b) (i : sigT B) :=
  f (projT1 i) (projT2 i).

(*
Definition curry2' {A : Type} {B : A -> Type} {C : forall a, B a -> Type}
                  (f : forall i, C (projT1 i) (projT2 i)) a b :=
  f (a ,& b).
*)
Notation curry2' := (fun f a b => f (a ,& b)).

(***************)
(* Finite sets *)

Variant T0 := .
Variant T1 := t1_0.
Variant T2 := t2_0 | t2_1.
Variant T3 := t3_0 | t3_1 | t3_2.

Definition ex_falso {A : Type} (bot : T0) : A := match bot with end.

Definition voidᵢ {I : Type} : I -> Type := fun _ => T0.
Notation "∅ᵢ" := (voidᵢ).


(********************************)
(* Couple lemma on list/vec/fin *)

(*

Equations s_case {A B C : Type} (x : A + B) (f : A -> C) (g : B -> C) : C :=
  s_case (inl a) f g := f a ;
  s_case (inr b) f g := g b .

Equations f_split {a b} (i : fin (a + b)) : (fin a + fin b) :=
  @f_split O     _ i := inr i ;
  @f_split (S n) _ F0 := inl F0 ;
  @f_split (S n) _ (FS i) with f_split i := {
     | inl i := inl (FS i) ;
     | inr i := inr i } .

Equations f_split_list {X : Type} {xs ys : list X} (i : fin (length (xs ++ ys)))
           : fin (length xs) + fin (length ys) :=
  @f_split_list _ nil        _ i := inr i ;
  @f_split_list _ (cons _ _) _ F0     := inl F0 ;
  @f_split_list _ (cons _ _) _ (FS i) with f_split_list i := {
     | inl i := inl (FS i) ;
     | inr i := inr i } .
*)

Equations l_get {X} (xs : list X) : fin (length xs) -> X :=
  l_get (cons x xs) F0     := x ;
  l_get (cons x xs) (FS i) := l_get xs i.

Notation "xs .[ i ]" := (l_get xs i) (at level 10).

(*
Equations f_split_get {X} {xs ys : list X} i : (xs ++ ys) .[i] = s_case (f_split_list i) (l_get xs) (l_get ys) :=
  @f_split_get _ nil        _ i := eq_refl ;
  @f_split_get _ (cons _ _) _ F0     := eq_refl ;
  @f_split_get _ (cons _ _) _ (FS i) with f_split_list i := {
                                                             | inl i := _ ;
                                                          | inr i := _  } .
Obligation 2.
*)


Equations l_acc {X} (n : nat) (f : fin n -> X) : list X :=
  l_acc O     f := nil ;
  l_acc (S n) f := cons (f F0) (l_acc n (f ∘ FS)).

Equations len_acc {X} n (f : fin n -> X) : length (l_acc n f) = n :=
  len_acc O     f := eq_refl ;
  len_acc (S n) f := f_equal S (len_acc n (f ∘ FS)).

(*
Record list' (X : Type) : Type := List' { len : nat ; val : fin len -> X }.
Arguments len {X}.
Arguments val {X}.

Definition l_any {X : Type} (T : X -> Type) (xs : list' X) : Type :=
  { i : fin (len xs) & T (val xs i) }.

Definition l_all {X : Type} (T : X -> Type) (xs : list' X) : Type :=
  forall i : fin (len xs), T (val xs i).

Definition l_curry {X : Type} {T : X -> Type} (U : forall x, T x -> Type)
           {xs} (h : forall e : l_any T xs, U _ (projT2 e))
           : l_all (fun x -> forall t : T x, ) xs


*)


Equations dvec {X} (ty : X -> Type) (xs : list X) : Type :=
  dvec ty nil := T1 ;
  dvec ty (cons x xs) := ty x * dvec ty xs.
Transparent dvec.

Equations d_get {X ty} (c : list X) (d : dvec ty c) (i : fin (length c)) : ty (l_get c i) :=
  d_get (cons t ts) r F0     := fst r ;
  d_get (cons t ts) r (FS i) := d_get ts (snd r) i.

Equations d_concat {X ty} (a b : list X) (d : dvec ty a) (h : forall i : fin (length b), ty (b .[i])) : dvec ty (b ++ a) :=
  d_concat _ nil        d h := d ;
  d_concat _ (cons _ _) d h := (h F0 , d_concat _ _ d (fun i => h (FS i))).


Declare Scope indexed_scope.
Open Scope indexed_scope.
Delimit Scope indexed_scope with indexed.

Variant prod1 (D E : Type -> Type) : Type -> Type :=
| pair1 : forall {X Y}, D X -> E Y -> prod1 D E (X * Y).

#[global] Notation "D *' E" := (prod1 D E) (at level 50).

(* (covariant) presheaves *)
Definition psh (I : Type) : Type := I -> Type.

Definition eqᵢ {I : Type} {X : psh I} i (x y : X i) : Prop := x = y.

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
