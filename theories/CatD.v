Set Implicit Arguments.
Set Strict Implicit.
Set Universe Polymorphism.

From OGS Require Import Utils.

Class Functor {I} (f : psh I -> psh I) : Type := {
  fmap {x y : psh I} : x ⇒ᵢ y -> f x ⇒ᵢ f y 
}.

Notation "f <$> x" := (fmap f _ x) (at level 30).

Class Monad {I} (m : psh I -> psh I) : Type := {
  ret {x : psh I} : x ⇒ᵢ m x ;
  sub {x y : psh I} : (x ⇒ᵢ m y) -> m x ⇒ᵢ m y
}.

Definition mcompose {I} {m : psh I -> psh I} {M : Monad m}
             {x y z : psh I} (f : x ⇒ᵢ m y) (g: y ⇒ᵢ m z) : (x ⇒ᵢ m z) :=
    fun _ x => sub g _ (f _ x).

Notation "x >>= f" := (sub f _ x) (at level 30).
Notation "f =<< x" := (sub f _ x) (at level 30).
Notation "f >=> g" := (mcompose f g) (at level 30).


Class MonadIter {I : Type} (m : psh I -> psh I) : Type := {
  iter {x y : psh I} : x ⇒ᵢ m (x +ᵢ y) -> x ⇒ᵢ m y
}.
