Set Implicit Arguments.
Set Strict Implicit.
Set Universe Polymorphism.

From OGS Require Import Utils.

Class Functor {I : Type} (f : psh I -> psh I) : Type := {
  fmap {x y : psh I} : iarrow x y -> iarrow (f x) (f y) 
}.

Class Monad {I : Type} (m : psh I -> psh I) : Type := {
  ret {x : psh I} : x ==> m x ;
  sub {x y : psh I} : (x ==> m y) -> m x ==> m y
}.

Class MonadIter {I : Type} (m : psh I -> psh I) : Type := {
  iter {x y : psh I} : (x ==> m (x +i y)) -> x ==> m y
}.
