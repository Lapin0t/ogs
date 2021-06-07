From OGS Require Import Utils EventD CatD.
From OGS Require Import ITreeD.

Definition itreeₐ {I} (E : event I I) i j X : Type := itree E (X @ j) i.

Section angelic.
Context {I : Type} {E : event I I}.

Definition tauₐ {X i j} (t : itreeₐ E i j X) : itreeₐ E i j X := tau t.
Definition retₐ {X i} (x : X) : itreeₐ E i i X := ret (pin _ x).
Definition visₐ {X i j} q (k : forall r, itreeₐ E _ j X) : itreeₐ E i j X := vis q k.

Definition bindₐ {X Y i j k} (x : itreeₐ E i j X) (f : X -> itreeₐ E j k Y)
                       : itreeₐ E i k Y :=
 x >>= fiber_into (itree _ _) f.

Notation "x !>= f" := (bindₐ x f) (at level 30).

Definition iterₐ {X Y i} (f : X -> itreeₐ E i i (X + Y)) : X -> itreeₐ E i i Y :=
  cofix _iter x := f x !>= fun r => match r with
                                 | inl x => tauₐ (_iter x)
                                 | inr y => retₐ y
                                 end.
End angelic.


Definition itree₀ (E : event₀) X : Type := itreeₐ E t1_0 t1_0 X.

Section triv_index.
  Context {E : event₀}.

  Definition tau₀ {X} (t : itree₀ E X) : itree₀ E X := tau t.
  Definition ret₀ {X} (x : X) : itree₀ E X := ret (pin _ x).
  Definition vis₀ {X} (q : qry₀ E) (k : forall r, itree₀ E X) : itree₀ E X :=
    vis q (fun r => match E.(nxt) q r with t1_0 => k r end).
End triv_index.
