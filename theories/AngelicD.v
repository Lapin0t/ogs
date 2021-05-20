From OGS Require Import Utils EventD.
From OGS Require ITreeD.

Section angelic.
Context {I : Type}.

Definition itree (E : event I) i j X : Type := ITreeD.itree E (X @ j) i.

Definition tau {E : event I} {X i j} (t : itree E i j X) : itree E i j X :=
  ITreeD.tau t.
Definition ret {E : event I} {X i} (x : X) : itree E i i X := ITreeD.ret (pin _ x).
Definition vis {E : event I} {X i j} q (k : forall r, itree E _ j X) : itree E i j X :=
  ITreeD.vis q k.

(* McBride's "angelic" bind: we know the states i, j, k we are in *)
Definition bind {E : event I} {X Y i j k}
            : itree E i j X -> (X -> itree E j k Y) -> itree E i k Y :=
 fun x f => ITreeD.bind x (fiber_into (ITreeD.itree E (Y @ _)) f).

Definition iter {E : event I} {X Y : Type} {i}
           (body : X -> itree E i i (X + Y)) : X -> itree E i i Y :=
  cofix _iter x := bind (body x) (fun r => match r with
                                 | inl x => tau (_iter x)
                                 | inr y => ret y
                                 end).
End angelic.
