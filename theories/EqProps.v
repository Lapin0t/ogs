Set Primitive Projections.
From Equations Require Import Equations.

From Paco Require Import paco.
From OGS Require Import Utils Ctx EventD CatD ITreeD EqD RecD AngelicD.

Record observing {I} {E : event I I} {X Y : psh I}
           (R : forall i, itree' E X i -> itree' E Y i -> Prop)
           i (t1 : itree E X i) (t2 : itree E Y i) : Prop :=
  observing_intros
  { observing_observe : R _ (observe t1) (observe t2) }.
Global Hint Constructors observing: core.


Lemma unfold_iter {I} {E : event I I} {X Y : I -> Type}
           (f : X ⇒ᵢ itree E (X +ᵢ Y)) {i} (x : X i) 
           : observing eqᵢ _
              (iter f i x)
              (bind (f i x) (fun i y => match y with
                                        | inl x => Tau (iter f i x)
                                        | inr y => Ret y
                                        end)).
constructor; reflexivity.
Qed.

Lemma unfold_iterₐ {I} {E : event I I} {X Y i}
           (f : X -> itreeₐ E i i (X + Y)) (x : X)
  : observing eqᵢ _
      (iterₐ f x)
      (f x !>= fun r => match r with
                     | inl x => tauₐ (iterₐ f x)
                     | inr y => retₐ y
                     end).
constructor; reflexivity.
Qed.
