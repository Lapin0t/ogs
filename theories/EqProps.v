Set Primitive Projections.
From Equations Require Import Equations.

From Paco Require Import paco.
From OGS Require Import Utils Ctx EventD CatD ITreeD EqD RecD AngelicD.
From Coq Require Import RelationClasses.

Record observing {I} {E : event I I} {X Y : psh I}
           (R : relᵢ (itree' E X) (itree' E Y))
           i (t1 : itree E X i) (t2 : itree E Y i) : Prop :=
  observing_intros
  { observing_observe : R _ (observe t1) (observe t2) }.
Check observing_observe.
Arguments observing_observe {I E X Y R i t1 t2}.
Global Hint Constructors observing: core.

Definition observing_sub_eqit {I} {E : event I I} {X : psh I}
           (R : relᵢ X X) (RR : Reflexiveᵢ R) b0 b1
           : subrelᵢ (observing eqᵢ) (@eqit I E _ _ R b0 b1).
  repeat red; intros.
  pstep. red. rewrite (observing_observe H).
  apply Reflexive_eqitF; eauto. 
  left; apply reflexivity.
  Qed. 

Definition subst_ {I} {E : event I I} {X Y : I -> Type}
           (f : X ⇒ᵢ itree E Y) : itree E X ⇒ᵢ itree E Y
  := fun i x => match (observe x) with
             | RetF r => f _ r
             | TauF t => Tau (subst f t)
             | VisF e k => Vis e (fun r => subst f (k r))
             end.

Lemma unfold_subst {I} {E : event I I} {X Y : I -> Type}
           (f : X ⇒ᵢ itree E Y) {i} (x : itree E X i)
           : observing eqᵢ _ (subst f x) (subst_ f _ x).
  constructor; reflexivity.
Qed.

Definition iter_ {I} {E : event I I} {X Y : I -> Type} (f : X ⇒ᵢ itree E (X +ᵢ Y)) :=
  fun i x => bind (f i x) (fun i y => match y with
                                | inl x => Tau (iter f i x)
                                | inr y => Ret y
                                end).

Lemma unfold_iter {I} {E : event I I} {X Y : I -> Type}
           (f : X ⇒ᵢ itree E (X +ᵢ Y)) {i} (x : X i) 
           : observing eqᵢ _ (iter f i x) (iter_ f i x).
constructor; reflexivity.
Qed.

Definition iterₐ_ {I} {E : event I I} {X Y i} (f : X -> itreeₐ E i i (X + Y)) x :=
  f x !>= fun r => match r with
                | inl x => tauₐ (iterₐ f x)
                | inr y => retₐ y
                end.

Lemma unfold_iterₐ {I} {E : event I I} {X Y i}
           (f : X -> itreeₐ E i i (X + Y)) (x : X)
  : observing eqᵢ _ (iterₐ f x) (iterₐ_ f x).
constructor; reflexivity.
Qed.
