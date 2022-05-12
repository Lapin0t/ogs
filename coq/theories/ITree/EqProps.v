Set Primitive Projections.

From Coq Require Import RelationClasses Morphisms.
From Paco Require Import paco.
From Equations Require Import Equations.

From OGS Require Import Utils.
From OGS.ITree Require Import Cat Event ITree Eq Rec Angelic.

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

Section observing_relations.
  Context {I} {E : event I I} {X : psh I}.
  Context (R : relᵢ (itree' E X) (itree' E X)).
 
  #[global]
  Instance observing_observe_ i :
    Proper (observing R i ==> R i) (@observe I E X i).
  Proof. intros ? ? []; cbv; auto. Qed.

  #[global]
  Instance observing_go i : Proper (R i ==> observing R i) (@go I E X i).
  Proof. cbv; auto. Qed.

  #[global]
  Instance monotonic_observing (R' : relᵢ (itree' E X) (itree' E X)) :
  subrelᵢ R R' ->
  subrelᵢ (observing R) (observing R').
  Proof. intros ? ? ? ? [o]; econstructor; apply H; exact o. Qed.

  (*
  Instance equivalence_observing :
    Equivalence R' -> Equivalence (observing eq_).
Proof with (auto with itree).
  intros []; split; cbv...
  - intros ? ? []; auto...
  - intros ? ? ? [] []; eauto with itree.
Qed.
*)
End observing_relations.


Definition subst_ {I} {E : event I I} {X Y : I -> Type}
           (f : X ⇒ᵢ itree E Y) : itree E X ⇒ᵢ itree E Y
  := fun i x => match (observe x) with
             | RetF r => f _ r
             | TauF t => Tau (subst f t)
             | VisF e k => Vis e (fun r => subst f (k r))
             end.
Require Import OGS.Utils.Psh.

Lemma unfold_subst {I} {E : event I I} {X Y : I -> Type}
           (f : X ⇒ᵢ itree E Y) {i} (x : itree E X i)
           : eq_itree eqᵢ _ (subst f x) (subst_ f _ x).
  pstep; cbv [eqit_ subst subst_ observe]; destruct (_observe x); reflexivity.
Qed.

Definition iter_ {I} {E : event I I} {X Y : I -> Type} (f : X ⇒ᵢ itree E (X +ᵢ Y)) :=
  fun i x => bind (f i x) (fun i y => match y with
                                | inl x => Tau (iter f i x)
                                | inr y => Ret y
                                end).

Lemma unfold_iter {I} {E : event I I} {X Y : I -> Type}
           (f : X ⇒ᵢ itree E (X +ᵢ Y)) {i} (x : X i) 
           : eq_itree eqᵢ _ (iter f i x) (iter_ f i x).
  pstep; cbv [eqit_ iter iter_ observe]; reflexivity.
Qed.

Definition iterₐ_ {I} {E : event I I} {X Y i} (f : X -> itreeₐ E i i (X + Y)) x :=
  f x !>= fun r => match r with
                | inl x => tauₐ (iterₐ f x)
                | inr y => retₐ y
                end.

Lemma unfold_iterₐ {I} {E : event I I} {X Y i}
           (f : X -> itreeₐ E i i (X + Y)) (x : X)
  : eq_itree eqᵢ _ (iterₐ f x) (iterₐ_ f x).
  pstep; cbv [eqit_ iterₐ iterₐ_ observe]; reflexivity.
Qed.
