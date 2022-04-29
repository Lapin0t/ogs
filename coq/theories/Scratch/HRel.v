From Coq Require Import
     Morphisms
     Setoid
     Relation_Definitions
     RelationClasses.

From OGS Require Import Utils.

Definition relH {I} (A B : psh I) := forall i, A i -> B i -> Prop.

Section relH_ops.
  Definition rel_compose {I} {A B C : psh I} (S : relH B C) (R : relH A B)
             : relH A C :=
    fun i x y => exists b, R i x b /\ S i b y.

  Definition rel_transpose {I} {A B : psh I} (R : relH A B) : relH B A :=
    fun i x y => R i y x.

  Definition sub_rel {I} {A B : psh I} (R S : relH A B) :=
    forall i x y, R i x y -> S i x y.

  Definition eq_rel {I} {A B : psh I} (R S : relH A B) :=
    sub_rel R S /\ sub_rel S R.
