From OGS Require Import Utils EventD ITreeD.
From Paco Require Import paco.
Require Import Program.Tactics Logic RelationClasses .
Import EqNotations.

Tactic Notation "hinduction" hyp(IND) "before" hyp(H)
  := move IND before H; revert_until IND; induction IND.


Section eqit.
  Context {I : Type} {E : event I I} {R1 R2 : I -> Type} (RR : forall i, R1 i -> R2 i -> Prop).

  Inductive eqitF (b1 b2: bool) (vclo : endo (forall i, itree E R1 i -> itree E R2 i -> Prop) ) (sim : forall i, itree E R1 i -> itree E R2 i -> Prop) i
    : itree' E R1 i -> itree' E R2 i -> Prop :=
    | EqRet r1 r2
       (REL: RR i r1 r2)
       : eqitF b1 b2 vclo sim i (RetF r1) (RetF r2)
    | EqTau m1 m2
        (REL: sim i m1 m2):
        eqitF b1 b2 vclo sim i (TauF m1) (TauF m2)
    | EqVis (e : E.(qry) i) k1 k2
        (REL: forall v, vclo sim _ (k1 v) (k2 v) : Prop):
        eqitF b1 b2 vclo sim i (VisF e k1) (VisF e k2)
    | EqTauL t1 ot2
        (CHECK: is_true b1)
        (REL: eqitF b1 b2 vclo sim i (observe t1) ot2):
        eqitF b1 b2 vclo sim i (TauF t1) ot2
    | EqTauR ot1 t2
        (CHECK: is_true b2)
        (REL: eqitF b1 b2 vclo sim i ot1 (observe t2)):
        eqitF b1 b2 vclo sim i ot1 (TauF t2).

  Hint Constructors eqitF: core.

  Definition eqit_ b1 b2 vclo sim i :
    itree E R1 i -> itree E R2 i -> Prop :=
    fun t1 t2 => eqitF b1 b2 vclo sim i (observe t1) (observe t2).
  Hint Unfold eqit_: core.

  Definition eqit b1 b2 : forall i, itree E R1 i -> itree E R2 i -> Prop :=
  paco3 (eqit_ b1 b2 id) bot3.

  Lemma eqitF_mono b1 b2 vclo vclo' sim sim' i x0 x1 
        (IN: eqitF b1 b2 vclo sim i x0 x1)
        (MON: monotone3 vclo)
        (LEc: vclo <4= vclo')
        (LE: sim <3= sim'):
    eqitF b1 b2 vclo' sim' i x0 x1. 
    induction IN; eauto.
  Qed.

  Lemma eqit__mono b1 b2 vclo (MON: monotone3 vclo) : monotone3 (eqit_ b1 b2 vclo).
    do 2 red. intros; eapply eqitF_mono; eauto.
  Qed.

  Lemma eqit_idclo_mono : monotone3 (@id (forall i, itree E R1 i -> itree E R2 i -> Prop)).
    unfold id. eauto. Qed.

  Hint Resolve eqit__mono : paco.
  Hint Resolve eqit_idclo_mono : paco.

  Definition eutt := eqit true true.
End eqit.

#[global] Hint Constructors eqitF: core.
#[global] Hint Unfold eqit_: core.
#[global] Hint Resolve eqit__mono : paco.
#[global] Hint Resolve eqit_idclo_mono : paco.
#[global] Hint Unfold eqit: core.
(*#[global] Hint Unfold eq_itree: core.*)
#[global] Hint Unfold eutt: core.
(*#[global] Hint Unfold euttge: core.*)
#[global] Hint Unfold id: core.
#[global] Infix "≈" := (eutt eqᵢ _) (at level 70) : type_scope.


Section eqit_trans.
  Context {I} {E : event I I} {R1 R2 : psh I} (RR : forall i, R1 i -> R2 i -> Prop).
  Inductive eqit_trans_clo b1 b2 b1' b2'
               (r : forall i, itree E R1 i -> itree E R2 i -> Prop) i
           : itree E R1 i -> itree E R2 i -> Prop :=
  | eqit_trans_clo_intro t1 t2 t1' t2' RR1 RR2
      (EQVl: eqit RR1 b1 b1' i t1 t1')
      (EQVr: eqit RR2 b2 b2' i t2 t2')
      (REL: r i t1' t2')
      (LERR1: forall i x x' y, RR1 i x x' -> RR i x' y -> RR i x y)
      (LERR2: forall i x y y', RR2 i y y' -> RR i x y' -> RR i x y)
  : eqit_trans_clo b1 b2 b1' b2' r i t1 t2
.
Hint Constructors eqit_trans_clo: core.

Definition eqitC b1 b2 := eqit_trans_clo b1 b2 false false.
Hint Unfold eqitC: core.

Lemma eqitC_mon b1 b2 r1 r2 i t1 t2
      (IN: eqitC b1 b2 r1 i t1 t2)
      (LE: r1 <3= r2):
  eqitC b1 b2 r2 i t1 t2.
  destruct IN; econstructor; eauto.
Qed.
Hint Resolve eqitC_mon : paco.

Lemma eq_inv_VisF_weak {R i} (e1 e2 : E.(qry) i)
      (k1 : forall r, itree E R _) (k2 : forall r, itree E R _)
  : VisF (R := R) e1 k1 = VisF (R := R) e2 k2 ->
    { p : e1 = e2 & rew [ fun _ => forall r, _ ] p in k1 = k2 }.
  intros.
  injection H as _ H1.
  inversion_sigma.
  eauto.
Qed.


Ltac unfold_eqit :=
  (try match goal with [|- eqit_ _ _ _ _ _ _ _ _ ] => red end);
  (repeat match goal with [H: eqit_ _ _ _ _ _ _ _ _ |- _ ] => red in H end).

Ltac inv H := inversion H; clear H; subst.

Ltac inv_Vis :=
  discriminate +
  match goal with
  | [ E : VisF _ _ = VisF _ _ |- _ ] =>
     apply eq_inv_VisF_weak in E; destruct E as [ <- <- ]
  end.


Lemma eqitC_wcompat b1 b2 vclo
      (MON: monotone3 vclo)
      (CMP: compose (eqitC b1 b2) vclo <4= compose vclo (eqitC b1 b2)):
  wcompatible3 (@eqit_ I E R1 R2 RR b1 b2 vclo) (eqitC b1 b2).
  econstructor. pmonauto.
  intros. destruct PR.
  punfold EQVl. punfold EQVr. unfold_eqit.
  hinduction REL before r; intros; clear t1' t2'.
  + remember (RetF r1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; eauto.
    remember (RetF r3) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; eauto.
  + remember (TauF m1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; eauto.
    remember (TauF m3) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; eauto.
    pclearbot. econstructor. gclo. econstructor; eauto with paco.
  + remember (VisF e k1) as x.
    hinduction EQVl before r; intros; try discriminate Heqx; eauto; inv_Vis.
    remember (VisF e k3) as y.
    hinduction EQVr before r; intros; try discriminate Heqy; eauto; inv_Vis.
    econstructor. intros. pclearbot.
    eapply MON.
    * apply CMP. econstructor; eauto.
    * intros. apply gpaco3_clo, PR.
  + remember (TauF t1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; eauto.
    pclearbot. punfold REL.
  + remember (TauF t2) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; eauto.
    pclearbot. punfold REL.
Qed.

Hint Resolve eqitC_wcompat : paco.

Lemma eqit_idclo_compat b1 b2: compose (eqitC b1 b2) id <4= compose id (eqitC b1 b2).
  intros. apply PR.
Qed.
Hint Resolve eqit_idclo_compat : paco.


Lemma eqitC_dist b1 b2:
  forall r1 r2, eqitC b1 b2 (r1 \3/ r2) <3= (eqitC b1 b2 r1 \3/ eqitC b1 b2 r2).
  intros. destruct PR. destruct REL; eauto.
Qed.

Hint Resolve eqitC_dist : paco.

Lemma eqit_clo_trans b1 b2 vclo
      (MON: monotone3 vclo)
      (CMP: compose (eqitC b1 b2) vclo <4= compose vclo (eqitC b1 b2)):
  eqit_trans_clo b1 b2 false false <4= gupaco3 (eqit_ RR b1 b2 vclo) (eqitC b1 b2).
  intros. destruct PR. gclo. econstructor; eauto with paco.
Qed.

End eqit_trans.
#[global] Hint Unfold eqitC: core.
#[global] Hint Resolve eqitC_mon : paco.
#[global] Hint Resolve eqitC_wcompat : paco.
#[global] Hint Resolve eqit_idclo_compat : paco.
#[global] Hint Resolve eqitC_dist : paco.
Arguments eqit_clo_trans : clear implicits.
#[global] Hint Constructors eqit_trans_clo: core.


Section eqit_gen.
Context {I} {E : event I I} {R: I -> Type} (RR : forall i, R i -> R i -> Prop).

Global Instance Reflexive_eqitF b1 b2 (sim : forall i, itree E R i -> itree E R i -> Prop)
: (forall i, Reflexive (RR i)) -> (forall i, Reflexive (sim i)) -> (forall i, Reflexive (eqitF RR b1 b2 id sim i)).
intros.
red. destruct x; constructor; eauto.
exact (H i r).
exact (H0 i t).
intro v. exact (H0 _ (k v)).
Qed.

Global Instance Symmetric_eqitF b (sim : forall i, itree E R i -> itree E R i -> Prop)
: (forall i, Symmetric (RR i)) -> (forall i, Symmetric (sim i)) -> (forall i, Symmetric (eqitF RR b b id sim i)).
  red. induction 3; constructor; subst; eauto.
  exact (H i _ _ REL).
  exact (H0 i _ _ REL).
  intro v. exact (H0 _ _ _ (REL v)).
Qed.

Global Instance Reflexive_eqit_ b1 b2 (sim : forall i, itree E R i -> itree E R i -> Prop)
: (forall i, Reflexive (RR i)) -> (forall i, Reflexive (sim i)) -> (forall i, Reflexive (eqit_ RR b1 b2 id sim i)).
repeat red. intros. reflexivity. Qed.

Global Instance Symmetric_eqit_ b (sim : forall i, itree E R i -> itree E R i -> Prop)
: (forall i, Symmetric (RR i)) -> (forall i, Symmetric (sim i)) -> (forall i, Symmetric (eqit_ RR b b id sim i)).
repeat red; symmetry; auto. Qed.

(* FAILLING HERE *)
(*
Global Instance Reflexive_eqit_gen b1 b2 (r rg: forall i, itree E R i -> itree E R i -> Prop) :
  (forall i, Reflexive (RR i)) -> (forall i, Reflexive (gpaco3 (eqit_ RR b1 b2 id) (eqitC RR b1 b2) r rg i)).
  pcofix CIH. gstep; intros.
  repeat red. destruct (observe x); eauto with paco.
  reflexivity.
Qed.

Global Instance Reflexive_eqit b1 b2 : Reflexive RR -> Reflexive (@eqit E _ _ RR b1 b2).
Proof.
  red; intros. ginit. apply Reflexive_eqit_gen; eauto.
Qed.

Global Instance Symmetric_eqit b : Symmetric RR -> Symmetric (@eqit E _ _ RR b b).
Proof.
  red; intros. apply eqit_flip.
  eapply eqit_mon, H0; eauto.
Qed.

Global Instance eq_sub_euttge:
  subrelation (@eq_itree E _ _ RR) (euttge RR).
Proof.
  ginit. pcofix CIH. intros.
  punfold H0. gstep. red in H0 |- *.
  hinduction H0 before CIH; subst; econstructor; try inv CHECK; pclearbot; eauto 7 with paco.
Qed.

Global Instance euttge_sub_eutt:
  subrelation (@euttge E _ _ RR) (eutt RR).
Proof.
  ginit. pcofix CIH. intros.
  punfold H0. gstep. red in H0 |- *.
  hinduction H0 before CIH; subst; econstructor; pclearbot; eauto 7 with paco.
Qed.

Global Instance eq_sub_eutt:
  subrelation (@eq_itree E _ _ RR) (eutt RR).
Proof.
  red; intros. eapply euttge_sub_eutt. eapply eq_sub_euttge. apply H.
Qed.

End eqit_gen.

*)

End eqit_gen.

