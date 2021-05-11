From OGS Require Import Utils EventD ITreeD.
From Paco Require Import paco.
Require Import Program.Tactics.

Tactic Notation "hinduction" hyp(IND) "before" hyp(H)
  := move IND before H; revert_until IND; induction IND.


Section eqit.
  Context {I : Type} {E : event I} {R1 R2 : I -> Type} (RR : forall i, R1 i -> R2 i -> Prop).

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
  Check eutt.
  Infix "≈" := (eutt eq) (at level 70) : type_scope.
End eqit.

Global Hint Constructors eqitF: core.
Global Hint Unfold eqit_: core.
Global Hint Resolve eqit__mono : paco.
Global Hint Resolve eqit_idclo_mono : paco.
Global Hint Unfold eqit: core.
(*Global Hint Unfold eq_itree: core.*)
Global Hint Unfold eutt: core.
(*Global Hint Unfold euttge: core.*)
Global Hint Unfold id: core.


Section eqit_trans.
   Context {I} {E : event I} {R1 R2 : psh I} (RR : forall i, R1 i -> R2 i -> Prop).
  Inductive eqit_trans_clo b1 b2 b1' b2'
               (r : forall i, itree E R1 i -> itree E R2 i -> Prop) i
           : itree E R1 i -> itree E R2 i -> Prop :=
  | eqit_trans_clo_intro t1 t2 t1' t2' RR1 RR2
      (EQVl: eqit RR1 b1 b1' i t1 t1')
      (EQVr: eqit RR2 b2 b2' i t2 t2')
      (REL: r i t1' t2')
      (LERR1: forall x x' y, RR1 i x x' -> RR i x' y -> RR i x y)
      (LERR2: forall x y y', RR2 i y y' -> RR i x y' -> RR i x y)
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

Lemma eq_inv_VisF_weak {E R X1 X2} (e1 : E X1) (e2 : E X2) (k1 : X1 -> itree E R) (k2 : X2 -> itree E R)
  : VisF (R := R) e1 k1 = VisF (R := R) e2 k2 ->
    exists p : X1 = X2, eqeq E p e1 e2 /\ eqeq (fun X => X -> itree E R) p k1 k2.
Proof.
  refine (fun H =>
    match H in _ = t return
      match t with
      | VisF e2 k2 => _
      | _ => True
      end
    with
    | eq_refl => _
    end); cbn.
  exists eq_refl; cbn; auto.
Qed.

Ltac unfold_eqit :=
  (try match goal with [|- eqit_ _ _ _ _ _ _ _ _ ] => red end);
  (repeat match goal with [H: eqit_ _ _ _ _ _ _ _ _ |- _ ] => red in H end).

Ltac inv H := inversion H; clear H; subst.
Ltac inv_Vis :=
  discriminate +
  match goal with
  | [ E : VisF _ _ = VisF _ _ |- _ ] =>
     apply eq_inv_VisF_weak in E; destruct E as [ <- [ <- <- ]]
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
