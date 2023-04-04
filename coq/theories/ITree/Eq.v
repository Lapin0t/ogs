Require Import Coq.Program.Equality.
From Coinduction Require Import lattice rel coinduction tactics.

From OGS Require Import Utils.
From OGS.Utils Require Import Rel.
From OGS.Game Require Import Event.
From OGS.ITree Require Import ITree.

(*|
Silent step "eating" relation: "it_eat X Y" := "X = Tau^n(Y) for some n".
Could be generalized to any itreeF coalgebra if needed.
|*)
Section it_eat.
  Context {I : Type} {E : event I I} {R : psh I}.

  Inductive it_eat i : itree' E R i -> itree' E R i -> Prop :=
    | EatRefl {t} : it_eat i t t
    | EatStep {t1 t2} : it_eat _ (observe t1) t2 -> it_eat i (TauF t1) t2
  .
  Hint Constructors it_eat : core.
  Arguments EatRefl {i t}.
  Arguments EatStep {i t1 t2} p.

  #[global] Instance eat_trans : Transitiveᵢ it_eat.
  intros i x y z r1 r2; dependent induction r1; auto.
  Defined.

  Equations eat_cmp : (revᵢ it_eat ⨟ it_eat) <= (it_eat ∨ᵢ revᵢ it_eat) :=
    eat_cmp i' x' y' (ex_intro _ z' (conj p' q')) := _eat_cmp p' q'
  where _eat_cmp {i x y z} : it_eat i x y -> it_eat i x z -> (it_eat i y z \/ it_eat i z y) :=
    _eat_cmp (EatRefl)   q           := or_introl q ;
    _eat_cmp p           (EatRefl)   := or_intror p ;
    _eat_cmp (EatStep p) (EatStep q) := _eat_cmp p q .

End it_eat.

#[global] Hint Constructors it_eat : core.
#[global] Arguments EatRefl {I E R i t}.
#[global] Arguments EatStep {I E R i t1 t2} p.

(*|
Strong bisimilarity aka coinductive equality
|*)
Variant it_eqF {I} E {R1 R2 Y1 Y2} (RR : relᵢ R1 R2) (RY : relᵢ Y1 Y2) (i : I)
        : itreeF E R1 Y1 i -> itreeF E R2 Y2 i -> Prop :=
  | EqRet {r1 r2} (r_rel : RR i r1 r2)                : it_eqF _ _ _ _ (RetF r1)   (RetF r2)
  | EqTau {t1 t2} (t_rel : RY i t1 t2)                : it_eqF _ _ _ _ (TauF t1)   (TauF t2)
  | EqVis {q k1 k2} (k_rel : forall r, RY _ (k1 r) (k2 r)) : it_eqF _ _ _ _ (VisF q k1) (VisF q k2)
.
#[global] Hint Constructors it_eqF : core.
#[global] Arguments EqRet {I E R1 R2 Y1 Y2 RR RY i r1 r2}.
#[global] Arguments EqTau {I E R1 R2 Y1 Y2 RR RY i t1 t2}.
#[global] Arguments EqVis {I E R1 R2 Y1 Y2 RR RY i q k1 k2}.

Equations it_eqF_mon {I E X1 X2 Y1 Y2} : Proper (leq ==> leq ==> leq) (@it_eqF I E X1 X2 Y1 Y2) :=
  it_eqF_mon _ _ H0 _ _ H1 _ _ _ (EqRet r_rel) := EqRet (H0 _ _ _ r_rel) ;
  it_eqF_mon _ _ H0 _ _ H1 _ _ _ (EqTau t_rel) := EqTau (H1 _ _ _ t_rel) ;
  it_eqF_mon _ _ H0 _ _ H1 _ _ _ (EqVis k_rel) := EqVis (fun r => H1 _ _ _ (k_rel r)) .
#[global] Existing Instance it_eqF_mon.

Definition it_eq_map {I} E {X1 X2} (R : relᵢ X1 X2) : mon (relᵢ (@itree I E X1) (@itree I E X2)) := {|
  body RY i x y := it_eqF E R RY i (observe x) (observe y) ;
  Hbody _ _ H _ _ _ r := it_eqF_mon _ _ (fun _ _ _ p => p) _ _ H _ _ _ r ;
|}.

Definition it_eq {I} E {X1 X2} R := gfp (@it_eq_map I E X1 X2 R).
Notation it_eq_t E R := (t (@it_eq_map _ E _ _ R)).
Notation it_eq_bt E R := (bt (@it_eq_map _ E _ _ R)).
Notation it_eq_T E R := (T (@it_eq_map _ E _ _ R)).

Section it_eq_facts.
  Context {I} {E : event I I}.
  Context {X1 X2 : psh I}.
  Context {}

  #[global] Instance it_eq_mon {X1 X2} : Proper (leq ==> leq) (@it_eq I E X1 X2).
  Proof.
    intros R1 R2 H; apply coinduction; intros ? ? ? ?.
    eapply (it_eqF_mon R1 R2 H).
    now apply id_t.
    now apply (gfp_fp (it_eq_map _ _)).
  Qed.

(*|
Reversal, symmetry.
|*)
  Lemma it_eqF_rev {X1 X2 RX Y1 Y2 RY} : revᵢ (@it_eqF I E X1 X2 Y1 Y2 RX RY) <= it_eqF E (revᵢ RX) (revᵢ RY).
  Proof. intros ? ? ? p; dependent elimination p; auto. Qed.

  Lemma it_eqF_rev' {X1 X2 RX Y1 Y2 RY} : it_eqF E (revᵢ RX) (revᵢ RY) <= revᵢ (@it_eqF I E X1 X2 Y1 Y2 RX RY).
  Proof. intros ? ? ? p; dependent elimination p; auto. Qed.

Lemma it_eq_rev {I E X1 X2} : revᵢ ∘ @it_eq I E X1 X2 <= @it_eq I E X2 X1 ∘ revᵢ.
  intros ?; apply coinduction; intros ? ? ? CIH.
  eapply it_eqF_mon.
  - intros ? ? ? r; exact r.
  - apply id_t.
  - apply it_eqF_rev, (gfp_fp (it_eq_map _ _)); auto.
Qed.

Lemma it_eq_t_sym {I E} {X : psh I} {R : relᵢ X X} (H : Symmetricᵢ R)
      : converseᵢ <= it_eq_t E R.
Proof.
  apply leq_t; intros ? ? ? ? p.
  now apply it_eqF_rev, (it_eqF_mon _ _ H _ _ (fun _ _ _ r => r)).
Qed.

#[global] Instance it_eq_sym {I E X R} (H : Symmetricᵢ R) : Symmetricᵢ (@it_eq I E X X R).
Proof. intros ? ? ? ?; now apply it_eq_rev, (it_eq_mon _ _ H). Qed.

(*|
Reflexivity
|*)
#[global] Instance it_eqF_refl {I E X Y RX RY} (HX : Reflexiveᵢ RX) (HY : Reflexiveᵢ RY)
                   : Reflexiveᵢ (@it_eqF I E X X Y Y RX RY).
Proof. intros ? []; econstructor; reflexivity. Qed.

Lemma it_eq_t_refl {I E} {X : psh I} {R : relᵢ X X} {H : Reflexiveᵢ R} : const (eqᵢ _) <= @it_eq_t E R.
Proof. apply leq_t; intros ? ? ? ? <-; now apply it_eqF_refl. Qed.

#[global] Instance it_eq_refl {I E X R} (H : Reflexiveᵢ R) : Reflexiveᵢ (@it_eq I E X X R).
Proof. apply build_reflexive, it_eq_t_refl. Qed.

(*|
Concatenation, transitivity.
|*)
Equations it_eqF_seq {I E X1 X2 X3 RX1 RX2 RX3} (HX : (RX1 ⨟ RX2) <= RX3) {Y1 Y2 Y3 RY1 RY2}
      : (@it_eqF I E X1 X2 Y1 Y2 RX1 RY1 ⨟ @it_eqF I E X2 X3 Y2 Y3 RX2 RY2) <= it_eqF E RX3 (RY1 ⨟ RY2) :=
  it_eqF_seq HX _ _ _ (EqRet r_rel1 ⨟⨟ EqRet r_rel2) := EqRet (HX _ _ _ (r_rel1 ⨟⨟ r_rel2)) ;
  it_eqF_seq HX _ _ _ (EqTau t_rel1 ⨟⨟ EqTau t_rel2) := EqTau (t_rel1 ⨟⨟ t_rel2) ;
  it_eqF_seq HX _ _ _ (EqVis k_rel1 ⨟⨟ EqVis k_rel2) := EqVis (fun v => k_rel1 v ⨟⨟ k_rel2 v) .

Lemma it_eq_seq {I} {E : event I I} {X1 X2 X3} {RX1 : relᵢ X1 X2} {RX2 : relᵢ X2 X3} {RX3}
                (HX : (RX1 ⨟ RX2) <= RX3) : (it_eq E RX1 ⨟ it_eq E RX2) <= it_eq E RX3.
Proof.
  apply coinduction; intros ? ? ? [ ? [ u v ] ].
  eapply it_eqF_mon.
  - intros ? ? ? r; exact r.
  - apply id_t.
  - apply (it_eqF_seq HX).
    refine (_ ⨟⨟ _); apply (gfp_fp (it_eq_map _ _)); [ exact u | exact v ].
Qed.

Lemma it_eq_t_trans {I E} {X : psh I} {R : relᵢ X X} {H : Transitiveᵢ R}
      : squareᵢ <= @it_eq_t E R.
Proof.
  apply leq_t; intros ? ? ? ? [ ? [ u v ] ]; cbn.
  exact (it_eqF_seq (use_transitive H) _ _ _ (u ⨟⨟ v)).
Qed.

#[global] Instance it_eq_trans {I E X R} (H : Transitiveᵢ R) : Transitiveᵢ (@it_eq I E X X R).
Proof. now apply build_transitive, it_eq_seq, use_transitive. Qed.

Section wbisim.
  Context {I : Type} (E : event I I).
  Context {R1 R2 : I -> Type} (RR : relᵢ R1 R2).

  Variant it_wbisimF RY i (t1 : itree' E R1 i) (t2 : itree' E R2 i) : Prop :=
    | WBisim {x1 x2} (r1 : it_eat i t1 x1) (r2 : it_eat i t2 x2) (rr : it_eqF E RR RY i x1 x2) .
  Arguments WBisim {RY i t1 t2 x1 x2}.

  Definition it_wbisim_map : mon (relᵢ (itree E R1) (itree E R2)) := {|
    body RY i x y := it_wbisimF RY i (observe x) (observe y) ;
    Hbody _ _ H _ _ _ '(WBisim r1 r2 rr) := WBisim r1 r2 (it_eqF_mon _ _ (fun _ _ _ r => r) _ _ H _ _ _ rr) ;
  |}.

  Definition it_wbisim := gfp it_wbisim_map.
  Definition it_wbisim' := it_wbisimF it_wbisim.

End wbisim.
#[global] Notation it_wbisim_t E R := (t (@it_wbisim_map _ E _ _ R)).
#[global] Notation it_wbisim_bt E R := (bt (@it_wbisim_map _ E _ _ R)).
#[global] Notation it_wbisim_T E R := (T (@it_wbisim_map _ E _ _ R)).

#[global] Arguments WBisim {I E R1 R2 RR RY i t1 t2 x1 x2}.
#[global] Hint Constructors it_wbisimF : core.

Section wbisim_facts1.
  Context {I : Type} {E : event I I}.
  Context {R1 R2 : psh I} {RR : relᵢ R1 R2}.

(*|
Reversal, symmetry.
|*)
  Lemma it_wbisimF_rev {RY} : revᵢ (it_wbisimF E RR RY) <= it_wbisimF E (revᵢ RR) (revᵢ RY).
  Proof. intros ? ? ? [ ? ? ? ? rr ]; apply it_eqF_rev in rr; eauto. Qed.

  Lemma it_wbisim_rev : revᵢ (it_wbisim E RR) <= it_wbisim E (revᵢ RR).
  Proof.
    apply coinduction; intros ? ? ? u.
    eapply (Hbody (it_wbisim_map _ _)).
    - apply id_t.
    - apply it_wbisimF_rev.
      apply (gfp_fp (it_wbisim_map E RR)); auto.
  Qed.

  Lemma it_wbisim_t_sym (H : Symmetricᵢ RR) : converseᵢ <= it_wbisim_t E RR.

  Equations wbisim_step_l {i x y} : it_wbisim' E RR i x (TauF y) -> it_wbisim' E RR i x (observe y) :=
    wbisim_step_l (WBisim p (EatRefl) (EqTau r))
      with proj1 (gfp_fp (it_wbisim_map E RR) _ _ _) r :=
      { | WBisim w1 w2 s := WBisim (eat_trans _ _ _ _ p (EatStep w1)) w2 s } ;
    wbisim_step_l (WBisim p (EatStep q) v) := WBisim p q v .

  Equations wbisim_step_r {i x y} : it_wbisim' E RR i (TauF x) y -> it_wbisim' E RR i (observe x) y :=
    wbisim_step_r (WBisim (EatRefl) q (EqTau r))
      with proj1 (gfp_fp (it_wbisim_map E RR) _ _ _) r :=
      { | WBisim w1 w2 s := WBisim w1 (eat_trans _ _ _ _ q (EatStep w2)) s } ;
    wbisim_step_r (WBisim (EatStep p) q v) := WBisim p q v .

  Equations? wbisim_tau_up_r {i x y z} : it_eat i x (TauF y) -> it_eqF E RR (it_wbisim E RR) i (TauF y) z
                                    -> it_eqF E RR (it_wbisim E RR) i x z :=
    wbisim_tau_up_r (EatRefl)   q         := q ;
    wbisim_tau_up_r (EatStep p) (EqTau q) := EqTau _ .

  apply (gfp_fp (it_wbisim_map E RR)) in q; destruct q as [ ? ? r1 r2 rr ].
  apply (gfp_fp (it_wbisim_map E RR)).
  refine (WBisim _ r2 rr); eapply eat_trans; [ exact p | exact (EatStep r1) ].
  Defined.

  Equations? wbisim_tau_up_l {i x y z} : it_eqF E RR (it_wbisim E RR) i x (TauF y) -> it_eat i z (TauF y)
                                    -> it_eqF E RR (it_wbisim E RR) i x z :=
    wbisim_tau_up_l p         (EatRefl)   := p ;
    wbisim_tau_up_l (EqTau p) (EatStep q) := EqTau _ .

  apply (gfp_fp (it_wbisim_map E RR)) in p; destruct p as [ ? ? r1 r2 rr ].
  apply (gfp_fp (it_wbisim_map E RR)).
  refine (WBisim r1 _ rr); eapply eat_trans; [ exact q | exact (EatStep r2) ].
  Defined.

  Equations wbisim_ret_down_l {i x y r} : it_wbisim' E RR i x y -> it_eat i y (RetF r)
                                      -> (it_eat ⨟ it_eqF E RR (it_wbisim E RR)) i x (RetF r) :=
    wbisim_ret_down_l (WBisim p (EatRefl) w) (EatRefl)   := p ⨟⨟ w ;
    wbisim_ret_down_l w                      (EatStep q) := wbisim_ret_down_l (wbisim_step_l w) q .

  Equations wbisim_ret_down_r {i x y r} : it_eat i x (RetF r) -> it_wbisim' E RR i x y
                                      -> (it_eqF E RR (it_wbisim E RR) ⨟ revᵢ it_eat) i (RetF r) y :=
    wbisim_ret_down_r (EatRefl)   (WBisim (EatRefl) q w) := w ⨟⨟ q ;
    wbisim_ret_down_r (EatStep p) w                      := wbisim_ret_down_r p (wbisim_step_r w) .

  Equations wbisim_vis_down_l {i x y e k} : it_wbisim' E RR i x y -> it_eat i y (VisF e k)
                                        -> (it_eat ⨟ it_eqF E RR (it_wbisim E RR)) i x (VisF e k) :=
    wbisim_vis_down_l (WBisim p (EatRefl) w) (EatRefl)   := p ⨟⨟ w ;
    wbisim_vis_down_l w                      (EatStep q) := wbisim_vis_down_l (wbisim_step_l w) q .

  Equations wbisim_vis_down_r {i x y e k} : it_eat i x (VisF e k) -> it_wbisim' E RR i x y
                                      -> (it_eqF E RR (it_wbisim E RR) ⨟ revᵢ it_eat) i (VisF e k) y :=
    wbisim_vis_down_r (EatRefl)   (WBisim (EatRefl) q w) := w ⨟⨟ q ;
    wbisim_vis_down_r (EatStep p) w                      := wbisim_vis_down_r p (wbisim_step_r w) .

End wbisim_facts1.

(*|
Concatenation, transitivity.
|*)
Lemma it_wbisimF_seq {I E X1 X2 X3 RX1 RX2 RX3} (HX : (RX1 ⨟ RX2) <= RX3)
      : (@it_wbisim' I E X1 X2 RX1 ⨟ @it_wbisim' I E X2 X3 RX2)
       <= it_wbisimF E RX3 (it_wbisim E RX1 ⨟ it_wbisim E RX2).
  intros i x y [z [[x1 x2 u1 u2 uS] [y1 y2 v1 v2 vS]]].
  destruct (eat_cmp _ _ _ (u2 ⨟⨟ v1)) as [w | w]; clear z u2 v1.
  - destruct y1.
    + destruct (wbisim_ret_down_l (WBisim u1 EatRefl uS) w) as [z [w1 ww]]; clear u1 uS w.
      dependent destruction vS; dependent destruction ww.
      exact (WBisim w1 v2 (EqRet (HX _ _ _ (r_rel0 ⨟⨟ r_rel)))).
    + exact (WBisim u1 v2 (it_eqF_seq HX _ _ _ (uS ⨟⨟ wbisim_tau_up_r w vS))).
    + destruct (wbisim_vis_down_l (WBisim u1 EatRefl uS) w) as [z [w1 ww]]; clear u1 uS w.
      dependent destruction vS; dependent destruction ww.
      exact (WBisim w1 v2 (EqVis (fun r => k_rel0 r ⨟⨟ k_rel r))).
  - destruct x2.
    + destruct (wbisim_ret_down_r w (WBisim EatRefl v2 vS)) as [z [ww w1]]; clear v2 vS w.
      dependent destruction uS; dependent destruction ww.
      exact (WBisim u1 w1 (EqRet (HX _ _ _ (r_rel ⨟⨟ r_rel0)))).
    + exact (WBisim u1 v2 (it_eqF_seq HX _ _ _ (wbisim_tau_up_l uS w ⨟⨟ vS))).
    + destruct (wbisim_vis_down_r w (WBisim EatRefl v2 vS)) as [z [ww w1]]; clear v2 vS w.
      dependent destruction uS; dependent destruction ww.
      exact (WBisim u1 w1 (EqVis (fun r => k_rel r ⨟⨟ k_rel0 r))).
Qed.

Lemma it_wbisim_seq {I E X1 X2 X3 RX1 RX2 RX3} (HX : (RX1 ⨟ RX2) <= RX3)
      : (@it_wbisim I E X1 X2 RX1 ⨟ @it_wbisim I E X2 X3 RX2) <= it_wbisim E RX3 .
  apply coinduction; intros ? ? ? [ ? [ u v ] ].
  eapply (Hbody (it_wbisim_map _ _)).
  - apply id_t.
  - apply (it_wbisimF_seq HX).
    refine (_ ⨟⨟ _); apply (gfp_fp (it_wbisim_map _ _)); [ exact u | exact v ].
Qed.

#[global] Instance it_wbisim_trans {I E X R} (H : Transitiveᵢ R) : Transitiveᵢ (@it_wbisim I E X X R).
  intros ? ? ? ? u v; refine (it_wbisim_seq _ _ _ _ (u ⨟⨟ v)).
  intros ? ? ? [ ? [ p q ] ]; exact (H _ _ _ _ p q).
Qed.


Section wsim.
  Context {I : Type} (E : event I I).
  Context {R1 R2 : I -> Type} (RR : relᵢ R1 R2).

  Variant it_wsimF RY i (t1 : itree' E R1 i) (t2 : itree' E R2 i) : Prop :=
    | WSim {x1} (r1 : it_eat i t1 x1) (rr : it_eqF E RR RY i x1 t2) .
  Arguments WSim {RY i t1 t2 x1}.

  Definition it_wsim_map : mon (relᵢ (itree E R1) (itree E R2)) := {|
    body RY i x y := it_wsimF RY i (observe x) (observe y) ;
    Hbody _ _ H _ _ _ '(WSim r1 rr) := WSim r1 (it_eqF_mon _ _ (fun _ _ _ r => r) _ _ H _ _ _ rr) ;
  |}.

  Definition it_wsim := gfp it_wsim_map.
  Definition it_wsim' := it_wsimF it_wsim.

End wsim.
#[global] Notation it_wsim_t E R := (t (@it_wsim_map _ E _ _ R)).
#[global] Notation it_wsim_bt E R := (bt (@it_wsim_map _ E _ _ R)).
#[global] Notation it_wsim_T E R := (T (@it_wsim_map _ E _ _ R)).

#[global] Arguments WSim {I E R1 R2 RR RY i t1 t2 x1}.
#[global] Hint Constructors it_wsimF : core.

Section wsim_facts1.
  Context {I : Type} {E : event I I}.
  Context {R1 R2 : psh I} {RR : relᵢ R1 R2}.
