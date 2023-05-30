Require Import Coq.Program.Equality.
From Coinduction Require Import lattice rel coinduction tactics.

From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.
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

  Definition it_eat' : relᵢ (itree E R) (itree E R) := fun i u v => it_eat i u.(_observe) v.(_observe).

  Definition it_eat_tau {i x y} (H : it_eat i (TauF x) (TauF y))
    : it_eat i x.(_observe) y.(_observe).
    dependent induction H; eauto.
    unfold observe in H; destruct x.(_observe) eqn:Hx; try inversion H; eauto.
  Defined.

End it_eat.

#[global] Hint Constructors it_eat : core.
#[global] Arguments EatRefl {I E R i t}.
#[global] Arguments EatStep {I E R i t1 t2} p.

(*|
Strong bisimilarity aka coinductive equality
|*)
Variant it_eqF {I} E {X1 X2} (RX : relᵢ X1 X2) {Y1 Y2} (RR : relᵢ Y1 Y2) (i : I)
        : itreeF E X1 Y1 i -> itreeF E X2 Y2 i -> Prop :=
  | EqRet {r1 r2} (r_rel : RX i r1 r2)                : it_eqF _ _ _ _ (RetF r1)   (RetF r2)
  | EqTau {t1 t2} (t_rel : RR i t1 t2)                : it_eqF _ _ _ _ (TauF t1)   (TauF t2)
  | EqVis {q k1 k2} (k_rel : forall r, RR _ (k1 r) (k2 r)) : it_eqF _ _ _ _ (VisF q k1) (VisF q k2)
.
#[global] Hint Constructors it_eqF : core.
#[global] Arguments EqRet {I E X1 X2 RX Y1 Y2 RR i r1 r2}.
#[global] Arguments EqTau {I E X1 X2 RX Y1 Y2 RR i t1 t2}.
#[global] Arguments EqVis {I E X1 X2 RX Y1 Y2 RR i q k1 k2}.

Equations it_eqF_mon {I E X1 X2 RX Y1 Y2} : Proper (leq ==> leq) (@it_eqF I E X1 X2 RX Y1 Y2) :=
  it_eqF_mon _ _ H1 _ _ _ (EqRet r_rel) := EqRet r_rel ;
  it_eqF_mon _ _ H1 _ _ _ (EqTau t_rel) := EqTau (H1 _ _ _ t_rel) ;
  it_eqF_mon _ _ H1 _ _ _ (EqVis k_rel) := EqVis (fun r => H1 _ _ _ (k_rel r)) .
#[global] Existing Instance it_eqF_mon.

Definition it_eq_map {I} E {X1 X2} RX : mon (relᵢ (@itree I E X1) (@itree I E X2)) := {|
  body RR i x y := it_eqF E RX RR i (observe x) (observe y) ;
  Hbody _ _ H _ _ _ r := it_eqF_mon _ _ H _ _ _ r ;
|}.

Definition it_eq {I E X1 X2} RX [i] := gfp (@it_eq_map I E X1 X2 RX) i.
#[global] Notation it_eq_t E RX := (t (it_eq_map E RX)).
#[global] Notation it_eq_bt E RX := (bt (it_eq_map E RX)).
#[global] Notation it_eq_T E RX := (T (it_eq_map E RX)).
#[global] Notation "a ≊ b" := (it_eq (eqᵢ _) a b) (at level 20).

Definition it_eq_step {I E X1 X2 RX} : it_eq RX <= @it_eq_map I E X1 X2 RX (it_eq RX)
  := fun i x y => proj1 (gfp_fp (it_eq_map E RX) i x y) .

Definition it_eq_unstep {I E X1 X2 RX} : @it_eq_map I E X1 X2 RX (it_eq RX) <= it_eq RX 
  := fun i x y => proj2 (gfp_fp (it_eq_map E RX) i x y) .

#[global] Instance it_eqbt_mon {I} {E : event I I} {X1 X2} {RX : relᵢ X1 X2}
  : Proper (leq ==> leq) (it_eq_bt E RX).
  intros R1 R2 H i x y. apply it_eqF_mon. rewrite H. reflexivity.
  Qed.

Section it_eq_facts.
  Context {I} {E : event I I} {X : psh I} {RX : relᵢ X X}.

(*|
Reversal, symmetry.
|*)

  Lemma it_eqF_sym {_ : Symmetricᵢ RX} {Y1 Y2} {RR : relᵢ Y1 Y2} : revᵢ (it_eqF E RX RR) <= it_eqF E RX (revᵢ RR).
    intros ? ? ? p; cbn in *; destruct p; try symmetry in r_rel; auto.
  Qed.

  Lemma it_eq_up2sym {_ : Symmetricᵢ RX} : converseᵢ <= it_eq_t E RX.
  Proof. apply leq_t; repeat intro; now apply it_eqF_sym. Qed.

  #[global] Instance it_eq_t_sym {_ : Symmetricᵢ RX} {RR} : Symmetricᵢ (it_eq_t E RX RR).
  Proof. apply build_symmetric, (ft_t it_eq_up2sym RR). Qed.

(*|
Reflexivity
|*)
  Lemma it_eqF_rfl {_ : Reflexiveᵢ RX} {Y} : eqᵢ _ <= it_eqF E RX (eqᵢ Y).
  Proof. intros ? [] ? <-; auto. Qed.

  Lemma it_eq_up2rfl {_ : Reflexiveᵢ RX} : const (eqᵢ _) <= it_eq_t E RX.
  Proof. apply leq_t; repeat intro; now apply (it_eqF_rfl), (f_equal observe). Qed.

  #[global] Instance it_eq_t_refl {_ : Reflexiveᵢ RX} {RR} : Reflexiveᵢ (it_eq_t E RX RR).
  Proof. apply build_reflexive, (ft_t it_eq_up2rfl RR). Qed.

(*|
Concatenation, transitivity.
|*)

  Lemma it_eqF_tra {_ : Transitiveᵢ RX} {Y1 Y2 Y3} {R1 : relᵢ Y1 Y2}  {R2 : relᵢ Y2 Y3}
        : (it_eqF E RX R1 ⨟ it_eqF E RX R2) <= it_eqF E RX (R1 ⨟ R2).
  Proof.
    intros ? ? ? [ ? [ u v ] ].
    destruct u; dependent destruction v; simpl_depind; eauto.
    econstructor; transitivity r2; auto.
  Qed.

  Lemma it_eq_up2tra {_ : Transitiveᵢ RX} : squareᵢ <= it_eq_t E RX.
  Proof.
    apply leq_t; intros ? ? ? ? []; cbn in *.
    apply it_eqF_tra; eauto.
  Qed.

  #[global] Instance it_eq_t_trans {_ : Transitiveᵢ RX} {RR} : Transitiveᵢ (it_eq_t E RX RR).
  Proof. apply build_transitive, (ft_t it_eq_up2tra RR). Qed.

  #[global] Instance it_eq_t_equiv {_ : Equivalenceᵢ RX} {RR} : Equivalenceᵢ (it_eq_t E RX RR).
  Proof. econstructor; typeclasses eauto. Qed.

  #[global] Instance it_eq_bt_equiv {_ : Equivalenceᵢ RX} {RR} : Equivalenceᵢ (it_eq_bt E RX RR).
  Proof.
    apply build_equivalence.
    - apply (fbt_bt it_eq_up2rfl).
    - apply (fbt_bt it_eq_up2sym).
    - apply (fbt_bt it_eq_up2tra).
   Qed.

End it_eq_facts.

Section wbisim.
  Context {I : Type} (E : event I I) {X1 X2 : psh I} (RX : relᵢ X1 X2).

  Variant it_wbisimF RR i (t1 : itree' E X1 i) (t2 : itree' E X2 i) : Prop :=
    | WBisim {x1 x2} (r1 : it_eat i t1 x1) (r2 : it_eat i t2 x2) (rr : it_eqF E RX RR i x1 x2) .
  Arguments WBisim {RR i t1 t2 x1 x2}.

  Definition it_wbisim_map : mon (relᵢ (itree E X1) (itree E X2)) := {|
    body RR i x y := it_wbisimF RR i (observe x) (observe y) ;
    Hbody _ _ H _ _ _ '(WBisim r1 r2 rr) := WBisim r1 r2 (it_eqF_mon _ _ H _ _ _ rr) ;
  |}.

  Definition it_wbisim := gfp it_wbisim_map.
  Definition it_wbisim' := it_wbisimF it_wbisim.


End wbisim.
#[global] Notation it_wbisim_t E RX := (t (it_wbisim_map E RX)).
#[global] Notation it_wbisim_bt E RX := (bt (it_wbisim_map E RX)).
#[global] Notation it_wbisim_T E RX := (T (it_wbisim_map E RX)).

#[global] Arguments it_wbisim {I E X1 X2} RX i.
#[global] Notation "a ≈ b" := (it_wbisim (eqᵢ _) _ a b) (at level 20).

#[global] Arguments WBisim {I E X1 X2 RX RR i t1 t2 x1 x2}.
#[global] Hint Constructors it_wbisimF : core.

Definition it_wbisim_step {I E X1 X2 RX}
  : it_wbisim RX <= @it_wbisim_map I E X1 X2 RX (it_wbisim RX)
  := fun i x y => proj1 (gfp_fp (it_wbisim_map E RX) i x y) .

Definition it_wbisim_unstep {I E X1 X2 RX}
  : @it_wbisim_map I E X1 X2 RX (it_wbisim RX) <= it_wbisim RX
  := fun i x y => proj2 (gfp_fp (it_wbisim_map E RX) i x y) .


Section wbisim_facts_het.
  Context {I : Type} {E : event I I} {X1 X2 : psh I} {RX : relᵢ X1 X2}.

(*|
Reversal, symmetry.
|*)

  Lemma it_wbisim_obs {i x y} : it_wbisim (E:=E) RX i x y -> it_wbisim RX i (go x.(_observe)) (go y.(_observe)).
    intro H.
    apply it_wbisim_step in H.
    apply it_wbisim_unstep.
    exact H.
  Qed.

  Lemma it_wbisim_up2eq : const (it_eq RX) <= it_wbisim_t E RX.
    apply leq_t; intros R i x y H1.
    cbn in H1; apply it_eq_step in H1.
    cbn in *; dependent destruction H1; simpl_depind; eauto.
  Qed.

  Lemma it_wbisim_up2eqF : it_eq_map E RX <= it_wbisim_t E RX.
    apply Coinduction; intros R i x y H.
    cbn in *; dependent destruction H; simpl_depind; econstructor; eauto; econstructor.
    - apply (b_T (it_wbisim_map E RX)), t_rel.
    - intro r; apply (b_T (it_wbisim_map E RX)), k_rel.
  Qed.

  Lemma it_eq_wbisim : it_eq (E:=E) RX <= it_wbisim (E:=E) RX.
    unfold it_wbisim, leq; cbn. unfold Basics.impl.
    coinduction R CIH; intros i x y H.
    apply it_eq_step in H; cbn in *.
    dependent destruction H; simpl_depind; eauto.
  Qed.

  Equations wbisim_step_l {i x y} : it_wbisim' E RX i x (TauF y) -> it_wbisim' E RX i x (observe y) :=
    wbisim_step_l (WBisim p (EatRefl) (EqTau r))
      with it_wbisim_step _ _ _ r :=
      { | WBisim w1 w2 s := WBisim (eat_trans _ _ _ _ p (EatStep w1)) w2 s } ;
    wbisim_step_l (WBisim p (EatStep q) v) := WBisim p q v .

  Equations wbisim_step_r {i x y} : it_wbisim' E RX i (TauF x) y -> it_wbisim' E RX i (observe x) y :=
    wbisim_step_r (WBisim (EatRefl) q (EqTau r))
      with it_wbisim_step _ _ _ r :=
      { | WBisim w1 w2 s := WBisim w1 (eat_trans _ _ _ _ q (EatStep w2)) s } ;
    wbisim_step_r (WBisim (EatStep p) q v) := WBisim p q v .

  Equations wbisim_tau_up_r {i x y z} (u : it_eat i x (TauF y))
             (v : it_eqF E RX (it_wbisim RX) i (TauF y) z)
             : it_eqF E RX (it_wbisim RX) i x z :=
    wbisim_tau_up_r (EatRefl)   q         := q ;
    wbisim_tau_up_r (EatStep p) (EqTau q) with it_wbisim_step _ _ _ q := {
      | WBisim w1 w2 s :=
          EqTau (it_wbisim_unstep _ _ _ (WBisim (eat_trans _ _ _ _ p (EatStep w1)) w2 s))
    } .

  Equations wbisim_tau_up_l {i x y z} (u : it_eqF E RX (it_wbisim RX) i x (TauF y))
             (v : it_eat i z (TauF y))
             : it_eqF E RX (it_wbisim RX) i x z :=
    wbisim_tau_up_l p         (EatRefl)   := p ;
    wbisim_tau_up_l (EqTau p) (EatStep q) with it_wbisim_step _ _ _ p := {
     | WBisim w1 w2 s :=
         EqTau (it_wbisim_unstep _ _ _ (WBisim w1 (eat_trans _ _ _ _ q (EatStep w2)) s))
    } .

  Equations wbisim_ret_down_l {i x y r} : it_wbisim' E RX i x y -> it_eat i y (RetF r)
                                      -> (it_eat ⨟ it_eqF E RX (it_wbisim RX)) i x (RetF r) :=
    wbisim_ret_down_l (WBisim p (EatRefl) w) (EatRefl)   := p ⨟⨟ w ;
    wbisim_ret_down_l w                      (EatStep q) := wbisim_ret_down_l (wbisim_step_l w) q .

  Equations wbisim_ret_down_r {i x y r} : it_eat i x (RetF r) -> it_wbisim' E RX i x y
                                      -> (it_eqF E RX (it_wbisim RX) ⨟ revᵢ it_eat) i (RetF r) y :=
    wbisim_ret_down_r (EatRefl)   (WBisim (EatRefl) q w) := w ⨟⨟ q ;
    wbisim_ret_down_r (EatStep p) w                      := wbisim_ret_down_r p (wbisim_step_r w) .

  Equations wbisim_vis_down_l {i x y e k} : it_wbisim' E RX i x y -> it_eat i y (VisF e k)
                                        -> (it_eat ⨟ it_eqF E RX (it_wbisim RX)) i x (VisF e k) :=
    wbisim_vis_down_l (WBisim p (EatRefl) w) (EatRefl)   := p ⨟⨟ w ;
    wbisim_vis_down_l w                      (EatStep q) := wbisim_vis_down_l (wbisim_step_l w) q .

  Equations wbisim_vis_down_r {i x y e k} : it_eat i x (VisF e k) -> it_wbisim' E RX i x y
                                      -> (it_eqF E RX (it_wbisim RX) ⨟ revᵢ it_eat) i (VisF e k) y :=
    wbisim_vis_down_r (EatRefl)   (WBisim (EatRefl) q w) := w ⨟⨟ q ;
    wbisim_vis_down_r (EatStep p) w                      := wbisim_vis_down_r p (wbisim_step_r w) .

End wbisim_facts_het.

Section wbisim_facts_hom.
  Context {I : Type} {E : event I I} {X : psh I} {RX : relᵢ X X}.


  #[global] Instance it_eq_wbisim_subrel
    : Subrelationᵢ (it_eq (E:=E) RX) (it_wbisim (E:=E) RX)
    := it_eq_wbisim.

  Lemma it_wbisim_up2rfl {_ : Reflexiveᵢ RX} : const (eqᵢ _) <= it_wbisim_t E RX.
  Proof.
    apply leq_t.
    repeat intro.
    rewrite H0.
    econstructor; eauto.
    now apply it_eqF_rfl.
  Qed.

  #[global] Instance it_wbisim_t_refl {_ : Reflexiveᵢ RX} {RR} : Reflexiveᵢ (it_wbisim_t E RX RR).
  Proof. apply build_reflexive, (ft_t it_wbisim_up2rfl RR). Qed.
    
  Lemma it_wbisim_up2sym {_ : Symmetricᵢ RX} : converseᵢ <= it_wbisim_t E RX.
  Proof.
    apply leq_t; intros ? ? ? ? [ ? ? r1 r2 rr ].
    refine (WBisim r2 r1 _).
    now apply it_eqF_sym.
  Qed.

  #[global] Instance it_wbisim_t_sym {_ : Symmetricᵢ RX} {RR} : Symmetricᵢ (it_wbisim_t E RX RR).
  Proof. apply build_symmetric, (ft_t it_wbisim_up2sym RR). Qed.

(*|
Concatenation, transitivity.
|*)

  Lemma it_wbisimF_tra {_ : Transitiveᵢ RX} : (it_wbisim' E RX ⨟ it_wbisim' E RX) <= it_wbisimF E RX (it_wbisim RX ⨟ it_wbisim RX).
  Proof.
    intros i x y [z [[x1 x2 u1 u2 uS] [y1 y2 v1 v2 vS]]].
    destruct (eat_cmp _ _ _ (u2 ⨟⨟ v1)) as [w | w]; clear z u2 v1.
    - destruct y1.
      + destruct (wbisim_ret_down_l (WBisim u1 EatRefl uS) w) as [z [w1 ww]]; clear u1 uS w.
        dependent destruction vS; dependent destruction ww.
        refine (WBisim w1 v2 (EqRet _)); now transitivity r.
      + exact (WBisim u1 v2 (it_eqF_tra _ _ _ (uS ⨟⨟ wbisim_tau_up_r w vS))).
      + destruct (wbisim_vis_down_l (WBisim u1 EatRefl uS) w) as [z [w1 ww]]; clear u1 uS w.
        dependent destruction vS; dependent destruction ww.
        exact (WBisim w1 v2 (EqVis (fun r => k_rel0 r ⨟⨟ k_rel r))).
    - destruct x2.
      + destruct (wbisim_ret_down_r w (WBisim EatRefl v2 vS)) as [z [ww w1]]; clear v2 vS w.
        dependent destruction uS; dependent destruction ww.
        refine (WBisim u1 w1 (EqRet _)); now transitivity r.
      + exact (WBisim u1 v2 (it_eqF_tra _ _ _ (wbisim_tau_up_l uS w ⨟⨟ vS))).
      + destruct (wbisim_vis_down_r w (WBisim EatRefl v2 vS)) as [z [ww w1]]; clear v2 vS w.
        dependent destruction uS; dependent destruction ww.
        exact (WBisim u1 w1 (EqVis (fun r => k_rel r ⨟⨟ k_rel0 r))).
  Qed.

  #[global] Instance it_wbisim_tra {_ : Transitiveᵢ RX} : Transitiveᵢ (@it_wbisim I E X X RX).
  Proof.
    apply build_transitive, coinduction; intros ? ? ? [ ? [ u v ] ].
    eapply (Hbody (it_wbisim_map _ _)).
    - apply id_t.
    - apply it_wbisimF_tra.
      refine (_ ⨟⨟ _) ; apply it_wbisim_step; [ exact u | exact v ].
  Qed.

  #[global] Instance it_wbisim_equiv {_ : Equivalenceᵢ RX} : Equivalenceᵢ (it_wbisim (E:=E) RX).
  Proof. econstructor; typeclasses eauto. Qed.

  Lemma it_wbisim_tau {_ : Equivalenceᵢ RX} {i x y} : it_wbisim (E:=E) RX i (Tau' x) (Tau' y) -> it_wbisim RX i x y.
    intro H1.
    transitivity (Tau' x).
    apply it_wbisim_unstep.
    econstructor; [ exact EatRefl | exact (EatStep EatRefl) | destruct (observe x); eauto ].
    transitivity (Tau' y).
    exact H1.
    apply it_wbisim_unstep.
    econstructor; [ exact (EatStep EatRefl) | exact EatRefl | destruct (observe y); eauto ].
  Qed.

End wbisim_facts_hom.

(* WIP tau-expansion order ⪅
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
*)
