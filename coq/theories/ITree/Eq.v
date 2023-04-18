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
Variant it_eqF {I} E X {Y1 Y2} (RR : relᵢ Y1 Y2) (i : I)
        : itreeF E X Y1 i -> itreeF E X Y2 i -> Prop :=
  | EqRet {r}                                         : it_eqF _ _ _ _ (RetF r)    (RetF r)
  | EqTau {t1 t2} (t_rel : RR i t1 t2)                : it_eqF _ _ _ _ (TauF t1)   (TauF t2)
  | EqVis {q k1 k2} (k_rel : forall r, RR _ (k1 r) (k2 r)) : it_eqF _ _ _ _ (VisF q k1) (VisF q k2)
.
#[global] Hint Constructors it_eqF : core.
#[global] Arguments EqRet {I E X Y1 Y2 RR i r}.
#[global] Arguments EqTau {I E X Y1 Y2 RR i t1 t2}.
#[global] Arguments EqVis {I E X Y1 Y2 RR i q k1 k2}.

Equations it_eqF_mon {I E X Y1 Y2} : Proper (leq ==> leq) (@it_eqF I E X Y1 Y2) :=
  it_eqF_mon _ _ H1 _ _ _ (EqRet) := EqRet ;
  it_eqF_mon _ _ H1 _ _ _ (EqTau t_rel) := EqTau (H1 _ _ _ t_rel) ;
  it_eqF_mon _ _ H1 _ _ _ (EqVis k_rel) := EqVis (fun r => H1 _ _ _ (k_rel r)) .
#[global] Existing Instance it_eqF_mon.

Definition it_eq_map {I} E X : mon (relᵢ (@itree I E X) (@itree I E X)) := {|
  body RR i x y := it_eqF E X RR i (observe x) (observe y) ;
  Hbody _ _ H _ _ _ r := it_eqF_mon _ _ H _ _ _ r ;
|}.

Definition it_eq {I E X} [i] := gfp (@it_eq_map I E X) i.
Notation it_eq_t E X := (t (it_eq_map E X)).
Notation it_eq_bt E X := (bt (it_eq_map E X)).
Notation it_eq_T E X := (T (it_eq_map E X)).

#[global] Instance it_eqbt_mon {I} {E : event I I} {X} : Proper (leq ==> leq) (@it_eq_bt E X).
  intros R1 R2 H i x y. apply it_eqF_mon. rewrite H. reflexivity.
  Qed.

Section it_eq_facts.
  Context {I} {E : event I I} {X : psh I}.

(*|
Reversal, symmetry.
|*)

  Lemma it_eqF_sym {Y1 Y2} {RR : relᵢ Y1 Y2} : revᵢ (it_eqF E X RR) <= it_eqF E X (revᵢ RR).
    intros ? ? ? p; cbn in *; destruct p; auto.
  Qed.

  Lemma it_eq_up2sym : converseᵢ <= it_eq_t E X.
  Proof. apply leq_t; repeat intro; now apply it_eqF_sym. Qed.

  #[global] Instance it_eq_t_sym {RR} : Symmetricᵢ (it_eq_t E X RR).
  Proof. apply build_symmetric, (ft_t it_eq_up2sym RR). Qed.

(*|
Reflexivity
|*)
  Lemma it_eqF_rfl {Y} : eqᵢ _ <= it_eqF E X (eqᵢ Y).
  Proof. intros ? [] ? <-; auto. Qed.

  Lemma it_eq_up2rfl : const (eqᵢ _) <= it_eq_t E X.
  Proof. apply leq_t; repeat intro; now apply (it_eqF_rfl), (f_equal observe). Qed.

  #[global] Instance it_eq_t_refl {RR} : Reflexiveᵢ (it_eq_t E X RR).
  Proof. apply build_reflexive, (ft_t it_eq_up2rfl RR). Qed.

(*|
Concatenation, transitivity.
|*)

  Lemma it_eqF_tra {Y1 Y2 Y3} {R1 : relᵢ Y1 Y2}  {R2 : relᵢ Y2 Y3}
        : (it_eqF E X R1 ⨟ it_eqF E X R2) <= it_eqF E X (R1 ⨟ R2).
  Proof.
    intros ? ? ? [ ? [ u v ] ].
    destruct u; dependent destruction v; simpl_depind; eauto.
  Qed.

  Lemma it_eq_up2tra : squareᵢ <= it_eq_t E X.
  Proof.
    apply leq_t; intros ? ? ? ? []; cbn in *.
    apply it_eqF_tra; eauto.
  Qed.

  #[global] Instance it_eq_t_trans {RR} : Transitiveᵢ (it_eq_t E X RR).
  Proof. apply build_transitive, (ft_t it_eq_up2tra RR). Qed.

  #[global] Instance it_eq_t_equiv {RR} : Equivalenceᵢ (it_eq_t E X RR).
  Proof. econstructor; typeclasses eauto. Qed.

  #[global] Instance it_eq_bt_equiv {RR} : Equivalenceᵢ (it_eq_bt E X RR).
  Proof.
    apply build_equivalence.
    - apply (fbt_bt it_eq_up2rfl).
    - apply (fbt_bt it_eq_up2sym).
    - apply (fbt_bt it_eq_up2tra).
   Qed.

End it_eq_facts.

Section wbisim.
  Context {I : Type} (E : event I I) (X : I -> Type).

  Variant it_wbisimF RR i (t1 : itree' E X i) (t2 : itree' E X i) : Prop :=
    | WBisim {x1 x2} (r1 : it_eat i t1 x1) (r2 : it_eat i t2 x2) (rr : it_eqF E X RR i x1 x2) .
  Arguments WBisim {RR i t1 t2 x1 x2}.

  Definition it_wbisim_map : mon (relᵢ (itree E X) (itree E X)) := {|
    body RR i x y := it_wbisimF RR i (observe x) (observe y) ;
    Hbody _ _ H _ _ _ '(WBisim r1 r2 rr) := WBisim r1 r2 (it_eqF_mon _ _ H _ _ _ rr) ;
  |}.

  Definition it_wbisim := gfp it_wbisim_map.
  Definition it_wbisim' := it_wbisimF it_wbisim.

End wbisim.
#[global] Notation it_wbisim_t E X := (t (it_wbisim_map E X)).
#[global] Notation it_wbisim_bt E X := (bt (it_wbisim_map E X)).
#[global] Notation it_wbisim_T E X := (T (it_wbisim_map E X)).

#[global] Arguments it_wbisim {I E X} [i].
#[global] Arguments WBisim {I E X RR i t1 t2 x1 x2}.
#[global] Hint Constructors it_wbisimF : core.

Section wbisim_facts1.
  Context {I : Type} {E : event I I} {X : psh I}.

(*|
Reversal, symmetry.
|*)

  Lemma it_wbisim_up2sym : converseᵢ <= it_wbisim_t E X.
  Proof.
    apply leq_t; intros ? ? ? ? [ ? ? r1 r2 rr ].
    refine (WBisim r2 r1 _).
    now apply it_eqF_sym.
  Qed.

  #[global] Instance it_wbisim_t_sym {RR} : Symmetricᵢ (it_wbisim_t E X RR).
  Proof. apply build_symmetric, (ft_t it_wbisim_up2sym RR). Qed.

  Equations wbisim_step_l {i x y} : it_wbisim' E X i x (TauF y) -> it_wbisim' E X i x (observe y) :=
    wbisim_step_l (WBisim p (EatRefl) (EqTau r))
      with proj1 (gfp_fp (it_wbisim_map E X) _ _ _) r :=
      { | WBisim w1 w2 s := WBisim (eat_trans _ _ _ _ p (EatStep w1)) w2 s } ;
    wbisim_step_l (WBisim p (EatStep q) v) := WBisim p q v .

  Equations wbisim_step_r {i x y} : it_wbisim' E X i (TauF x) y -> it_wbisim' E X i (observe x) y :=
    wbisim_step_r (WBisim (EatRefl) q (EqTau r))
      with proj1 (gfp_fp (it_wbisim_map E X) _ _ _) r :=
      { | WBisim w1 w2 s := WBisim w1 (eat_trans _ _ _ _ q (EatStep w2)) s } ;
    wbisim_step_r (WBisim (EatStep p) q v) := WBisim p q v .

  Equations? wbisim_tau_up_r {i x y z} (u : it_eat i x (TauF y))
             (v : it_eqF E X it_wbisim i (TauF y) z)
             : it_eqF E X it_wbisim i x z :=
    wbisim_tau_up_r (EatRefl)   q         := q ;
    wbisim_tau_up_r (EatStep p) (EqTau q) := EqTau _ .

  apply (gfp_fp (it_wbisim_map E X)) in q; destruct q as [ ? ? r1 r2 rr ].
  apply (gfp_fp (it_wbisim_map E X)).
  refine (WBisim _ r2 rr); eapply eat_trans; [ exact p | exact (EatStep r1) ].
  Defined.

  Equations? wbisim_tau_up_l {i x y z} (u : it_eqF E X it_wbisim i x (TauF y))
             (v : it_eat i z (TauF y))
             : it_eqF E X it_wbisim i x z :=
    wbisim_tau_up_l p         (EatRefl)   := p ;
    wbisim_tau_up_l (EqTau p) (EatStep q) := EqTau _ .

  apply (gfp_fp (it_wbisim_map E X)) in p; destruct p as [ ? ? r1 r2 rr ].
  apply (gfp_fp (it_wbisim_map E X)).
  refine (WBisim r1 _ rr); eapply eat_trans; [ exact q | exact (EatStep r2) ].
  Defined.

  Equations wbisim_ret_down_l {i x y r} : it_wbisim' E X i x y -> it_eat i y (RetF r)
                                      -> (it_eat ⨟ it_eqF E X it_wbisim) i x (RetF r) :=
    wbisim_ret_down_l (WBisim p (EatRefl) w) (EatRefl)   := p ⨟⨟ w ;
    wbisim_ret_down_l w                      (EatStep q) := wbisim_ret_down_l (wbisim_step_l w) q .

  Equations wbisim_ret_down_r {i x y r} : it_eat i x (RetF r) -> it_wbisim' E X i x y
                                      -> (it_eqF E X it_wbisim ⨟ revᵢ it_eat) i (RetF r) y :=
    wbisim_ret_down_r (EatRefl)   (WBisim (EatRefl) q w) := w ⨟⨟ q ;
    wbisim_ret_down_r (EatStep p) w                      := wbisim_ret_down_r p (wbisim_step_r w) .

  Equations wbisim_vis_down_l {i x y e k} : it_wbisim' E X i x y -> it_eat i y (VisF e k)
                                        -> (it_eat ⨟ it_eqF E X it_wbisim) i x (VisF e k) :=
    wbisim_vis_down_l (WBisim p (EatRefl) w) (EatRefl)   := p ⨟⨟ w ;
    wbisim_vis_down_l w                      (EatStep q) := wbisim_vis_down_l (wbisim_step_l w) q .

  Equations wbisim_vis_down_r {i x y e k} : it_eat i x (VisF e k) -> it_wbisim' E X i x y
                                      -> (it_eqF E X it_wbisim ⨟ revᵢ it_eat) i (VisF e k) y :=
    wbisim_vis_down_r (EatRefl)   (WBisim (EatRefl) q w) := w ⨟⨟ q ;
    wbisim_vis_down_r (EatStep p) w                      := wbisim_vis_down_r p (wbisim_step_r w) .


(*|
Concatenation, transitivity.
|*)

  Lemma it_wbisimF_tra : (it_wbisim' E X ⨟ it_wbisim' E X) <= it_wbisimF E X (it_wbisim ⨟ it_wbisim).
  Proof.
    intros i x y [z [[x1 x2 u1 u2 uS] [y1 y2 v1 v2 vS]]].
    destruct (eat_cmp _ _ _ (u2 ⨟⨟ v1)) as [w | w]; clear z u2 v1.
    - destruct y1.
      + destruct (wbisim_ret_down_l (WBisim u1 EatRefl uS) w) as [z [w1 ww]]; clear u1 uS w.
        dependent destruction vS; dependent destruction ww.
        exact (WBisim w1 v2 (EqRet)).
      + exact (WBisim u1 v2 (it_eqF_tra _ _ _ (uS ⨟⨟ wbisim_tau_up_r w vS))).
      + destruct (wbisim_vis_down_l (WBisim u1 EatRefl uS) w) as [z [w1 ww]]; clear u1 uS w.
        dependent destruction vS; dependent destruction ww.
        exact (WBisim w1 v2 (EqVis (fun r => k_rel0 r ⨟⨟ k_rel r))).
    - destruct x2.
      + destruct (wbisim_ret_down_r w (WBisim EatRefl v2 vS)) as [z [ww w1]]; clear v2 vS w.
        dependent destruction uS; dependent destruction ww.
        exact (WBisim u1 w1 (EqRet )).
      + exact (WBisim u1 v2 (it_eqF_tra _ _ _ (wbisim_tau_up_l uS w ⨟⨟ vS))).
      + destruct (wbisim_vis_down_r w (WBisim EatRefl v2 vS)) as [z [ww w1]]; clear v2 vS w.
        dependent destruction uS; dependent destruction ww.
        exact (WBisim u1 w1 (EqVis (fun r => k_rel r ⨟⨟ k_rel0 r))).
  Qed.

  #[global] Instance it_wbisim_tra : Transitiveᵢ (@it_wbisim I E X).
  Proof.
    apply build_transitive, coinduction; intros ? ? ? [ ? [ u v ] ].
    eapply (Hbody (it_wbisim_map _ _)).
    - apply id_t.
    - apply it_wbisimF_tra.
      refine (_ ⨟⨟ _); apply (gfp_fp (it_wbisim_map _ _)); [ exact u | exact v ].
  Qed.
End wbisim_facts1.

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
