Require Import Coq.Program.Equality.
From Coinduction Require Import lattice rel coinduction.

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
  
  Equations _eat_confluence {i a x y} : it_eat i a x -> it_eat i a y -> (it_eat ⨟ revᵢ it_eat) i x y :=
    _eat_confluence (EatRefl)    q           := q ⨟⨟ EatRefl ;
    _eat_confluence (EatStep p)  (EatRefl)   := EatRefl ⨟⨟ EatStep p ;
    _eat_confluence (EatStep p)  (EatStep q) := _eat_confluence p q .

  Equations eat_confluence : (revᵢ it_eat ⨟ it_eat) <= (it_eat ⨟ revᵢ it_eat) :=
    eat_confluence _ _ _ (p ⨟⨟ q) := _eat_confluence p q .
    
End it_eat.

#[global] Hint Constructors it_eat : core.
#[global] Arguments EatRefl {I E R i t}.
#[global] Arguments EatStep {I E R i t1 t2} p.

(* strong bisimilarity aka coinductive equality *)
Variant it_eqF {I} (E : event I I) {R1 R2 REC1 REC2} (RR : relᵢ R1 R2) (RREC : relᵢ REC1 REC2)
               (i : I) : itreeF E R1 REC1 i -> itreeF E R2 REC2 i -> Prop :=
  | EqRet {r1 r2} (r_rel : RR i r1 r2) : it_eqF E RR RREC i (RetF r1) (RetF r2)
  | EqTau {t1 t2} (t_rel : RREC i t1 t2) : it_eqF E RR RREC i (TauF t1) (TauF t2)
  | EqVis {q k1 k2} (k_rel : forall r, RREC _ (k1 r) (k2 r)) : it_eqF E RR RREC i (VisF q k1) (VisF q k2)
.
#[global] Hint Constructors it_eqF : core.
#[global] Arguments EqRet {I E R1 R2 REC1 REC2 RR RREC i r1 r2}.
#[global] Arguments EqTau {I E R1 R2 REC1 REC2 RR RREC i t1 t2}.
#[global] Arguments EqVis {I E R1 R2 REC1 REC2 RR RREC i q k1 k2}.


Equations it_eqF_mon {I} {E : event I I} {R1 R2 Y1 Y2} : Proper (leq ==> leq ==> leq) (@it_eqF I E R1 R2 Y1 Y2) :=
  it_eqF_mon _ _ H0 _ _ H1 _ _ _ (EqRet r_rel) := EqRet (H0 _ _ _ r_rel) ;
  it_eqF_mon _ _ H0 _ _ H1 _ _ _ (EqTau t_rel) := EqTau (H1 _ _ _ t_rel) ;
  it_eqF_mon _ _ H0 _ _ H1 _ _ _ (EqVis k_rel) := EqVis (fun r => H1 _ _ _ (k_rel r)) .

Definition it_eq_mon {I} (E : event I I) {R1 R2} (RR : relᵢ R1 R2) : mon (relᵢ (itree E R1) (itree E R2)) := {|
  body RREC i x y := it_eqF E RR RREC i (observe x) (observe y) ;
  Hbody _ _ H1 _ _ _ r := it_eqF_mon _ _ (fun _ _ _ r => r) _ _ H1 _ _ _ r ;
|}.

Definition it_eq {I} (E : event I I) {R1 R2} (RR RR : relᵢ R1 R2) := gfp (it_eq_mon E RR).


Equations it_eq_seq {I} {E : event I I}
      {X1 X2 X3} {RX1 : relᵢ X1 X2} {RX2 : relᵢ X2 X3}
      {Y1 Y2 Y3} {RY1 : relᵢ Y1 Y2} {RY2 : relᵢ Y2 Y3}
      : (it_eqF E RX1 RY1 ⨟ it_eqF E RX2 RY2) <= it_eqF E (RX1 ⨟ RX2) (RY1 ⨟ RY2) :=
  it_eq_seq _ _ _ (EqRet r_rel1 ⨟⨟ EqRet r_rel2) := EqRet (r_rel1 ⨟⨟ r_rel2) ;
  it_eq_seq _ _ _ (EqTau t_rel1 ⨟⨟ EqTau t_rel2) := EqTau (t_rel1 ⨟⨟ t_rel2) ;
  it_eq_seq _ _ _ (EqVis k_rel1 ⨟⨟ EqVis k_rel2) := EqVis (fun v => k_rel1 v ⨟⨟ k_rel2 v) .

Lemma it_eq_rev {I} {E : event I I} {X1 X2} {RX : relᵢ X1 X2} {Y1 Y2} {RY : relᵢ Y1 Y2}
      : revᵢ (it_eqF E RX RY) <= it_eqF E (revᵢ RX) (revᵢ RY).
intros ? ? ? p; cbv [revᵢ] in p; dependent elimination p; auto.
Qed.

Section it_eq_swap.
  Context {I : Type} {E : event I I}.
  Context {R1 R2 : psh I} {RR : relᵢ R1 R2}.
  Context {RREC : relᵢ (itree E R1) (itree E R2) }.

  Equations _swap_eat_eq (H : it_eq_mon E RR RREC <= RREC) {i x y z t}
    : it_eat i x y -> it_eqF E RR RREC i y z -> it_eat i z t -> (it_eqF E RR RREC ⨟ it_eat) i x t :=
    _swap_eat_eq H (EatRefl)   q r := q ⨟⨟ r ;
    _swap_eat_eq H (EatStep p) q r :=
      let (y , s) := _swap_eat_eq H p q r in
      ex_intro _ (TauF {| _observe := y |}) (conj (EqTau (H _ _ _ _)) (EatStep _)) .

  Equations swap_eat_eq (H : it_eq_mon E RR RREC <= RREC)
    : (it_eat ⨟ it_eqF E RR RREC ⨟ it_eat) <= (it_eqF E RR RREC ⨟ it_eat) :=
    swap_eat_eq H _ _ _ ((p ⨟⨟ q) ⨟⨟ r) := _swap_eat_eq H p q r .

  Equations _swap_eq_eat (H : RREC <= it_eq_mon E RR RREC) {i x y z}
    : it_eqF E RR RREC i x y -> it_eat i y z -> (it_eat ⨟ it_eqF E RR RREC) i x z :=
    _swap_eq_eat H p         (EatRefl)   := EatRefl ⨟⨟ p ;
    _swap_eq_eat H (EqTau p) (EatStep q) :=
      let (y , s) := _swap_eq_eat H (H _ _ _ p) q in
      EatStep _ ⨟⨟  _ .

  Equations swap_eq_eat (H : RREC <= it_eq_mon E RR RREC)
    : (it_eqF E RR RREC ⨟ it_eat) <= (it_eat ⨟ it_eqF E RR RREC) :=
    swap_eq_eat H _ _ _ (p ⨟⨟ q) := _swap_eq_eat H p q .

End it_eq_swap.

  

Section bisim.
  Context {I : Type} {E : event I I}.
  Context {R1 R2 : I -> Type} (RR : relᵢ R1 R2).

  Variant it_wbisimF (RREC : relᵢ (itree E R1) (itree E R2)) i (t1 : itree' E R1 i) (t2 : itree' E R2 i) : Prop :=
    | WBisim {x1 x2} : it_eat i t1 x1 -> it_eat i t2 x2 -> it_eqF E RR RREC i x1 x2 -> it_wbisimF RREC i t1 t2. 
  Arguments WBisim {RREC i t1 t2 x1 x2}.
  Hint Constructors it_wbisimF : core.
