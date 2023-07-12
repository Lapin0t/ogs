From Coinduction Require Import coinduction tactics.

From OGS Require Import Prelude.
From OGS.Utils Require Import Rel.
From OGS.Game Require Import Event.
From OGS.ITree Require Import ITree Structure Eq Properties.
From OGS.ITree Require Import Properties.

Section stuff.
  Context {I} {E : event I I}.

  Definition eqn R X Y : Type := X ⇒ᵢ itree E (Y +ᵢ R) .
 
  Definition apply_eqn {R X Y} (q : eqn R X Y) : itree E (X +ᵢ R) ⇒ᵢ itree E (Y +ᵢ R) :=
    fun _ t => t >>= fun _ r => match r with
                            | inl x => q _ x
                            | inr y => Ret' (inr y)
                            end .

  Variant guarded' {X Y i} : itree' E (X +ᵢ Y) i -> Prop :=
  | GRet y : guarded' (RetF (inr y))
  | GTau t : guarded' (TauF t)
  | GVis e k : guarded' (VisF e k)
  .
  Definition guarded {X Y i} (t : itree E (X +ᵢ Y) i) := guarded' t.(_observe). 
  Definition eqn_guarded {R X Y} (e : eqn R X Y) : Prop := forall i (x : X i), guarded (e i x) .

  Equations apply_guarded_l' {R X Y} (e : eqn R X Y) {i} t : guarded' t -> guarded (apply_eqn e i (go t)) :=
    apply_guarded_l' _ _ (GRet y)   := GRet _ ;
    apply_guarded_l' _ _ (GTau t)   := GTau _ ;
    apply_guarded_l' _ _ (GVis e k) := GVis _ _ .

  Definition apply_guarded_l {R X Y} (e : eqn R X Y) {i} t (p : guarded t) : guarded (apply_eqn e i t)
    := apply_guarded_l' e t.(_observe) p. 

  Equations apply_guarded_r' {R X Y} (e : eqn R X Y) (H : eqn_guarded e) {i} t : guarded (apply_eqn e i (go t)) :=
    apply_guarded_r' e H (RetF (inl x)) := H _ x ;
    apply_guarded_r' e H (RetF (inr _)) := GRet _ ;
    apply_guarded_r' e H (TauF _)       := GTau _ ;
    apply_guarded_r' e H (VisF _ _)     := GVis _ _ .

  Definition apply_guarded_r {R X Y} (e : eqn R X Y) (H : eqn_guarded e) {i} t : guarded (apply_eqn e i t)
    := apply_guarded_r' e H t.(_observe) .

  Lemma guarded'_irrelevant {R X i t} (p q : @guarded' R X i t) : p = q .
    destruct t; dependent elimination p; dependent elimination q; reflexivity.
  Qed.

  Lemma guarded_irrelevant {R X i t} (p q : @guarded R X i t) : p = q .
    apply guarded'_irrelevant.
  Qed.

  (*

  Definition iter_guarded_aux {R X} (e : eqn R X X) (H : eqn_guarded e) : itree E (X +ᵢ R) ⇒ᵢ itree E R :=
    cofix CIH i t := go match t.(_observe) with
                        | RetF (inl x) => match H i x with
                                          | GRet y => RetF y
                                          | GTau t => TauF (CIH _ t)
                                          | GVis e k => VisF e (fun r => CIH _ (k r))
                                          end
                        | RetF (inr y) => RetF y
                        | TauF t => TauF (CIH _ t)
                        | VisF e k => VisF e (fun r => CIH _ (k r))
                        end .
  *)

  Equations elim_guarded {R X i x} : @guarded' R X i (RetF (inl x)) -> T0 := | ! .    

  Definition iter_guarded_aux {R X} (e : eqn R X X) (H : eqn_guarded e) : itree E (X +ᵢ R) ⇒ᵢ itree E R :=
    cofix CIH i t := t >>= fun _ r => go match r with
                                     | inl x => match (e _ x).(_observe) as t return guarded' t -> _ with
                                                | RetF (inl x) => fun g => ex_falso (elim_guarded g)
                                                | RetF (inr r) => fun _ => RetF r
                                                | TauF t       => fun _ => TauF (CIH _ t)
                                                | VisF q k     => fun _ => VisF q (fun r => CIH _ (k r))
                                                end (H _ x)
                                     | inr y => RetF y
                                     end .

  Definition iter_guarded {R X} (f : eqn R X X) (H : eqn_guarded f) : X ⇒ᵢ itree E R :=
    fun _ x => go (match (f _ x).(_observe) as t return guarded' t -> _ with
                 | RetF (inl x) => fun g => ex_falso (elim_guarded g)
                 | RetF (inr r) => fun _ => RetF r
                 | TauF t       => fun _ => TauF (iter_guarded_aux f H _ t)
                 | VisF q k     => fun _ => VisF q (fun r => iter_guarded_aux f H _ (k r))
                 end (H _ x)) .

  (*
  Definition iter_guarded {R X} (e : eqn R X X) (H : eqn_guarded e) : X ⇒ᵢ itree E R :=
    fun _ x => iter_guarded_aux e H _ (e _ x) .
  *)

  Lemma iter_guarded_aux_unfold {X Y RY} {_ : Reflexiveᵢ RY} (f : eqn Y X X) (H : eqn_guarded f) {i}
    (t : itree E (X +ᵢ Y) i)
    : it_eq RY
        (iter_guarded_aux f H i t)
        (t >>= fun _ r => match r with
                         | inl x => iter_guarded f H _ x
                         | inr y => Ret' y
                       end).
    revert i t; unfold it_eq; coinduction R CIH; intros i t.
    cbn; pose (ot := _observe t); fold ot.
    destruct ot as [ [] | | ]; cbn.
    1: destruct (H i x).
    all: econstructor; auto.
    2: intro r.
    all: apply (tt_t (it_eq_map E RY)); cbn; eapply it_eq_up2bind_t; econstructor; auto.
    all: intros ? ? x2 ->; destruct x2; auto.
  Qed.
    
  Lemma iter_guarded_unfold {X Y RY} {_ : Reflexiveᵢ RY} (f : eqn Y X X) (H : eqn_guarded f) {i x}
    : it_eq RY
        (iter_guarded f H i x)
        (f i x >>= fun _ r => match r with
                            | inl x => iter_guarded f H _ x
                            | inr y => Ret' y
                            end).
    apply it_eq_unstep; cbn.
    pose (p := H i x); fold p; unfold guarded in p.
    pose (ot := _observe (f i x)); fold ot in p |- *.
    destruct p; econstructor; [ now apply H0 | | intro r ]; apply iter_guarded_aux_unfold.
  Qed.

  Lemma iter_guarded_uniq {X Y RY} {_ : Equivalenceᵢ RY} (f : eqn Y X X) (g : X ⇒ᵢ itree E Y)
                 (H0 : eqn_guarded f)
                 (H : forall i x, it_eq RY (g i x) (bind (f i x) (fun _ r => match r with
                                                  | inl x => g _ x
                                                  | inr y => Ret' y end)))
                 : forall i x, it_eq RY (g i x) (iter_guarded f H0 i x).
    unfold it_eq; coinduction R CIH; intros i x.
    etransitivity; [ | symmetry; apply it_eq_t_bt, (iter_guarded_unfold f H0) ].
    rewrite (H i x); cbn.
    pose (a := (f i x).(_observe)); fold a.
    pose (Ha := H0 i x); unfold guarded in Ha; fold a in Ha.
    destruct Ha; cbn; econstructor; auto; [ | intro r ].
    all: change (subst ?f _ ?t) with (bind t f).
    all: eapply (tt_t (it_eq_map E RY)).
    all: refine (it_eq_up2bind_t _ _ _ _ _ _ _); econstructor; eauto.
    all: intros ? ? ? <-; destruct x1; auto.
  Qed.

  Lemma guarded_cong' {X Y} {i} (s t : itree' E (X +ᵢ Y) i) (H : it_eq' (eqᵢ _) s t) (g : guarded' s)
    : guarded' t .
    destruct H as [ [] | | ]; [ dependent elimination g | rewrite <- r_rel | | ]; econstructor.
  Qed.

  Definition guarded_cong {X Y} {i} (s t : itree E (X +ᵢ Y) i) (H : s ≊ t) (g : guarded s) : guarded t
    := guarded_cong' s.(_observe) t.(_observe) (it_eq_step _ _ _ H) g .

  Unset Elimination Schemes.
  Inductive ev_guarded' {X Y} (e : eqn Y X X) {i} : itree' E (X +ᵢ Y) i -> Prop :=
  | GHead t : guarded' t -> ev_guarded' e t
  | GNext x : ev_guarded' e (e i x).(_observe) -> ev_guarded' e (RetF (inl x))
  .
  #[global] Arguments GHead {X Y e i t}.
  #[global] Arguments GNext {X Y e i x}.

  Scheme ev_guarded'_ind := Induction for ev_guarded' Sort Prop.
  Set Elimination Schemes.
  
  Lemma ev_guarded'_irrelevant {R X e i t} (p q : @ev_guarded' R X e i t) : p = q .
    induction p.
    - destruct t as [ [] | | ]; [ dependent elimination g | | | ];
        dependent elimination q; f_equal; apply guarded'_irrelevant.
    - dependent elimination q; [ dependent elimination g | ]; f_equal; apply IHp.
  Qed.

  Equations elim_ev_guarded' {X Y e i x} (g : @ev_guarded' X Y e i (RetF (inl x)))
    : ev_guarded' e (e i x).(_observe) :=
    elim_ev_guarded' (GNext g) := g .

  Definition ev_guarded {X Y} (e : eqn Y X X) {i} (t : itree E (X +ᵢ Y) i) := ev_guarded' e t.(_observe).
  Definition eqn_ev_guarded {X Y} (e : eqn Y X X) : Type := forall i (x : X i), ev_guarded e (e i x) .

  Fixpoint evg_unroll' {X Y} (e : eqn Y X X) {i} (t : itree' E (X +ᵢ Y) i) (g : ev_guarded' e t) { struct g }
    : itree' E (X +ᵢ Y) i
    := match t as t' return ev_guarded' e t' -> _ with
       | RetF (inl x) => fun g => evg_unroll' e (e _ x).(_observe) (elim_ev_guarded' g)
       | RetF (inr y) => fun _ => RetF (inr y)
       | TauF t       => fun _ => TauF t
       | VisF q k     => fun _ => VisF q k
       end g .

  Lemma evg_unroll'_equation {X Y} (e : eqn Y X X) {i} {x : X i} (g : ev_guarded' e (RetF (inl x)))
                             : evg_unroll' e (RetF (inl x)) g = evg_unroll' e (e _ x).(_observe) (elim_ev_guarded' g) .
  dependent elimination g; [ dependent elimination g | reflexivity ] .
  Qed.

  Definition evg_unroll {X Y} (e : eqn Y X X) {i} (t : itree E (X +ᵢ Y) i) (g : ev_guarded e t)
    : itree E (X +ᵢ Y) i := go (evg_unroll' e t.(_observe) g) .
  
  Lemma evg_unroll_guarded' {X Y} (e : eqn Y X X) {i} (t : itree' E (X +ᵢ Y) i) (g : ev_guarded' e t)
    : guarded' (evg_unroll' e t g) .
    induction g; auto.
    destruct t as [ [] | | ]; auto.
    dependent elimination g.
  Qed.

  Definition evg_unroll_guarded {X Y} (e : eqn Y X X) {i} (t : itree E (X +ᵢ Y) i) (g : ev_guarded e t)
    : guarded (evg_unroll e t g)
    := evg_unroll_guarded' e t.(_observe) g .

  Definition ev_guarded_cong' {X Y} {i} (e : eqn Y X X) {s t : itree' E (X +ᵢ Y) i} (H : it_eq' (eqᵢ _) s t)
    (g : ev_guarded' e s) : ev_guarded' e t .
    revert t H; induction g; intros u H.
    - exact (GHead (guarded_cong' _ _ H g)).
    - destruct u as [ [] | | ]; try (apply GHead; econstructor).
      apply GNext, IHg.
      dependent elimination H; inversion_clear r_rel.
      apply it_eq_step; reflexivity.
  Defined.

  Definition ev_guarded_cong {X Y} {i} (e : eqn Y X X) {s t : itree E (X +ᵢ Y) i} (H : s ≊ t)
    (g : ev_guarded e s) : ev_guarded e t
    := ev_guarded_cong' e (it_eq_step _ _ _ H) g .

  Lemma ev_guarded_cong_unroll' {X Y} {i} (e : eqn Y X X) {s t : itree' E (X +ᵢ Y) i}
    (H : it_eq' (eqᵢ _) s t) (g : ev_guarded' e s) : it_eq' (eqᵢ _) (evg_unroll' e s g) (evg_unroll' e t (ev_guarded_cong' e H g)).
    revert t H; induction g; intros u H.
    - destruct H.
      destruct r1; [ dependent elimination g | ].
      destruct r2; [ inversion r_rel | ].
      all: now econstructor.
    - destruct u as [ [] | | ]; dependent elimination H.
      * apply IHg.
      * inversion r_rel.
  Qed.

  Definition ev_guarded_cong_unroll {X Y} {i} (e : eqn Y X X) {s t : itree E (X +ᵢ Y) i}
    (H : s ≊ t) (g : ev_guarded e s) : evg_unroll e s g ≊ evg_unroll e t (ev_guarded_cong e H g) :=
    it_eq_unstep _ (go _) (go _) (ev_guarded_cong_unroll' e (it_eq_step _ _ _ H) g) .

  Definition eqn_evg_unroll {X Y} (e : eqn Y X X) (H : eqn_ev_guarded e) : eqn Y X X
    := fun _ x => evg_unroll e _ (H _ x) .

  Definition eqn_evg_unroll_guarded {X Y} (e : eqn Y X X) H : eqn_guarded (eqn_evg_unroll e H)
    := fun _ x => evg_unroll_guarded e _ (H _ x) .

  Definition iter_ev_guarded {R X} (e : eqn R X X) (H : eqn_ev_guarded e) : X ⇒ᵢ itree E R :=
    fun _ x => iter_guarded _ (eqn_evg_unroll_guarded e H) _ x .

  Lemma iter_evg_unfold_lem {X Y RY} {_ : Equivalenceᵢ RY} (f : eqn Y X X) (H : eqn_ev_guarded f) {i x1 x2}
    (p : (f i x1).(_observe) = RetF (inl x2))
    : it_eq RY
        (iter_ev_guarded f H i x1)
        (iter_ev_guarded f H i x2) .
    unfold iter_ev_guarded at 1.
    etransitivity; [ apply iter_guarded_unfold | ].
    change (iter_guarded _ _ ?i ?x) with (iter_ev_guarded f H i x).
    unfold eqn_evg_unroll; remember (H i x1) as q; clear Heqq.
    apply it_eq_unstep; unfold evg_unroll; cbn -[iter_ev_guarded].
    unfold ev_guarded in q; revert q; rewrite p; clear p; intro q.
    rewrite evg_unroll'_equation, (ev_guarded'_irrelevant (elim_ev_guarded' q) (H _ x2)); clear q.
    change (it_eqF E RY (it_eq RY) i _ (observe ?a))
      with (it_eq_map E RY (it_eq RY) i
             (evg_unroll f (f i x2) (H i x2) >>= fun (i0 : I) (r : (X +ᵢ Y) i0) =>
               match r with
               | inl x => iter_ev_guarded f H i0 x
               | inr y => Ret' y
               end)
             a).
    apply it_eq_step; symmetry; exact (iter_guarded_unfold _ _).
  Qed.

  Lemma iter_evg_unfold {X Y RY} {_ : Equivalenceᵢ RY} (f : eqn Y X X) (H : eqn_ev_guarded f) {i x}
    : it_eq RY
        (iter_ev_guarded f H i x)
        (f i x >>= fun _ r => match r with
                            | inl x => iter_ev_guarded f H _ x
                            | inr y => Ret' y
                            end).
    apply it_eq_unstep; cbn -[iter_ev_guarded].
    remember (H i x) as g; clear Heqg; unfold ev_guarded in g.
    remember (_observe (f i x)).
    destruct i0 as [ [] | | ].
      apply (it_eq_step _ (iter_ev_guarded f H i x) (iter_ev_guarded f H i x0)), iter_evg_unfold_lem; auto.
    all: clear g; cbn; unfold eqn_evg_unroll_guarded at 3, evg_unroll_guarded.
    all: remember (H i x) as g'; clear Heqg'; unfold ev_guarded in g'.
    all: revert g'; rewrite <- Heqi0; intros g'.
    all: dependent elimination g'; econstructor; auto; intros.
    all: apply iter_guarded_aux_unfold.
  Qed.

  Lemma iter_evg_uniq {X Y RY} {_ : Equivalenceᵢ RY} (f : eqn Y X X) (g : X ⇒ᵢ itree E Y)
                 (H0 : eqn_ev_guarded f)
                 (H : forall i x, it_eq RY (g i x) (bind (f i x) (fun _ r => match r with
                                                  | inl x => g _ x
                                                  | inr y => Ret' y end)))
                 : forall i x, it_eq RY (g i x) (iter_ev_guarded f H0 i x).
    unfold it_eq; coinduction R CIH; intros i x.
    rewrite iter_evg_unfold, (H i x).
    remember (H0 i x) as Ha; clear HeqHa; unfold ev_guarded in Ha.
    remember (f i x) as t; clear Heqt.
    remember (_observe t) as ot.
    revert t Heqot; induction Ha; intros t' Heqot.
    - dependent elimination g0; cbn; rewrite <- Heqot; econstructor; auto; [ | intro r ].
      all: eapply (tt_t (it_eq_map E RY)).
      all: refine (it_eq_up2bind_t _ _ _ _ _ _ _); econstructor; auto.
      all: intros ? ? x2 ->; destruct x2; auto.
    - cbn; rewrite <- Heqot.
      change (it_eqF E RY ?R i (_observe ?a) (_observe ?b)) with (it_eq_map E RY R i a b).
      rewrite iter_evg_unfold, (H i x0).
      apply IHHa; auto.
  Qed.
End stuff.
