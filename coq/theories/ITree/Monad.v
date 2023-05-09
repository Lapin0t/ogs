Require Import Coq.Program.Equality.
Import EqNotations.

From Coinduction Require Import coinduction lattice rel tactics.

From OGS Require Import Utils.
From OGS.Utils Require Import Rel.
From OGS.Game Require Import Event.
From OGS.ITree Require Import ITree Eq.


Section monad.
  Context {I} {E : event I I}.

  Definition fmap {X Y} (f : X ⇒ᵢ Y) : itree E X ⇒ᵢ itree E Y :=
    cofix _fmap _ u :=
      go (match u.(_observe) with
         | RetF r => RetF (f _ r)
         | TauF t => TauF (_fmap _ t)
         | VisF e k => VisF e (fun r => _fmap _ (k r))
         end).

  #[global] Instance fmap_eq {X RX Y RY} {f : X ⇒ᵢ Y}
    {_ : forall i, Proper (@RX i ==> @RY i) (f i)}
    {i} : Proper (it_eq RX (i:=i) ==> it_eq RY (i:=i)) (fmap f i).
  Proof.
    unfold Proper, respectful, it_eq.
    revert i; coinduction R CIH; intros i x y h.
    apply (gfp_fp (it_eq_map E RX)) in h.
    cbn in *; cbv [observe] in h; dependent destruction h; simpl_depind; eauto.
    econstructor; now apply H.
  Qed.

  Definition subst {X Y} (f : X ⇒ᵢ itree E Y) : itree E X ⇒ᵢ itree E Y :=
    cofix _subst _ u :=
      go (match u.(_observe) with
         | RetF r => (f _ r).(_observe)
         | TauF t => TauF (_subst _ t)
         | VisF e k => VisF e (fun r => _subst _ (k r))
          end).

  #[global] Instance subst_eq {X Y} {RX : relᵢ X X} {RY : relᵢ Y Y}
    : Proper (dpointwise_relation (fun i => RX i ==> it_eq RY (i:=i))
              ==> dpointwise_relation (fun i => it_eq RX (i:=i) ==> it_eq RY (i:=i)))
        (@subst X Y).
  Proof.
    unfold Proper, respectful, dpointwise_relation, pointwise_relation, it_eq.
    intros f g h1; coinduction R CIH; intros i x y h2.
    apply (gfp_fp (it_eq_map E RX)) in h2.
    cbn in *; cbv [observe] in h2; dependent destruction h2; simpl_depind; eauto.
    pose (h3 := h1 i _ _ r_rel).
    apply (gfp_fp (it_eq_map E RY)) in h3.
    cbn in h3; cbv [observe] in h3.
    dependent destruction h3; simpl_depind; econstructor; eauto.
    2: intro.
    all: now apply (gfp_t (it_eq_map E RY)).
  Qed.
  
  #[global] Instance subst_eat {X Y} (f : X ⇒ᵢ itree E Y) {i}
   : Proper (it_eat' i ==> it_eat' i) (subst f i).
  Proof.
    intros ? ? H; unfold it_eat' in *; cbn.
    dependent induction H; simpl_depind; econstructor; cbn; eauto.
  Qed.    

  Definition bind {X Y i} x f := @subst X Y f i x.

  Variant bindR {X1 X2 Y1 Y2} (RX : relᵢ X1 X2) (R : relᵢ (itree E X1) (itree E X2))
                (S : relᵢ (itree E Y1) (itree E Y2))
          : relᵢ (itree E Y1) (itree E Y2) :=
    | BindR {i t1 t2 k1 k2}
        (u : R i t1 t2)
        (v : forall i x1 x2, RX i x1 x2 -> S i (k1 i x1) (k2 i x2))
      : bindR RX R S i (bind t1 k1) (bind t2 k2).
  Arguments BindR {X1 X2 Y1 Y2 RX R S i t1 t2 k1 k2}.    
  Hint Constructors bindR : core.

  Program Definition bindR_eq_map {X1 X2 Y1 Y2} (RX : relᵢ X1 X2) : mon (relᵢ (itree E Y1) (itree E Y2)) :=
    {| body S := bindR RX (@it_eq _ E _ _ RX) S ;
       Hbody _ _ H _ _ _ '(BindR u v) := BindR u (fun i _ _ r => H _ _ _ (v i _ _ r)) |}.

  Lemma it_eq_up2bind_t {X1 X2 Y1 Y2} RX RY : @bindR_eq_map X1 X2 Y1 Y2 RX <= it_eq_t E RY.
  Proof.
    apply Coinduction; intros R i x y [ ? ? ? ? ? u v].
    unfold it_eq in u; apply (gfp_fp (it_eq_map E RX)) in u.
    cbn in *; cbv [observe] in u.
    dependent destruction u; simpl_depind.
    - refine (it_eqF_mon _ _ (id_T _ _ R) _ _ _ (v i0 _ _ r_rel)).
    - econstructor; apply (fTf_Tf (it_eq_map E RY)).
      refine (BindR t_rel (fun i _ _ r => b_T (it_eq_map E RY) _ _ _ _ _ (v i _ _ r))).
    - econstructor; intros r; apply (fTf_Tf (it_eq_map E RY)).
      refine (BindR (k_rel r) (fun i _ _ r => b_T (it_eq_map E RY) _ _ _ _ _ (v i _ _ r))).
  Qed.

  Program Definition bindR_w_map {X1 X2 Y1 Y2} (RX : relᵢ X1 X2) : mon (relᵢ (itree E Y1) (itree E Y2)) :=
    {| body S := bindR RX (@it_wbisim _ E _ _ RX) S ;
       Hbody _ _ H _ _ _ '(BindR u v) := BindR u (fun i _ _ r => H _ _ _ (v i _ _ r)) |}.

  Lemma it_wbisim_up2bind_t {X1 X2 Y1 Y2} RX RY : @bindR_w_map X1 X2 Y1 Y2 RX <= it_wbisim_t E RY.
  Proof.
    apply Coinduction; intros R i x y [ ? ? ? ? ? u v].
    unfold it_wbisim in u; apply (gfp_fp (it_wbisim_map E RX)) in u.
    cbn in *; cbv [observe] in u.
    destruct u as [? ? r1 r2 rr]; dependent destruction rr.
    - destruct (v _ _ _ r_rel) as [ ? ? s1 s2 ss]; econstructor.
      etransitivity; [ exact (subst_eat _ _ (Ret' _) r1) | exact s1 ].
      etransitivity; [ exact (subst_eat _ _ (Ret' _) r2) | exact s2 ].
      now apply (it_eqF_mon _ _ (id_T _ _ R)).
   - econstructor.
     exact (subst_eat _ _ (Tau' _) r1).
     exact (subst_eat _ _ (Tau' _) r2).
     cbn; econstructor.
     apply (fTf_Tf (it_wbisim_map E RY)).
     econstructor; [ apply t_rel | intros; now apply (b_T (it_wbisim_map E RY)), v ].
   - econstructor.
     exact (subst_eat _ _ (Vis' _ _) r1).
     exact (subst_eat _ _ (Vis' _ _) r2).
     cbn; econstructor; intro r.
     apply (fTf_Tf (it_wbisim_map E RY)).
     econstructor; [ apply k_rel | intros; now apply (b_T (it_wbisim_map E RY)), v ].
 Qed.

  Definition kcomp {X Y Z} (f : X ⇒ᵢ itree E Y) (g : Y ⇒ᵢ itree E Z) : X ⇒ᵢ itree E Z :=
    fun i x => bind (f i x) g.

  Definition iter {X Y} (f : X ⇒ᵢ itree E (X +ᵢ Y)) : X ⇒ᵢ itree E Y :=
    cofix _iter _ x :=
      bind (f _ x) (fun _ r => go (match r with
                                | inl x => TauF (_iter _ x)
                                | inr y => RetF y end)) .

  Open Scope signature.

  Lemma iter_cong_strong {X1 X2 Y1 Y2} {RX : relᵢ X1 X2} {RY : relᵢ Y1 Y2}
                      f g (_ : forall i a b, RX i a b ->  it_eq (sumᵣ RX RY) (f i a) (g i b))
                      : forall i a b, RX i a b -> it_eq RY (iter f i a) (iter g i b).
  Proof.
    unfold it_eq; coinduction R CIH; intros i a b r.
    pose (h1 := H i a b r).
    apply it_eq_step in h1; cbn in *; cbv [observe] in h1.
    dependent destruction h1; simpl_depind.
    - destruct r_rel; eauto.
    - econstructor.
      apply (tt_t (it_eq_map E _)); cbn.
      apply (it_eq_up2bind_t (sumᵣ RX RY) RY); econstructor; eauto.
      intros ? ? ? []; apply (tt_t (it_eq_map E RY)), (b_t (it_eq_map E RY)); cbn; eauto.
    - econstructor; intro.
      apply (tt_t (it_eq_map E _)); cbn.
      apply (it_eq_up2bind_t (sumᵣ RX RY) RY); econstructor; eauto.
      intros ? ? ? []; apply (bt_t (it_eq_map E RY)); cbn; eauto.
  Qed.

  #[global] Instance iter_proper_strong {X Y} {RX : relᵢ X X} {RY : relᵢ Y Y}
    : Proper (dpointwise_relation (fun i => RX i ==> it_eq (sumᵣ RX RY) (i:=i))
              ==> dpointwise_relation (fun i => RX i ==> it_eq RY (i:=i)))
        (@iter X Y)
    := iter_cong_strong.


  (*
  Definition iter_op {X Y} (f : X ⇒ᵢ itree E (X +ᵢ Y)) (R : relᵢ Y Y) : mon (relᵢ X X).
    unshelve econstructor.
    - intros S i x y. refine (it_wbisim (sumᵣ S R) (f i x) (f i y)).
    - intros ? ? H.
      unfold it_wbisim; cbn; unfold Basics.impl.
      coinduction RR CIH.
      intros ? a b u.
      apply (gfp_fp (it_wbisim_map E _)) in u.
      cbn in *. destruct u. destruct rr.
      * econstructor; [exact r1 | exact r2 | ].
        econstructor. destruct r_rel; econstructor; try apply H; auto.
      * econstructor; [exact r1 | exact r2 | ].
        econstructor. apply (CIH _ _ _ t_rel).
      * 
        
        destruct r_rel.

      d
      
      
    

  Lemma iter_inv {X Y} (f : X ⇒ᵢ Y) {i x y} : iter f i x ≈ iter g i x -> gfp () i x y
*)
  Lemma iter_cong_weak {X1 X2 Y1 Y2} {RX : relᵢ X1 X2} {RY : relᵢ Y1 Y2}
                      f g (_ : forall i a b, RX i a b -> it_wbisim (sumᵣ RX RY) i (f i a) (g i b))
                      : forall i a b, RX i a b -> it_wbisim RY i (iter f i a) (iter g i b).
  Proof.
    unfold it_wbisim; coinduction R CIH; intros i a b r.
    pose (H1 := H i a b r).
    apply it_wbisim_step in H1.
    cbn in *; cbv [observe] in H1.
    destruct H1 as [ ? ? r1 r2 rr ]; dependent destruction rr.
    - destruct r_rel.
      * pose (H2 := H _ _ _ H0).
        apply it_wbisim_step in H2.
        destruct H2 as [ ? ? s1 s2 ss ].
        econstructor.
        exact (subst_eat _ _ (Ret' _) r1).
        exact (subst_eat _ _ (Ret' _) r2).
        econstructor.
        now apply CIH.
      * econstructor.
        exact (subst_eat _ _ (Ret' _) r1).
        exact (subst_eat _ _ (Ret' _) r2).
        now econstructor.
    - econstructor.
      exact (subst_eat _ _ (Tau' _) r1).
      exact (subst_eat _ _ (Tau' _) r2).
      cbn; econstructor.
      apply (tt_t (it_wbisim_map E _)); cbn.
      apply (it_wbisim_up2bind_t (sumᵣ RX RY) RY); econstructor; eauto.
      intros ? ? ? []; apply (tt_t (it_wbisim_map E RY)), (b_t (it_wbisim_map E RY)); cbn; eauto.
    - econstructor.
      exact (subst_eat _ _ (Vis' _ _) r1).
      exact (subst_eat _ _ (Vis' _ _) r2).
      cbn; econstructor; intro.
      apply (tt_t (it_wbisim_map E _)); cbn.
      apply (it_wbisim_up2bind_t (sumᵣ RX RY) RY); econstructor; [ apply k_rel | ].
      intros ? ? ? []; apply (tt_t (it_wbisim_map E RY)), (b_t (it_wbisim_map E RY)); cbn; eauto.
  Qed.

  #[global] Instance iter_weq {X Y} {RX : relᵢ X X} {RY : relᵢ Y Y}
    : Proper (dpointwise_relation (fun i => RX i ==> it_wbisim (sumᵣ RX RY) i)
              ==> dpointwise_relation (fun i => RX i ==> it_wbisim RY i))
        (@iter X Y)
    := iter_cong_weak.

  Lemma iter_unfold {X Y RY} {_ : Reflexiveᵢ RY} (f : X ⇒ᵢ itree E (X +ᵢ Y)) {i x}
    : it_eq RY
        (iter f i x)
        (bind (f i x) (fun _ r => go (match r with
                                   | inl x => TauF (iter f _ x)
                                   | inr y => RetF y end))).
  Proof.
    apply (gfp_fp (it_eq_map E RY)).
    cbn; destruct (_observe (f i x)); auto.
    destruct r; eauto.
  Qed.
  
  Lemma iter_lem {X Y RY} {_ : Equivalenceᵢ RY} (f : X ⇒ᵢ itree E (X +ᵢ Y)) (g : X ⇒ᵢ itree E Y)
                 (H : forall i x, it_eq RY (g i x) (bind (f i x) (fun _ r => go (match r with
                                                  | inl x => TauF (g _ x)
                                                  | inr y => RetF y end))))
                 : forall i x, it_eq RY (g i x) (iter f i x).
  Proof.
    unfold it_eq; coinduction R CIH; intros i x.
    apply (bt_tbt (it_eq_map E RY)).
    etransitivity.
    now unshelve eapply (Hbody (it_eq_t E RY) _ _ _ _ _ _ (H i x)).
    etransitivity; cycle 1.
    symmetry; now unshelve eapply (Hbody (it_eq_t E RY) _ _ _ _ _ _ (iter_unfold f)).
    eapply (it_eq_up2bind_t (eqᵢ (X +ᵢ Y)) RY).
    econstructor. reflexivity.
    intros ? ? [] ->; econstructor.
    now apply CIH.
    reflexivity.
  Qed.

  Lemma bind_bind_com {X Y Z RZ} {_ : Reflexiveᵢ RZ} {f : X ⇒ᵢ itree E Y} {g : Y ⇒ᵢ itree E Z} {i} {x : itree E X i}
    : it_eq RZ (bind (bind x f) g) (bind x (kcomp f g)).
  Proof.
    revert i x; unfold it_eq; coinduction R CIH; intros i x.
    cbn; destruct (x.(_observe)); eauto.
    destruct ((f i r).(_observe)); eauto.
    destruct ((g i r0).(_observe)); eauto.
  Qed.

  Lemma fmap_bind_com {X Y Z RZ} {_ : Reflexiveᵢ RZ} {f : X ⇒ᵢ Y} {g : Y ⇒ᵢ itree E Z} {i} {x : itree E X i}
    : it_eq RZ (bind (fmap f _ x) g) (bind x (fun i x => g i (f i x))).
  Proof.
    revert i x; unfold it_eq; coinduction R CIH; intros i x.
    cbn; destruct (x.(_observe)); eauto.
    destruct ((g i (f i r)).(_observe)); eauto.
  Qed.

  Lemma bind_fmap_com {X Y Z RZ} {_ : Reflexiveᵢ RZ} {f : X ⇒ᵢ itree E Y} {g : Y ⇒ᵢ Z} {i} {x : itree E X i}
    : it_eq RZ (fmap g _ (bind x f)) (bind x (fun i x => fmap g i (f i x))).
  Proof.
    revert i x; unfold it_eq; coinduction R CIH; intros i x.
    cbn; destruct (x.(_observe)); eauto.
    destruct ((f i r).(_observe)); eauto.
  Qed.

End monad.

#[global] Notation "x >>= f" := (bind x f) (at level 30).
#[global] Notation "f =<< x" := (subst f _ x) (at level 30).
#[global] Notation "f >=> g" := (kcomp f g) (at level 30).

Definition emap {I} {A B : event I I} (F : A ⇒ₑ B) {X} : itree A X ⇒ᵢ itree B X :=
  cofix _emap _ u :=
      go (match u.(_observe) with
         | RetF r => RetF r
         | TauF t => TauF (_emap _ t)
         | VisF e k => VisF (F.(ea_qry) e)
                           (fun r => _emap _ (rew (F.(ea_nxt)) in k (F.(ea_rsp) r)))
         end).


Lemma subst_subst {I} {E : event I I} {X Y Z} (f : Y ⇒ᵢ itree E Z) (g : X ⇒ᵢ itree E Y) {i} (x : itree E X i)
      : ((x >>= g) >>= f) ≊ (x >>= (g >=> f)) .
Proof.
  revert i x; unfold it_eq; coinduction R CIH; intros i x; cbn.
  destruct (_observe x); eauto.
  destruct (_observe (g i r)); eauto.
  destruct (_observe (f i r0)); eauto.
Qed.
