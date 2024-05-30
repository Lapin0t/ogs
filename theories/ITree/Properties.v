(*|
Interaction Trees: Theory of the structure
==========================================

We collect in these file the main lemmas capturing the applicative,
monadic, and iterative structure of itrees.

.. coq:: none
|*)
From Coinduction Require Import coinduction tactics.

From OGS Require Import Prelude.
From OGS.Utils Require Import Rel.
From OGS.ITree Require Import Event ITree Structure Eq.
(*|
|*)
Section withE.
  Context {I} {E : event I I}.
(*|
``fmap`` respects strong bisimilarity.
|*)
  #[global] Instance fmap_eq {X RX Y RY} :
    Proper (dpointwise_relation (fun i => RX i ==> RY i)
              ==> dpointwise_relation (fun i => it_eq RX (i:=i) ==> it_eq RY (i:=i)))
      (@fmap I E X Y).
  Proof.
    intros f g H1.
    unfold respectful, dpointwise_relation, it_eq.
    coinduction R CIH; intros i x y h.
    apply (gfp_fp (it_eq_map E RX)) in h.
    cbn in *; cbv [observe] in h; dependent destruction h; simpl_depind; eauto.
    econstructor; now apply H1.
  Qed.
(*|
``fmap`` respects weak bisimilarity.
|*)
  #[global] Instance fmap_weq {X RX Y RY} :
    Proper (dpointwise_relation (fun i => RX i ==> RY i)
              ==> dpointwise_relation (fun i => it_wbisim RX i ==> it_wbisim RY i))
      (@fmap I E X Y).
  Proof.
    intros f g H1.
    unfold respectful, dpointwise_relation, it_wbisim.
    coinduction R CIH; intros i x y h.
    apply (gfp_fp (it_wbisim_map E RX)) in h.
    cbn in *; cbv [observe] in h. destruct h.
    dependent destruction rr.
    - unshelve econstructor.
      + exact (RetF (f i r0)).
      + exact (RetF (g i r3)).
      + clear - r1; remember (_observe x) as ot; clear Heqot x.
        dependent induction r1; econstructor.
        exact (IHr1 Y f r0 eq_refl).
      + clear - r2; remember (_observe y) as ot; clear Heqot y.
        dependent induction r2; econstructor.
        exact (IHr2 Y g r3 eq_refl).
      + econstructor.
        now apply H1.
    - unshelve econstructor.
      + exact (TauF (f <$> t1)).
      + exact (TauF (g <$> t2)).
      + clear - r1; remember (_observe x) as ot; clear Heqot x.
        dependent induction r1; econstructor.
        exact (IHr1 Y f t1 eq_refl).
      + clear - r2; remember (_observe y) as ot; clear Heqot y.
        dependent induction r2; econstructor.
        exact (IHr2 Y g t2 eq_refl).
      + econstructor.
        now apply CIH.
    - unshelve econstructor.
      + exact (VisF q (fun r => f <$> k1 r)).
      + exact (VisF q (fun r => g <$> k2 r)).
      + clear - r1; remember (_observe x) as ot; clear Heqot x.
        dependent induction r1; econstructor.
        exact (IHr1 Y f q k1 eq_refl).
      + clear - r2; remember (_observe y) as ot; clear Heqot y.
        dependent induction r2; econstructor.
        exact (IHr2 Y g q k2 eq_refl).
      + econstructor.
        intro r; now apply CIH.
  Qed.
(*|
``subst`` respects weak bisimilarity.
|*)
  #[global] Instance subst_eq {X Y} {RX : relᵢ X X} {RY : relᵢ Y Y} :
    Proper (dpointwise_relation (fun i => RX i ==> it_eq RY (i:=i))
              ==> dpointwise_relation (fun i => it_eq RX (i:=i) ==> it_eq RY (i:=i)))
      (@subst I E X Y).
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
(*|
A slight generalization of the monad law ``t ≊ t >>= η``.
|*)
  Lemma bind_ret {X Y} {RX : relᵢ Y Y} {_ : Reflexiveᵢ RX} (f : X ⇒ᵢ Y) {i}
    (t : itree E X i)
    : it_eq RX (fmap f i t) (bind t (fun i x => Ret' (f i x))).
  Proof.
    revert i t; unfold it_eq; coinduction R CIH; intros i t.
    cbn; destruct (_observe t); auto.
  Qed.

  #[global] Instance subst_eat {X Y} (f : X ⇒ᵢ itree E Y) {i} :
    Proper (it_eat' i ==> it_eat' i) (subst f i).
  Proof.
    intros ? ? H; unfold it_eat' in *; cbn.
    remember (_observe x) as _x eqn:Hx; clear Hx.
    remember (_observe y) as _y eqn:Hy; clear Hy.
    dependent induction H; now econstructor.
  Qed.
(*|
Composition law of ``bind``.
|*)
  Lemma bind_bind_com {X Y Z RZ} `{Reflexiveᵢ RZ}
    {f : X ⇒ᵢ itree E Y} {g : Y ⇒ᵢ itree E Z} {i} {x : itree E X i} :
    it_eq RZ (bind (bind x f) g) (bind x (kcomp f g)).
  Proof.
    revert i x; unfold it_eq; coinduction R CIH; intros i x.
    cbn; destruct (x.(_observe)); eauto.
    destruct ((f i r).(_observe)); eauto.
    destruct ((g i r0).(_observe)); eauto.
  Qed.
(*|
Composition law of ``fmap``.
|*)
  Lemma fmap_fmap_com {X Y Z RZ} `{Reflexiveᵢ RZ}
    {f : X ⇒ᵢ Y} {g : Y ⇒ᵢ Z} {i} {x : itree E X i} :
    it_eq RZ (fmap g i (fmap f i x)) (fmap (fun i x => g i (f i x)) i x).
  Proof.
    revert i x; unfold it_eq; coinduction R CIH; intros i x.
    cbn; destruct (x.(_observe)); eauto.
  Qed.
(*|
``bind`` and ``fmap`` interaction.
|*)
  Lemma fmap_bind_com {X Y Z RZ} `{Reflexiveᵢ RZ}
    {f : X ⇒ᵢ Y} {g : Y ⇒ᵢ itree E Z} {i} {x : itree E X i} :
    it_eq RZ (bind (fmap f _ x) g) (bind x (fun i x => g i (f i x))).
  Proof.
    revert i x; unfold it_eq; coinduction R CIH; intros i x.
    cbn; destruct (x.(_observe)); eauto.
    destruct ((g i (f i r)).(_observe)); eauto.
  Qed.

  Lemma bind_fmap_com {X Y Z RZ} `{Reflexiveᵢ RZ}
    {f : X ⇒ᵢ itree E Y} {g : Y ⇒ᵢ Z} {i} {x : itree E X i} :
    it_eq RZ (fmap g _ (bind x f)) (bind x (fun i x => fmap g i (f i x))).
  Proof.
    revert i x; unfold it_eq; coinduction R CIH; intros i x.
    cbn; destruct (x.(_observe)); eauto.
    destruct ((f i r).(_observe)); eauto.
  Qed.
(*|
Rewording composition law of ``bind``.
|*)
  Lemma subst_subst {X Y Z}
    (f : Y ⇒ᵢ itree E Z) (g : X ⇒ᵢ itree E Y) {i} (x : itree E X i) :
    ((x >>= g) >>= f) ≊ (x >>= (g >=> f)) .
  Proof. apply bind_bind_com. Qed.
(*|
Proof of the up-to ``bind`` principle: we may close bisimulation candidates by prefixing
related elements by bisimilar computations.
|*)
  Variant bindR {X1 X2 Y1 Y2} (RX : relᵢ X1 X2)
    (R : relᵢ (itree E X1) (itree E X2))
    (S : relᵢ (itree E Y1) (itree E Y2)) :
    relᵢ (itree E Y1) (itree E Y2) :=
    | BindR {i t1 t2 k1 k2}
        (u : R i t1 t2)
        (v : forall i x1 x2, RX i x1 x2 -> S i (k1 i x1) (k2 i x2))
      : bindR RX R S i (t1 >>= k1) (t2 >>= k2).
  Arguments BindR {X1 X2 Y1 Y2 RX R S i t1 t2 k1 k2}.
  Hint Constructors bindR : core.
(*|
Up-to ``bind`` is valid for strong bisimilarity.
|*)
  Program Definition bindR_eq_map {X1 X2 Y1 Y2} (RX : relᵢ X1 X2) : mon (relᵢ (itree E Y1) (itree E Y2)) :=
    {| body S := bindR RX (@it_eq _ E _ _ RX) S ;
       Hbody _ _ H _ _ _ '(BindR u v) := BindR u (fun i _ _ r => H _ _ _ (v i _ _ r)) |}.

  Lemma it_eq_up2bind_t {X1 X2 Y1 Y2} RX RY :
    @bindR_eq_map X1 X2 Y1 Y2 RX <= it_eq_t E RY.
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
(*|
Up-to ``bind`` is valid for weak bisimilarity.
|*)
  Program Definition bindR_w_map {X1 X2 Y1 Y2} (RX : relᵢ X1 X2) : mon (relᵢ (itree E Y1) (itree E Y2)) :=
    {| body S := bindR RX (@it_wbisim _ E _ _ RX) S ;
       Hbody _ _ H _ _ _ '(BindR u v) := BindR u (fun i _ _ r => H _ _ _ (v i _ _ r)) |}.

  Lemma it_wbisim_up2bind_t {X1 X2 Y1 Y2} RX RY :
    @bindR_w_map X1 X2 Y1 Y2 RX <= it_wbisim_t E RY.
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
(*|
Bisimilar equations have bisimilar iteration (weakly and strongly).
|*)
  Lemma iter_cong_strong {X1 X2 Y1 Y2} {RX : relᵢ X1 X2} {RY : relᵢ Y1 Y2}
    f g (_ : forall i a b, RX i a b ->  it_eq (sumᵣ RX RY) (f i a) (g i b)) :
    forall i a b, RX i a b -> it_eq (E:=E) RY (iter f i a) (iter g i b).
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

  #[global] Instance iter_proper_strong {X Y} {RX : relᵢ X X} {RY : relᵢ Y Y} :
    Proper (dpointwise_relation (fun i => RX i ==> it_eq (sumᵣ RX RY) (i:=i))
              ==> dpointwise_relation (fun i => RX i ==> it_eq RY (i:=i)))
      (@iter I E X Y)
    := iter_cong_strong.

  Lemma iter_cong_weak {X1 X2 Y1 Y2} {RX : relᵢ X1 X2} {RY : relᵢ Y1 Y2}
    f g (_ : forall i a b, RX i a b -> it_wbisim (sumᵣ RX RY) i (f i a) (g i b)) :
    forall i a b, RX i a b -> it_wbisim (E:=E) RY i (iter f i a) (iter g i b).
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
        cbn; econstructor.
        now apply CIH.
      * econstructor.
        exact (subst_eat _ _ (Ret' _) r1).
        exact (subst_eat _ _ (Ret' _) r2).
        now cbn; econstructor.
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

  #[global] Instance iter_weq {X Y} {RX : relᵢ X X} {RY : relᵢ Y Y} :
    Proper (dpointwise_relation (fun i => RX i ==> it_wbisim (sumᵣ RX RY) i)
              ==> dpointwise_relation (fun i => RX i ==> it_wbisim RY i))
      (@iter I E X Y)
    := iter_cong_weak.
(*|
Iteration is a strong fixed point of the folowing guarded equation.
|*)
  Lemma iter_unfold {X Y RY} `{Reflexiveᵢ RY} (f : X ⇒ᵢ itree E (X +ᵢ Y)) {i x} :
    it_eq RY
      (iter f i x)
      (bind (f i x) (fun _ r => go (match r with
                                 | inl x => TauF (iter f _ x)
                                 | inr y => RetF y end))).
  Proof.
    apply (gfp_fp (it_eq_map E RY)).
    cbn; destruct (_observe (f i x)); auto.
    destruct r; eauto.
  Qed.
(*|
Iteration is the unique such fixed point w.r.t. strong bisimilarity. Note that this
is again not w.r.t. the initial equation but the alternate one which is trivially
guarded. See example 6.14 in the paper.
|*)
  Lemma iter_uniq {X Y RY} `{Equivalenceᵢ RY}
    (f : X ⇒ᵢ itree E (X +ᵢ Y)) (g : X ⇒ᵢ itree E Y)
    (EQ : forall i x, it_eq RY (g i x) (bind (f i x) (fun _ r => go (match r with
                                                             | inl x => TauF (g _ x)
                                                             | inr y => RetF y end)))) :
    forall i x, it_eq RY (g i x) (iter f i x).
  Proof.
    unfold it_eq; coinduction R CIH; intros i x.
    apply (bt_tbt (it_eq_map E RY)).
    etransitivity.
    now unshelve eapply (Hbody (it_eq_t E RY) _ _ _ _ _ _ (EQ i x)).
    etransitivity; cycle 1.
    symmetry; now unshelve eapply (Hbody (it_eq_t E RY) _ _ _ _ _ _ (iter_unfold f)).
    eapply (it_eq_up2bind_t (eqᵢ (X +ᵢ Y)) RY).
    econstructor. reflexivity.
    intros ? ? [] ->; econstructor.
    now apply CIH.
    reflexivity.
  Qed.
End withE.
(*|
Misc. utilities.
|*)
Variant is_tau' {I} {E : event I I} {X i} : itree' E X i -> Prop :=
  | IsTau {t : itree E X i} : is_tau' (TauF t) .
Definition is_tau {I} {E : event I I} {X i} (t : itree E X i) : Prop := is_tau' t.(_observe).

Variant is_ret' {I} {E : event I I} {X i} : itree' E X i -> Prop :=
  | IsRet {x : X i} : is_ret' (RetF x) .
Definition is_ret {I} {E : event I I} {X i} (t : itree E X i) : Prop := is_ret' t.(_observe).

Definition is_ret_get {I} {E : event I I} {X i} {t : itree E X i} : is_ret t -> X i .
Proof.
  unfold is_ret.
  destruct (_observe t); intro p; try dependent elimination p.
  exact r.
Defined.
