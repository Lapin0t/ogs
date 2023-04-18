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

  Definition subst {X Y} (f : X ⇒ᵢ itree E Y) : itree E X ⇒ᵢ itree E Y :=
    cofix _subst _ u :=
      go (match u.(_observe) with
         | RetF r => (f _ r).(_observe)
         | TauF t => TauF (_subst _ t)
         | VisF e k => VisF e (fun r => _subst _ (k r))
         end).

  Definition bind {X Y i} x f := @subst X Y f i x.

  Definition kcomp {X Y Z} (f : X ⇒ᵢ itree E Y) (g : Y ⇒ᵢ itree E Z) : X ⇒ᵢ itree E Z :=
    fun i x => bind (f i x) g.

  Definition iter {X Y} (f : X ⇒ᵢ itree E (X +ᵢ Y)) : X ⇒ᵢ itree E Y :=
    cofix _iter _ x :=
      bind (f _ x) (fun _ r => go (match r with
                                | inl x => TauF (_iter _ x)
                                | inr y => RetF y end)) .

  Variant bindR {X Y} (R : relᵢ (itree E X) (itree E X)) (S : relᵢ (itree E Y) (itree E Y))
          : relᵢ (itree E Y) (itree E Y) :=
    | BindR {i t1 t2 k1 k2}
        (u : R i t1 t2)
        (v : forall i x, S i (k1 i x) (k2 i x))
      : bindR R S i (bind t1 k1) (bind t2 k2).
  Arguments BindR {X Y R S i t1 t2 k1 k2}.    

  Program Definition bindR_map {X Y} : mon (relᵢ (itree E Y) (itree E Y)) :=
    {| body S := bindR (@it_eq _ E X) S ;
       Hbody _ _ H _ _ _ '(BindR u v) := BindR u (fun i x => H _ _ _ (v i x)) |}.

  Lemma it_eq_up2bind_t {X Y} : @bindR_map X Y <= it_eq_t E Y.
  Proof.
    apply Coinduction; intros R i x y [ ? ? ? ? ? u v].
    unfold it_eq in u; apply (gfp_fp (it_eq_map E X)) in u.
    cbn in *; cbv [observe] in u.
    dependent destruction u; simpl_depind.
    - refine (it_eqF_mon _ _ (id_T _ _ R) _ _ _ (v i0 r)).
    - econstructor; apply (fTf_Tf (it_eq_map E Y)).
      refine (BindR t_rel (fun i r => b_T (it_eq_map E Y) _ _ _ _ _ (v i r))).
    - econstructor; intros r; apply (fTf_Tf (it_eq_map E Y)).
      refine (BindR (k_rel r) (fun i r => b_T (it_eq_map E Y) _ _ _ _ _ (v i r))).
  Qed.

  Lemma iter_unfold {X Y} (f : X ⇒ᵢ itree E (X +ᵢ Y)) {i x}
    : it_eq
        (iter f i x)
        (bind (f i x) (fun _ r => go (match r with
                                   | inl x => TauF (iter f _ x)
                                   | inr y => RetF y end))).
  Proof.
    apply (gfp_fp (it_eq_map E Y)).
    cbn; destruct (_observe (f i x)); auto.
    destruct r; auto.
  Qed.
  
  Lemma iter_lem {X Y} (f : X ⇒ᵢ itree E (X +ᵢ Y)) (g : X ⇒ᵢ itree E Y)
                 (H : forall i x, it_eq (g i x) (bind (f i x) (fun _ r => go (match r with
                                                  | inl x => TauF (g _ x)
                                                  | inr y => RetF y end))))
                 : forall i x, it_eq (g i x) (iter f i x).
  Proof.
    unfold it_eq; coinduction R CIH; intros i x.
    apply (bt_tbt (it_eq_map E Y)).
    etransitivity.
    now unshelve eapply (Hbody (it_eq_t E Y) _ _ _ _ _ _ (H i x)).
    etransitivity.
    all: cycle 1.
    symmetry.
    now unshelve eapply (Hbody (it_eq_t E Y) _ _ _ _ _ _ (iter_unfold f)).
    eapply (@it_eq_up2bind_t (X +ᵢ Y) Y).
    econstructor. reflexivity.
    intros ? []; econstructor.
    now apply CIH.
  Qed.

  Lemma bind_bind_com {X Y Z} {f : X ⇒ᵢ itree E Y} {g : Y ⇒ᵢ itree E Z} {i} {x : itree E X i}
    : it_eq (bind (bind x f) g) (bind x (kcomp f g)).
  Proof.
    revert i x; unfold it_eq; coinduction R CIH; intros i x.
    cbn; destruct (x.(_observe)).
    - destruct ((f i r).(_observe)).
      + destruct ((g i r0).(_observe)); econstructor; reflexivity.
      + econstructor; reflexivity.
      + econstructor; reflexivity.
    - econstructor; apply CIH.
    - econstructor; intro r; apply CIH.
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
