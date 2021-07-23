From OGS Require Import Utils Ctx CatD EventD ITreeD RecD AngelicD EqD.
From ExtLib.Data Require Import Nat Fin List Unit.
Set Primitive Projections.
Set Implicit Arguments.
Set Equations Transparent.

(* taking the "OGS" of an uniform event *)
Definition ogs {I J} (U : uniform_event I J)
           : event (I * list (kon U)) (J * list (kon U)) :=
  Event (fun '(j , ks) => u_qry U j)
        (fun '(j , ks) q => { i : _ & k_rsp U ((u_rsp U q ++ ks) .[i]) })
        (fun '(j , ks) q r => (k_nxt U (projT2 r) , u_rsp U q ++ ks)).

Definition ogs_conf {I} {U : uniform_event I I}
             (X : I -> Type) (ks : list (kon U)) : Type :=
  dvec (fun k => forall r : k_rsp U k, X (k_nxt U r)) ks.

Definition ogs_emb {I} {U : uniform_event I I} {X : I -> Type}
           : forall {i ks},
             ogs_conf (itree U X) ks
           -> itree U X i
           -> itree (ogs U) (X ∘ fst) (i , ks) :=
  cofix _ogs_emb i ks c x := match (observe x) with
    | RetF x => Ret (x : X (fst (i , ks)))
    | TauF t => Tau (_ogs_emb i ks c t)
    | VisF e k => Vis (e : qry (ogs U) (i , ks)) (fun r =>
                   let c' := d_concat _ _ c (curry2' k) in
                   _ogs_emb _ _ c' (d_get _ c' _ _))
    end.

Lemma sigT_eq_lem {A : Type} {B : A -> Type} {C : forall a, B a -> Type}
      {a : A} {k0 k1 : forall b, C a b}
      : (a ,& k0 : sigT (fun a => forall b, C a b)) = (a ,& k1)
        -> forall b, k0 b = k1 b.
  intros e b.
  pose (h1 := projT2_eq e); cbn in h1; rewrite<- h1.
  apply (@f_equal (forall b, C a b) (C a b) (fun k => k b)).
  exact (Eqdep.Eq_rect_eq.eq_rect_eq _ a (fun a => forall b, C a b) k0 (projT1_eq e)).
Qed.
    
                 

From OGS Require Import EqD.
From Paco Require Import paco.

Definition eutt_conf {I} {U : uniform_event I I} {X ks}
           : ogs_conf (itree U X) ks -> ogs_conf (itree U X) ks -> Prop :=
  fun c0 c1 => forall i (r : k_rsp U (ks .[i])), d_get ks c0 i r ≈ d_get ks c1 i r.

Lemma ogs_sound0 {I} {U : uniform_event I I} {X i ks}
        (c0 c1 : ogs_conf (itree U X) ks) (a b : itree U X i)
        : ogs_emb c0 a ≈ ogs_emb c1 b -> a ≈ b.
  revert i ks c0 c1 a b.
  pcofix CIH.
  intros i ks c0 c1 a b h.
  pstep. punfold h.
  red in h |- *.
  remember (observe (ogs_emb c0 a)) as x.
  remember (observe (ogs_emb c1 b)) as y.
  hinduction h before r;
    pclearbot;
    intros CIH c0 c1 a b Ha Hb;
    cbv [ observe ogs_emb ] in Ha, Hb |- * .
  + destruct (_observe a); try discriminate Ha.
    destruct (_observe b); try discriminate Hb.
    econstructor.
    injection Ha as <-; injection Hb as <-; auto.
  +  destruct (_observe a); try discriminate Ha.
    destruct (_observe b); try discriminate Hb.
    econstructor; right.
    apply (CIH i ks c0 c1).
    cbv [ ogs_emb observe]; cbn.
    injection Ha as <-; injection Hb as <-; auto.
  +  destruct (_observe a); try discriminate Ha.
    destruct (_observe b); try discriminate Hb.
    injection Ha as <- Ha1; injection Hb as <- Hb1.
    econstructor; intro v; right.
    apply (CIH _ _ (d_concat ks _ c0 (fun a b => k (a ,& b)))
                   (d_concat ks _ c1 (fun a b => k0 (a ,& b)))).
    pose (Ha2 := sigT_eq_lem Ha1);
    admit. (* TODO *)
  + destruct (_observe a); try discriminate Ha.
    econstructor; auto.
    enough (Hcut : _) by apply (IHh CIH c0 c1 t b Hcut Hb).
    f_equal; injection Ha as Ha; exact Ha.
  + destruct (_observe b); try discriminate Hb.
    econstructor; auto.
    enough (Hcut : _) by apply (IHh CIH c0 c1 a t Ha Hcut).
    f_equal; injection Hb as Hb; exact Hb.
Admitted.

Lemma ogs_sound1 {I} {U : uniform_event I I} {X i ks}
        (c0 c1 : ogs_conf (itree U X) ks) (a b : itree U X i)
        : ogs_emb c0 a ≈ ogs_emb c1 b -> eutt_conf c0 c1.
  intros H n.
  induction ks.
  apply (fin0_elim n).
  destruct c0 as [c0 cs0 ].
  destruct c1 as [c1 cs1 ].
  destruct (fin_case n) as [Hn | [ n' Hn ] ].
  + rewrite Hn; cbn.
    admit. (* TODO *)
  + rewrite Hn; cbn.
    unshelve eapply (IHks cs0 cs1 _ n').
    clear IHks n Hn.
    admit. (* TODO *)
Admitted.

Theorem ogs_sound {I} {U : uniform_event I I} {X i ks}
        (c0 c1 : ogs_conf (itree U X) ks) (a b : itree U X i)
        : ogs_emb c0 a ≈ ogs_emb c1 b -> eutt_conf c0 c1 /\ a ≈ b.
  intro H; split.
  apply (ogs_sound1 c0 c1 a b H).
  apply (ogs_sound0 c0 c1 a b H).
Qed.

Theorem ogs_complete {I} {U : uniform_event I I} {X i ks}
        (c0 c1 : ogs_conf (itree U X) ks) (a b : itree U X i)
        : (a ≈ b) -> eutt_conf c0 c1 -> ogs_emb c0 a ≈ ogs_emb c1 b.
  revert i ks c0 c1 a b.
  pcofix CIH.
  intros i ks c0 c1 a b H0 H1.
  pstep; punfold H0.
  red in H0, H1 |- *.
  cbv [ observe ] in H0.
  cbv [ ogs_emb observe ]; cbn.
  remember (_observe a) as x.
  remember (_observe b) as y.
  hinduction H0 before r; intros CIH ks c0 c1 a b Ha Hb H1.
  + econstructor; eauto.
  + econstructor. right.
    destruct (_observe a); try discriminate Ha.
    destruct (_observe b); try discriminate Hb.
    enough (Hcut : _) by apply (CIH i ks c0 c1 m1 m2 Hcut H1).
    destruct REL; [eauto | destruct H ].
  + econstructor; intros [ci cr]; right.
    destruct (_observe a); try discriminate Ha.
    destruct (_observe b); try discriminate Hb.
    pose (c0' :=  (d_concat ks (u_rsp U e) c0 (fun a0 b0 => k1 (a0,& b0)))).
    pose (c1' :=  (d_concat ks (u_rsp U e) c1 (fun a0 b0 => k2 (a0,& b0)))).
    enough (H2 : eutt_conf c0' c1') by apply (CIH _ _ c0' c1' _ _ (H2 ci cr) H2).
    admit. (* TODO *)
  + apply EqTauL; auto.
    destruct (_observe a); try discriminate Ha.
    enough (Hcut : _) by apply (IHeqitF CIH ks c0 c1 t b Hcut Hb H1).
    injection Ha as ->; auto.
  + econstructor; auto.
    destruct (_observe b); try discriminate Hb.
    enough (Hcut : _) by apply (IHeqitF CIH ks c0 c1 a t Ha Hcut H1).
    injection Hb as ->; auto.
Admitted.
