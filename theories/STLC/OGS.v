(*|
==========================
Operational Game Semantics
==========================

.. coq:: none
|*)
From Coq Require Import JMeq Program.Equality EqdepFacts.
From OGS Require Import Utils Ctx CatD EventD ITreeD RecD AngelicD EqD.
From ExtLib.Data Require Import Nat Fin List Unit.
From Paco Require Import paco.
Set Primitive Projections.
Set Implicit Arguments.
Set Equations Transparent.

(*|
An uniform event is one where the set of answers for a given query is
of the form ``list kon`` for some type ``kon``. We argue that the gist
of an OGS is the ability for the opponent to remember all the
continuations that have been offered, and continue not only on the continuations
that have been offered at the last event, but also on all the previous ones.

Hence the OGS of an uniform event will be indexed by an additional
``ks : list kon`` representing the list of currently available continuations
and the set of responses will be the choice of a continuation in the concatenation
of the new continuations available and the ones present in the context.
|*)
Definition ogs {I J} (U : uniform_event I J)
           : event (I * list (kon U)) (J * list (kon U)) :=
  Event (fun '(j , ks) => u_qry U j)
        (fun '(j , ks) q => { i : _ & k_rsp U ((u_rsp U q ++ ks) .[i]) })
        (fun '(j , ks) q r => (k_nxt U (projT2 r) , u_rsp U q ++ ks)).

(*|
An OGS configuration ``c : ogs_conf X ks`` is a forest of ``itree U
X``, that has a tree for each ``ks``.
|*)
Definition ogs_conf {I} {U : uniform_event I I}
             (X : I -> Type) (ks : list (kon U)) : Type :=
  ffun (fun k => forall r : k_rsp U k, itree U X (k_nxt U r)) ks.

(*|
Given an OGS configuration containing itrees (eg a forest of itrees
explaining how to continue for every continuation in scope), and an
itree over ``U``, we can generate an itree over ``ogs U``.
|*)
Definition ogs_emb {I} {U : uniform_event I I} {X : I -> Type}
           : forall {i ks},
             ogs_conf X ks
           -> itree U X i
           -> itree (ogs U) (X ∘ fst) (i , ks) :=
  cofix _ogs_emb i ks c x := match (observe x) with
    | RetF x => Ret (x : X (fst (i , ks)))
    | TauF t => Tau (_ogs_emb i ks c t)
    | VisF e k => Vis (e : qry (ogs U) (i , ks)) (fun r =>
                   let c' := ffconcat_pi _ _ c k in
                   _ogs_emb _ _ c' (ffun_pi_get c' r))
    end.

(*|
Here is a short lemma injecting a query for ``U`` into a query for ``ogs U``.
|*)
Definition ogs_inj_rsp {I} {U : uniform_event I I} {i ks} {q : qry U i}
          (r : rsp U q) : rsp (ogs U) (q : qry (ogs U) (i , ks)) :=
  finj _ ,& eq_rect _ (k_rsp U) (projT2 r) _ (finj_get (projT1 r)).

(*|
Next is a definition of eutt lifted to our type of forests: two forests are eutt
if they are pointwise eutt.
|*)
Definition eutt_conf {I} {U : uniform_event I I} {X ks}
           : ogs_conf X ks -> ogs_conf X ks -> Prop :=
  fun c0 c1 => forall i (r : k_rsp U (ks .[i])), ffapp c0 i r ≈ ffapp c1 i r.

(*|
The soundness theorem: if the OGS embedding of two itrees are eutt, then the
trees are themselves eutt. The proof is very direct: by coinduction we pattern
match on the proof, destructing and discriminating everything to expose the forced
constructors (like the kind of clause-based dependent induction that coq-equation
does). The case for Vis is currently not finished, there are still some dependent
equality rewriting shenanigans.
|*)
Theorem ogs_sound {I} {U : uniform_event I I} {X i ks}
        {c0 c1 : ogs_conf X ks} {a b : itree U X i}
        (H : ogs_emb c0 a ≈ ogs_emb c1 b) : a ≈ b.
  revert i ks c0 c1 a b H.
  pcofix CIH.
  intros i ks c0 c1 a b H.
  pstep. punfold H.
  red in H |- *.
  remember (observe (ogs_emb c0 a)) as x.
  remember (observe (ogs_emb c1 b)) as y.
  hinduction H before r;
    pclearbot;
    intros CIH c0 c1 a b Ha Hb;
    cbv [ observe ogs_emb ] in Ha, Hb |- *; cbn [ rsp ogs ] in Ha, Hb;
    change (Tau (_ i ks ?c ?t)) with (Tau (ogs_emb c t)) in Ha, Hb;
    change (_ (k_nxt U (projT2 _)) (ks +▶ u_rsp U _)%ctx ?c ?r)
      with (ogs_emb c r) in Ha, Hb.
  + destruct (_observe a); try discriminate Ha.
    destruct (_observe b); try discriminate Hb.
    econstructor.
    injection Ha as <-; injection Hb as <-; auto.
  + destruct (_observe a); try discriminate Ha.
    destruct (_observe b); try discriminate Hb.
    econstructor; right.
    apply (CIH i ks c0 c1).
    cbn [_observe] in Ha, Hb.
    injection Ha as <-; injection Hb as <-; auto.
  + destruct (_observe a); try discriminate Ha.
    destruct (_observe b); try discriminate Hb.
    cbn [_observe] in Ha, Hb.
    injection Ha as <- Ha; injection Hb as <- Hb.
    econstructor; intros v; right.
    apply (CIH _ _ (ffconcat_pi ks _ c0 k)
                   (ffconcat_pi ks _ c1 k0)); clear CIH.
    dependent induction Ha.
    dependent induction Hb.
    specialize (REL (ogs_inj_rsp v)).
    cbn in REL.
    unfold eutt, eqit.
    (*
    cbn [projT1 projT2 ogs_inj_rsp uncurry2'] in REL.
    cbn [uncurry2'] in REL.
    *)
    admit.
  + destruct (_observe a); try discriminate Ha.
    econstructor; auto.
    enough (Hcut : _) by apply (IHeqitF CIH c0 c1 t b Hcut Hb).
    f_equal; injection Ha as Ha; exact Ha.
  + destruct (_observe b); try discriminate Hb.
    econstructor; auto.
    enough (Hcut : _) by apply (IHeqitF CIH c0 c1 a t Ha Hcut).
    f_equal; injection Hb as Hb; exact Hb.
Admitted.


(*|
The completeness result: given two eutt trees and two pointwise eutt forests,
the OGS embedding are eutt. Again this is a direct proof by coinduction and
pattern matching on the proofs.
|*)
Theorem ogs_complete {I} {U : uniform_event I I} {X i ks}
        (c0 c1 : ogs_conf X ks) (a b : itree U X i)
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
    pose (c0' :=  (ffconcat ks (u_rsp U e) c0 (fun a0 b0 => k1 (a0,& b0)))).
    pose (c1' :=  (ffconcat ks (u_rsp U e) c1 (fun a0 b0 => k2 (a0,& b0)))).
    enough (Hcut : eutt_conf c0' c1')
      by apply (CIH _ _ c0' c1' _ _ (Hcut ci cr) Hcut).
    clear ci cr.
    injection Ha as <- Ha.
    injection Hb as <- Hb.
    unfold eutt_conf.
    enough (Hcut : _)
      by eapply (d_concat_lem (fun _ (f0 : forall r, _) (f1 : forall r, _) => forall r, f0 r ≈ f1 r)
                  ks (u_rsp U e) c0 c1
                  (fun a0 b0 => k1 (a0 ,& b0)) (fun a0 b0 => k2 (a0 ,& b0))
                  H1 Hcut).
    intros ci cr.
    destruct (REL (ci ,& cr)); [ auto | destruct H ].
  + econstructor; auto.
    destruct (_observe a); try discriminate Ha.
    enough (Hcut : _) by apply (IHeqitF CIH ks c0 c1 t b Hcut Hb H1).
    injection Ha as ->; auto.
  + econstructor; auto.
    destruct (_observe b); try discriminate Hb.
    enough (Hcut : _) by apply (IHeqitF CIH ks c0 c1 a t Ha Hcut H1).
    injection Hb as ->; auto.
Qed.
