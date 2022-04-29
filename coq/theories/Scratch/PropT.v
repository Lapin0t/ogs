(** * Excerpt taken from Vellvm *)

From Coq Require Import
     Relations
     Morphisms.

From ITree Require Import
     ITree
     Eq.Eq
     Events.Exception
     ITreeFacts.

Require Import Paco.paco.

(* Definition currently used in Vellvm.
     A lot of wiggle room w.r.t. notions of equivalences over it, or even w.r.t
     the definition of its monadic operations.
     It is not quite a monad transformer (bind is not associative to the left)
 *)
Definition PropT (E: Type -> Type) (X: Type): Type :=
  itree E X -> Prop.

Definition eutt_closed {E X} (P: itree E X -> Prop): Prop :=
  Proper (eutt eq ==> iff) P.

Global Polymorphic Instance Eq1_PropT {E} : Eq1 (PropT E) :=
  fun a PA PA' =>
    (forall x y, x ≈ y -> (PA x <-> PA' y)) /\
    eutt_closed PA /\ eutt_closed PA'.

Global Instance Functor_Prop {E}
  : Functor.Functor (PropT E) :=
  {| Functor.fmap := fun A B f PA b => exists (a: itree E A), PA a /\ b = Functor.fmap f a |}.

Inductive Returns {E} {A: Type} (a: A) : itree E A -> Prop :=
| ReturnsRet: forall t, t ≈ Ret a -> Returns a t
| ReturnsTau: forall t u, t ≈ Tau u -> Returns a u -> Returns a t
| ReturnsVis: forall {X} (e: E X) (x: X) t k, t ≈ Vis e k -> Returns a (k x) -> Returns a t
.
Hint Constructors Returns: core.

Inductive interp_PropTF {E F} (h_spec : forall T, E T -> itree F T -> Prop)
          {R : Type} (RR : relation R) (sim : itree E R -> itree F R -> Prop)
  : itree' E R -> itree F R -> Prop := 
| Interp_PropT_Ret : forall r1 r2 (REL: RR r1 r2)
                       (t2 : itree F R)
                       (eq2 : t2 ≈ (Ret r2)),
    interp_PropTF h_spec RR sim (RetF r1) t2

| Interp_PropT_Tau : forall t1 t2 (HS: sim t1 t2), interp_PropTF h_spec RR sim (TauF t1) t2
                                                            
| Interp_PropT_Vis : forall A (e : E A) (k1 : A -> itree E R)
                       (t2 : itree F R)
                       (ta :itree F A)  (k2 : A -> itree F R) (HTA: h_spec A e ta)
                       (eq2 : t2 ≈ (bind ta k2))
                       (HK : forall (a : A), Returns a ta ->  sim (k1 a) (k2 a)), 
    interp_PropTF h_spec RR sim (VisF e k1) t2.

Hint Constructors interp_PropTF : core.

Lemma interp_PropTF_mono E F h_spec R RR  (t0 : itree' E R) (t1 : itree F R) sim sim'
      (IN : interp_PropTF h_spec RR sim t0 t1)
      (LE : sim <2= sim') : 
  (interp_PropTF h_spec RR sim' t0 t1).
Proof.
  induction IN; eauto.
Qed.

Hint Resolve interp_PropTF_mono : paco.

Definition interp_PropT_ E F h_spec R RR sim (t0 : itree E R) (t1 : itree F R) :=
  interp_PropTF h_spec RR sim (observe t0) t1.
Hint Unfold interp_PropT_ : core.

Lemma interp_PropT__mono E F h_spec R RR : monotone2 (interp_PropT_ E F h_spec R RR).
Proof.
  do 2 red. intros. eapply interp_PropTF_mono; eauto.
Qed.
Hint Resolve interp_PropT__mono : paco.  

Definition interp_prop {E F} (h_spec : E ~> PropT F) :
  forall R (RR: relation R), itree E R -> PropT F R :=
  fun R (RR: relation R) =>  paco2 (interp_PropT_ E F h_spec R RR) bot2.

Definition trigger_prop {E} : E ~> PropT E :=
  fun R e => fun t => t = trigger e.

