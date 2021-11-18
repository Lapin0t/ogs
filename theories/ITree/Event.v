Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

From ExtLib.Data Require Import List.
Require Import OGS.Utils.
Require Import OGS.ITree.Cat.

(** Events in ITree parlance (that is the specification of an
    effectful interface). Or in category-theory parlance, an encoding
    of polynomial functors (here in dependent variant: polynomial
    functors from/to presheaf categories). Or in Strathclyde parlance,
    indexed-containers.
*)
Record event (I J : Type) : Type := Event {
  qry : J -> Type ;
  rsp {j} : qry j -> Type ;
  nxt {j} (q : qry j) : rsp q -> I
}.

(** Interpretation of events as functors. *)
Definition evalₑ {I J} (E : event I J) : psh I -> psh J :=
  fun X i => { q : qry E i & forall r : rsp E q, X (nxt E q r) }.
Notation "⟦ E ⟧" := (evalₑ E) (at level 20).
Definition visₑ {I J} {E : event I J} {X i} q k : ⟦ E ⟧ X i := q ,' k.
Arguments visₑ {I J E X i} q k.

Instance FunctorEvent {I J} (E : event I J) : Functor (⟦ E ⟧).
  econstructor; intros x y f i [e k].
  exact (visₑ e (fun r => f _ (k r))).
Defined.

(** Morphisms between events. Because we can, we encode them in a two staged
    process: here we define "pre-morphisms" between an event and a functor.
    A morphism between events A and B will then be a pre-morphism between
    A and the interpretation of B.
*)
Definition arrowₑ {I J : Type} (E : event I J) (F : psh I -> psh J) : Type :=
  forall j (q : E.(qry) j), F (fiber (E.(nxt) q)) j.
Notation "E ⤳ₑ F" := (arrowₑ E F) (at level 30).
Notation "E ⇒ₑ F" := (arrowₑ E (⟦ F ⟧)) (at level 30).

(** Interpretation of events into functors is itself a functor. That is
    we can transform an event (pre-)morphism into a natural transformation between
    the interpretations.
*)
Definition evalₑ_arrow {I J} {E : event I J} {F : psh I -> psh J} {FF : Functor F}
           : E ⤳ₑ F -> ⟦ E ⟧ ⇒ₙ F :=
  fun m _ _ x => fib_into _ (projT2 x) <$> m _ (projT1 x).
Arguments evalₑ_arrow {I J E F FF} m X.
Notation "⟦⇒ m ⟧ X" := (evalₑ_arrow m X) (at level 30).

(** This is an inverse function for evalₑ_arrow: every natural transformation
    between interpretations of events arises from an event-morphism.
    Proofs that this function is indeed an inverse require parametricity theorems
    which afaik are not provable in Coq.
    In other words, the functor ⟦-⟧ : event I → endo (psh I) is fully-faithfull.
*)
Definition e_arrow_mk {I J} {E : event I J} {F} : ⟦ E ⟧ ⇒ₙ F -> E ⤳ₑ F :=
  fun m i q => m (fiber (nxt E q)) _ (existT _ q Fib).


(** Alternate unrolled definition of 'E ⇒ₑ F'. This definition is the one that
    is usually taken, in the spirit of indexed-containers. *)
Record arrowₑ' {I J : Type} (E F : event I J) := EArrow {
  EA_qry {j} : qry E j -> qry F j ;
  EA_rsp {j} (q : qry E j) : rsp F (EA_qry q) -> rsp E q ;
  EA_coh {j} (q : qry E j) r : nxt E q (EA_rsp q r) = nxt F (EA_qry q) r
}.
Notation "E ⇒'ₑ F" := (arrowₑ' E F) (at level 30).

Definition arrowₑ'_to_arrowₑ {I J} {E F : event I J} (m : E ⇒'ₑ F) : E ⇒ₑ F :=
  fun j q => visₑ (EA_qry m q) (fun r => fib_constr _ _ (EA_coh m q r)).

Definition arrowₑ_to_arrow'ₑ {I J} {E F : event I J} (m : E ⇒ₑ F) : E ⇒'ₑ F :=
  EArrow (fun j q => projT1 (m j q))
         (fun j q r => fib_extr (projT2 (m j q) r))
         (fun j q r => fib_coh (projT2 (m j q) r)).


(************************)
(* non-dependent events *)
Module NonDep.

Definition lower (F : psh T1 -> psh T1) (X : Type) : Type := F (fun _ => X) T1_0.
Definition lift (F : Type -> Type) (X : psh T1) : psh T1 := fun _ => F (X T1_0).

Definition event : Type := event T1 T1.

Definition Event (S : Type) (A : S -> Type) : event :=
  Event (fun _ => S) (fun _ s => A s) (fun i _ _ => i).
Arguments Event : clear implicits.
Definition qry (E : event) : Type := E.(qry) T1_0.
Definition rsp (E : event) : qry E -> Type := E.(rsp).
Definition nxt (E : event) (q : qry E) r : E.(nxt) q r = T1_0 :=
  match E.(nxt) q r with T1_0 => eq_refl end.

Notation "⟦ E ⟧ X" := (lower (⟦ E ⟧) X) (at level 30).

Definition arrowₑ (E : event) (F : Type -> Type) : Type := forall q, F (rsp E q).
Notation "E ⇒ₑ F" := (arrowₑ E F) (at level 30).

End NonDep.

Notation "⟦₀ E ⟧ X" := (NonDep.lower (⟦ E ⟧) X) (at level 30).
Notation "E ⇒₀ F" := (NonDep.arrowₑ E F) (at level 30).
  

(***************************)
(* constructions on events *)

(** `event` is a bifunctor `Type ⊗ Typeᵒᵖ → Type` with the following two actions,
    that reindex on the input and the output. *)
Definition liftₑ_r {I J K} (f : K -> J) (E : event I J) : event I K :=
  Event (E.(qry) ∘ f) (fun _ => E.(rsp)) (fun _ => E.(nxt)).
Definition liftₑ_l {I J K} (f : I -> K) (E : event I J) : event K J :=
  Event E.(qry) (fun _ => E.(rsp)) (fun _ q => f ∘ E.(nxt) q).

Notation "E <ₑ f" := (liftₑ_r f E) (at level 30).
Notation "f >ₑ E" := (liftₑ_l f E) (at level 30).


(** event coproduct *)
Definition sumₑ {I J : Type} (E F : event I J) : event I J :=
  Event (E.(qry) +ᵢ F.(qry))
        (fun _ q => match q with
                 | inl q => E.(rsp) q
                 | inr q => F.(rsp) q
                 end)
        (fun _ q => match q as q
                 return match q with
                         | inl q => E.(rsp) q
                         | inr q => F.(rsp) q
                         end -> I
                 with
                 | inl q => E.(nxt) q
                 | inr q => F.(nxt) q
                 end).
Notation "E +ₑ F" := (sumₑ E F) (at level 30).

Definition inlₑ {I J} {E F : event I J} : E ⇒ₑ (E +ₑ F) :=
  fun _ q => existT _ (inl q) Fib.
Definition inrₑ {I J} {E F : event I J} : F ⇒ₑ (E +ₑ F) :=
  fun _ q => existT _ (inr q) Fib.


(** null event *)
Definition voidₑ {I J : Type} : event I J :=
  Event (fun _ => T0) (fun _ q => match q with end) (fun _ q => match q with end).
Notation "∅ₑ" := (voidₑ).
Definition elimₑ {I J} {E : event I J} : voidₑ ⇒ₑ E := fun _ q => match q with end.

(** unit event *)
Definition unitₑ {I : Type} : event I I :=
  Event (fun _ => T1) (fun _ _ => T1) (fun i _ _ => i).
Notation "1ₑ" := (unitₑ).

(* translate a event from deepspec-itree form to trivially indexed form *)
Definition classicₑ (E : Type -> Type) : NonDep.event :=
  NonDep.Event { X : Type & E X } (@projT1 _ _).

Definition e_of_classic {E : Type -> Type} {X} : E X -> ⟦₀ classicₑ E ⟧ X.
  refine (fun e => (X ,' e) ,' _).
  refine (fun x => x).
Defined.

Record uniformₑ (I J : Type) : Type := UEvent {
  u_qry : J -> Type ;
  kon : Type ;
  u_rsp {j} : u_qry j -> list kon ;
  k_rsp : kon -> Type ;
  k_nxt {k} : k_rsp k -> I
}.
Arguments UEvent {I J} u_qry kon u_rsp k_rsp k_nxt.

(* every event is actually uniform, taking kon := {j : J & qry E j } *)
Definition event_uniform {I J} (E : event I J) : uniformₑ I J :=
  UEvent (qry E)
         ({ j : J & qry E j})
         (fun j q => (j ,' q) :: nil)
         (fun k => rsp E (projT2 k))
         (fun k r => nxt E (projT2 k) r).

(* embedding uniform events into usual events *)
Definition e_of_u {I J} (U : uniformₑ I J) : event I J :=
  Event (u_qry U)
        (fun _ q => { i : _ & k_rsp U (u_rsp U q .[i]) })
        (fun _ q r => k_nxt U (projT2 r)).
Coercion e_of_u : uniformₑ >-> event.
