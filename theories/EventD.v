Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

From OGS Require Import Utils CatD.

Record event (I J : Type) : Type := Event {
  qry : J -> Type ;
  rsp {j} : qry j -> Type ;
  nxt {j} (q : qry j) : rsp q -> I
}.

Definition e_eval {I J} (E : event I J) : psh I -> psh J :=
  fun X i => { q : qry E i & forall r : rsp E q, X (nxt E q r) }.

Notation "⟦ E ⟧" := (e_eval E) (at level 20).
Definition visₑ {I J} {E : event I J} {X i} q k : ⟦ E ⟧ X i := existT _ q k.
Arguments visₑ : clear implicits.
Arguments visₑ {I J E X i} q k.

Instance FunctorEvent {I J} (E : event I J) : Functor (⟦ E ⟧).
  econstructor. intros x y f i [e k].
  exact (visₑ e (fun r => f _ (k r))).
Defined.

(****************)
(* event arrows *)
Definition e_arrow {I J : Type} (E : event I J) (F : psh I -> psh J) : Type :=
  forall j (q : E.(qry) j), F (fiber (E.(nxt) q)) j.

Notation "E ₑ⇒ F" := (e_arrow E F) (at level 30).
Notation "E ⇒ₑ F" := (E ₑ⇒ ⟦ F ⟧) (at level 30).

Definition e_arrow_eval {I J} {E : event I J} {F : psh I -> psh J} {FF : Functor F}
           : E ₑ⇒ F -> ⟦ E ⟧ ⟹ F :=
  fun m _ _ x => fiber_into _ (projT2 x) <$> m _ (projT1 x).
Arguments e_arrow_eval {I J E F FF} m X.
Notation "⟦⇒ m ⟧ X" := (e_arrow_eval m X) (at level 30).

(** inverse of e_arrow_eval, meaning that the functor ⟦-⟧ : event I → endo (psh I)
    is fully-faithfull (i think the proof requires function extensionality
    and parametricity) *)
Definition e_arrow_mk {I J} {E : event I J} {F} : ⟦ E ⟧ ⟹ F -> E ₑ⇒ F :=
  fun m i q => m (fiber (nxt E q)) _ (existT _ q Fib).


(** Alternate unrolled definition of 'E ⇒ₑ F' *)
Record e_arrow' {I J : Type} (E F : event I J) := EArrow {
  EA_qry {j} : qry E j -> qry F j ;
  EA_rsp {j} (q : qry E j) : rsp F (EA_qry q) -> rsp E q ;
  EA_coh {j} (q : qry E j) r : nxt E q (EA_rsp q r) = nxt F (EA_qry q) r
}.
Notation "E ⇒'ₑ F" := (e_arrow' E F) (at level 30).

Definition e_arrow'_to_arrow {I J} {E F : event I J} (m : E ⇒'ₑ F) : E ⇒ₑ F :=
  fun j q => visₑ (EA_qry m q) (fun r => fiber_mk _ _ (EA_coh m q r)).

Definition e_arrow_to_arrow' {I J} {E F : event I J} (m : E ⇒ₑ F) : E ⇒'ₑ F :=
  EArrow (fun j q => projT1 (m j q))
         (fun j q r => fiber_ext (projT2 (m j q) r))
         (fun j q r => fiber_coh (projT2 (m j q) r)).

(************************)
(* non-dependent events *)

Definition lower₀ (F : psh T1 -> psh T1) (X : Type) : Type := F (fun _ => X) t1_0.
Definition lift₀ (F : Type -> Type) (X : psh T1) : psh T1 := fun _ => F (X t1_0).

(* type *)
Definition event₀ : Type := event T1 T1.

(* constructor and projections *)
Definition Event₀ (S : Type) (A : S -> Type) : event₀ :=
  Event (fun _ => S) (fun _ s => A s) (fun i _ _ => i).
Arguments Event₀ : clear implicits.
Definition qry₀ (E : event₀) : Type := E.(qry) t1_0.
Definition rsp₀ (E : event₀) : qry₀ E -> Type := E.(rsp).
Definition nxt₀ (E : event₀) (q : qry₀ E) r : E.(nxt) q r = t1_0 :=
  match E.(nxt) q r with t1_0 => eq_refl end.

Notation "⟦₀ E ⟧ X" := (lower₀ (⟦ E ⟧) X) (at level 30).

Definition e_arrow₀ (E : event₀) (F : Type -> Type) : Type := forall q, F (rsp₀ E q).
Notation "E ₑ⇒₀ F" := (e_arrow₀ E F) (at level 30).
  

(***************************)
(* constructions on events *)

(** event is a bifunctor 'Type ⊗ Typeᵒᵖ → Type' with the following two actions *)
Definition e_lift_r {I J K} (f : K -> J) (E : event I J) : event I K :=
  Event (E.(qry) ∘ f) (fun _ => E.(rsp)) (fun _ => E.(nxt)).
Definition e_lift_l {I J K} (f : I -> K) (E : event I J) : event K J :=
  Event E.(qry) (fun _ => E.(rsp)) (fun _ q => f ∘ E.(nxt) q).

Notation "E <ₑ f" := (e_lift_r f E) (at level 30).
Notation "f >ₑ E" := (e_lift_l f E) (at level 30).


(** event coproduct *)
Definition esum {I J : Type} (E F : event I J) : event I J :=
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
Notation "E +ₑ F" := (esum E F) (at level 30).

Definition inlₑ {I J} {E F : event I J} : E ⇒ₑ (E +ₑ F) :=
  fun _ q => existT _ (inl q) Fib.
Definition inrₑ {I J} {E F : event I J} : F ⇒ₑ (E +ₑ F) :=
  fun _ q => existT _ (inr q) Fib.


(* null event*)
Definition evoid {I J : Type} : event I J :=
  Event (fun _ => T0) (fun _ q => match q with end) (fun _ q => match q with end).
Notation "∅ₑ" := (evoid).
Definition eelim0 {I J} {E : event I J} : evoid ⇒ₑ E := fun _ q => match q with end.

(* unit event *)
Definition eunit {I : Type} : event I I :=
  Event (fun _ => T1) (fun _ _ => T1) (fun i _ _ => i).
Notation "1ₑ" := (eunit).

(* translate a event from deepspec-itree form to trivially indexed form *)
Definition eclassic (E : Type -> Type) : event₀ :=
  Event₀ { X : Type & E X } (@projT1 _ _).

Definition e_of_classic {E : Type -> Type} {X} : E X -> ⟦₀ eclassic E ⟧ X.
  refine (fun e => existT _ (existT E X e) _).
  refine (fun x => x).
Defined.
