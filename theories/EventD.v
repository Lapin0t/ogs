Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

From OGS Require Import Utils CatD.

Record event (I : Type) : Type := Event {
  qry : I -> Type ;
  rsp {i} : qry i -> Type ;
  nxt {i} (q : qry i) : rsp q -> I
}.

Definition e_eval {I} (E : event I) : endo (psh I) :=
  fun X i => { q : E.(qry) i & forall r : E.(rsp) q, X (E.(nxt) q r) }.

Notation "⟦ E ⟧" := (e_eval E) (at level 20).

Instance FunctorEvent {I} (E : event I) : Functor (⟦ E ⟧).
  econstructor. intros x y f i [e k].
  exact (existT _ e (fun r => f _ (k r))).
Defined.

(****************)
(* event arrows *)
Definition e_arrow {I : Type} (E : event I) (F : endo (psh I)) : Type :=
  forall i (q : E.(qry) i), F (fiber (E.(nxt) q)) i.

Notation "E ₑ⇒ F" := (e_arrow E F) (at level 30).
Notation "E ⇒ₑ F" := (E ₑ⇒ ⟦ F ⟧) (at level 30).

Definition e_arrow_eval {I} {E : event I} {F : endo (psh I)} {FF : Functor F}
           : E ₑ⇒ F -> ⟦ E ⟧ ⟹ F :=
  fun m _ _ x => fiber_into _ (projT2 x) <$> m _ (projT1 x).
Arguments e_arrow_eval {I} {E} {F} {FF} m X.
Notation "⟦⇒ m ⟧ X" := (e_arrow_eval m X) (at level 30).

(* inverse of e_arrow_eval, meaning that the functor ⟦-⟧ : event I → endo (psh I)
   is fully-faithfull (i think the proof requires function extensionality
   and parametricity) *)
Definition e_arrow_mk {I} {E : event I} {F : endo (psh I)} {FF : Functor F}
           : ⟦ E ⟧ ⟹ F -> E ₑ⇒ F :=
  fun m i q => m (fiber (nxt E q)) _ (existT _ q Fib).

(*********************************************)
(* alternate unrolled definition of 'E ⇒ₑ F' *)
Record e_arrow' {I : Type} (E F : event I) := EArrow {
  EA_qry {i} : E.(qry) i -> F.(qry) i ;
  EA_rsp {i} (q : E.(qry) i) : F.(rsp) (EA_qry q) -> E.(rsp) q ;
  EA_coh {i} (q : E.(qry) i) r : E.(nxt) q (EA_rsp q r) = F.(nxt) (EA_qry q) r
}.

Definition e_arrow'_to_arrow {I} {E F : event I} : e_arrow' E F -> E ⇒ₑ F.
intros m i q.
refine (existT _ (m.(EA_qry) q) (fun r => _)).
rewrite <-(m.(EA_coh) q r).
exact (Fib (m.(EA_rsp) q r)).
Defined.

Definition e_arrow_to_arrow' {I} {E F : event I} : E ⇒ₑ F -> e_arrow' E F.
intros m.
refine (EArrow (fun _ q => projT1 (m _ q))
               (fun _ q r => let (a) := projT2 (m _ q) r in a)
                _).
intros; cbn; destruct (projT2 (m i q) r); reflexivity.
Defined.
Print e_arrow_to_arrow'.

(* non-dependent events *)

Definition event0 : Type := event T1.
Definition e_eval0 (E : event0) : Type -> Type := fun X => ⟦ E ⟧ (fun _ => X) t1_0.
Definition e_arrow0 (E : event0) (F : Type -> Type) : Type :=
  forall q : E.(qry) t1_0, F (E.(rsp) q).
Notation "E ₑ⇒₀ F" := (e_arrow0 E F) (at level 30).
Definition lift_fam0 (F : Type -> Type) (X : psh T1) : psh T1 := fun _ => F (X t1_0).
(*
Definition arrow_of_arrow0 {E F} {FF : Functor (lift_fam0 F)} (m : E ₑ⇒₀ F) : E ₑ⇒ (lift_fam0 F).
  intros [] q.
  unfold e_arrow0 in m.
  Check (@fmap T1 (lift_fam0 F) FF).
*)
  

(***************************)
(* constructions on events *)

(* event coproduct *)
Definition esum {I : Type} (E F : event I) : event I.
  unshelve refine (Event _ _ _).
  + intro i. exact (E.(qry) i + F.(qry) i)%type.
  + intros i q. destruct q.
    - exact (E.(rsp) q).
    - exact (F.(rsp) q).
  + intros i q r. destruct q.
    - exact (E.(nxt) q r).
    - exact (F.(nxt) q r).
Defined.

Definition einl {I} {E F : event I} : E ⇒ₑ esum E F :=
  fun i q => existT _ (inl q) Fib.
Definition einr {I} {E F : event I} : F ⇒ₑ esum E F :=
  fun i q => existT _ (inr q) Fib.


(* null event*)
Definition evoid {I : Type} : event I :=
  Event (fun _ => T0) (fun _ e => match e with end) (fun _ e => match e with end).
Definition eelim0 {I} {E : event I} : evoid ⇒ₑ E :=
  fun _ q => ex_falso q.

(* unit event *)
Definition eunit {I : Type} : event I :=
  Event (fun _ => T1) (fun _ _ => T1) (fun i _ _ => i).

(* translate a event from deepspec-itree form to trivially indexed form *)
Definition eclassic (E : Type -> Type) : event T1 :=
  Event (fun _ => { X : Type & E X })
        (fun _ x => projT1 x)
        (fun _ _ _ => t1_0).

Definition e_of_classic {E : Type -> Type} {X} : E X -> ⟦ eclassic E ⟧ (fun _ => X) t1_0.
  refine (fun e => existT _ (existT E X e) _).
  refine (fun x => x).
Defined.
