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

Definition e_arrow {I : Type} (E : event I) (F : endo (psh I)) : Type :=
  forall i (q : E.(qry) i), F (fiber (E.(nxt) q)) i.

Notation "E ₑ⇒ F" := (e_arrow E F) (at level 30).
Notation "E ⇒ₑ F" := (E ₑ⇒ ⟦ F ⟧) (at level 30).

Definition e_arrow_eval {I} {E : event I} {F : endo (psh I)} {FF : Functor F}
           : E ₑ⇒ F -> ⟦ E ⟧ ⟹ F :=
  fun m _ _ x => fiber_elim _ (projT2 x) <$> m _ (projT1 x).
Arguments e_arrow_eval {I} {E} {F} {FF} m X.
Notation "⟦⇒ m ⟧ X" := (e_arrow_eval m X) (at level 30).

(* inverse of e_arrow_eval, meaning that the functor ⟦-⟧ : event I → endo (psh I)
   is fully-faithfull (i think the proof requires function extensionality
   and parametricity) *)
Definition e_arrow_mk {I} {E : event I} {F : endo (psh I)} {FF : Functor F}
           : ⟦ E ⟧ ⟹ F -> E ₑ⇒ F :=
  fun m i q => m (fiber (nxt E q)) _ (existT _ q Fib).

(* alternate *)
Record e_arrow' {I : Type} (E F : event I) := EArrow {
  EA_qry {i} : E.(qry) i -> F.(qry) i ;
  EA_rsp {i} (q : E.(qry) i) : F.(rsp) (EA_qry q) -> E.(rsp) q ;
  EA_coh {i} (q : E.(qry) i) r : E.(nxt) q (EA_rsp q r) = F.(nxt) (EA_qry q) r
}.

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

Definition eunit {I : Type} : event I :=
  Event (fun _ => T1) (fun _ _ => T1) (fun i _ _ => i).

Definition evoid {I : Type} : event I :=
  Event (fun _ => T0) (fun _ e => match e with end) (fun _ e => match e with end).
