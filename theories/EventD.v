Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

From OGS Require Import Utils CatD.

Record event (I : Type) : Type := Event {
  qry : I -> Type ;
  rsp {i} : qry i -> Type ;
  nxt {i} (q : qry i) : rsp q -> I
}.

Definition e_eval {I} (E : event I) (X : I -> Type) (i : I) : Type :=
  { q : E.(qry) i & forall r : E.(rsp) q, X (E.(nxt) q r) }.

Notation "⟦ E ⟧" := (e_eval E) (at level 20).

Instance FunctorEvent {I} (E : event I) : Functor (⟦ E ⟧).
  econstructor. intros x y f i [e k].
  exact (existT _ e (fun r => f _ (k r))).
Defined.

Definition e_ₑarr {I : Type} (E : event I) (F : (I -> Type) -> (I -> Type)) : Type :=
  forall i (q : E.(qry) i), F (fiber (E.(nxt) q)) i.


Notation "E ₑ⇒ F" := (earrow_fam E F) (at level 30).

Definition ea_eval_fam {I} {E : event I} {F : psh I -> psh I} {FF : Functor F}
           (m : E ₑ⇒ F) X : ⟦ E ⟧ X ==> F X.
intros i [ e k].
unfold earrow_fam in m.
refine (fmap _ _ (m _ e)).
intros j []. exact (k a).
Defined.
Arguments ea_eval_fam {I} {E} {F} {FF} m X.

Notation "⟦ₑ⇒ m ⟧ X" := (ea_eval_fam m X) (at level 100).

Definition earrow {I} (E F : event I) := earrow_fam E (⟦ F ⟧).
Notation "E ⇒ₑ F" := (earrow E F) (at level 30).

Definition eeval_arrow {I} {E F : event I} (m : E ⇒ₑ F) X : ⟦ E ⟧ X ==> ⟦ F ⟧ X :=
  ea_eval_fam m X.

Notation "⟦⇒ₑ m ⟧ X" := (eeval_arrow m X) (at level 100).

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
