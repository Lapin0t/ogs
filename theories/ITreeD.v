Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.Fin.
Require Import Program.Tactics.

Require Import Coq.Logic.FunctionalExtensionality.
From Equations Require Import Equations.

From OGS Require Import Utils EventD.

From ITree Require Import Basics.

Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.


(***************************)


Section itree.

  Context {I : Type} {E : event I} {R : I -> Type}.

  Variant itreeF (ind : I -> Type) (i : I) :=
  | RetF (r : R i)
  | TauF (t : ind i)
  | VisF (e : E.(qry) i) (k : forall r : E.(rsp) e, ind (E.(nxt) e r))
  .

  CoInductive itree (i : I) : Type := go
  { _observe : itreeF itree i }.

End itree.

Bind Scope itree_scope with itree.
Delimit Scope itree_scope with itree.
Local Open Scope itree_scope.

Arguments itree {_} _ _ _.
Arguments itreeF {_} _ _ _ _.

Notation itree' E R := (itreeF E R (itree E R)).

Definition observe {I E R i} (t : @itree I E R i) : itree' E R i :=
  @_observe I E R i t.

Notation Ret x := (go (RetF x)).
Notation Tau t := (go (TauF t)).
Notation Vis e k := (go (VisF e k)).

Section a.
Context {I} {E : event I} {R : I -> Type}.
Definition ret {i} x : itree E R i := Ret x.
Definition tau {i} t : itree E R i := Tau t.
Definition vis {i} e k : itree E R i := Vis e k.
Definition vis' : [[ E ]] (itree E R) ==> itree E R := fun i x => Vis _ (projT2 x).
End a.

Definition subst {I : Type} {E : event I} {X Y : I -> Type}
           (f : X ==> itree E Y) : itree E X ==> itree E Y :=
  cofix _subst _ u :=
    match observe u with
    | RetF r => f _ r
    | TauF t => Tau (_subst _ t)
    | VisF e k => Vis e (fun r => _subst _ (k r))
    end.

(* McBride's "daemonic" bind: [f] has to be defined at every state [i] *)
Definition bind {I E X Y i} x f := @subst I E X Y f i x.
Notation "x ?>= f" := (bind x f) (at level 20).





Section angelic.
Context {I : Type}.

Definition itreeP (E : event I) i j X : Type := itree E (X @ j) i.

Definition retP {E : event I} {X i} (x : X) : itreeP E i i X := Ret (Pin x).

(* McBride's "angelic" bind: we know the states i, j, k we are in *)
Equations bindP {E : event I} {X Y i j k}
            : itreeP E i j X -> (X -> itreeP E j k Y) -> itreeP E i k Y :=
   bindP x f := x ?>= λ { | _ | Pin x0 => f x0 }.
Notation "x >>= f" := (bindP x f) (at level 20).

Definition iterP {E : event I} {X Y : Type} {i}
           (body : X -> itreeP E i i (X + Y)) : X -> itreeP E i i Y :=
  cofix _iter x := body x >>= fun r => match r with
                              | inl x' => tau (_iter x')
                              | inr y => ret (Pin y)
                              end.
End angelic.
