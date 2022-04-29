Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

From Equations Require Import Equations.

From OGS Require Import Utils.
From OGS.ITree Require Import Cat Event.

Section itree. Context {I : Type} {E : event I I} {R : I -> Type}.

  Variant itreeF (ind : I -> Type) (i : I) :=
  | RetF (r : R i)
  | TauF (t : ind i)
  | VisF (e : E.(qry) i) (k : forall r : E.(rsp) e, ind (E.(nxt) e r))
  .

  CoInductive itree (i : I) : Type := go
  { _observe : itreeF itree i }.

End itree.

Declare Scope itree_scope.
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

Section short. Context {I} {E : event I I} {R : I -> Type}.

  Definition ret {i} x : itree E R i := Ret x.
  Definition tau {i} t : itree E R i := Tau t.
  Definition vis {i} e k : itree E R i := Vis e k.
  Definition vis_alg : ⟦ E ⟧ (itree E R) ⇒ᵢ itree E R :=
    fun _ x => Vis (projT1 x) (projT2 x).

End short.

Definition vis' {I} (E : event I I) {R i} e k : itree E R i := @vis _ E _ _ e k.
Arguments vis' {I} E {R i} e k.

Section structure. Context {I : Type} {E : event I I} {X Y : psh I}.

  Definition fmap (f : X ⇒ᵢ Y) : itree E X ⇒ᵢ itree E Y :=
    cofix _fmap _ u :=
      match (observe u) with
      | RetF r => Ret (f _ r)
      | TauF t => Tau (_fmap _ t)
      | VisF e k => vis e (fun r => _fmap _ (k r))
      end.

  Definition subst (f : X ⇒ᵢ itree E Y) : itree E X ⇒ᵢ itree E Y :=
    cofix _subst _ u :=
      match observe u with
      | RetF r => f _ r
      | TauF t => Tau (_subst _ t)
      | VisF e k => Vis e (fun r => _subst _ (k r))
      end.

  (* McBride's "daemonic" bind: [f] has to be defined at every state [i] *)
  Definition bind {i} x f := @subst f i x.

End structure.
(*Notation "x ?>= f" := (bind x f) (at level 20).*)

Instance FunctorItree {I} (E : event I I) : Functor (itree E) :=
  Build_Functor _ (fun X Y => @fmap I E X Y).

Instance MonadItree {I} (E : event I I) : Monad (itree E) :=
  Build_Monad _ (fun X => @ret I E X) (fun X Y => @subst I E X Y).

Definition kcomp {I} {E : event I I} {X Y Z : psh I} (f : X ⇒ᵢ itree E Y) (g : Y ⇒ᵢ itree E Z) : X ⇒ᵢ itree E Z :=
  fun i x => f i x >>= g.

#[global]
Notation "f >> g" := (kcomp f g) (at level 30).
