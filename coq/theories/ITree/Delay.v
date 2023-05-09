Require Import Coq.Program.Equality.
Import EqNotations.

From OGS Require Import Utils.
From OGS.Game Require Import Event.
From OGS.ITree Require Import ITree.

Definition delay (X : Type) : Type := itree ∅ₑ (fun _ => X) T1_0.

Definition emb_delay {I} {E : event I I} {X i} : delay X -> itree E (X @ i) i :=
  cofix _emb_delay x :=
      go (match x.(_observe) with
         | RetF r => RetF (Fib r)
         | TauF t => TauF (_emb_delay t)
         | VisF e k => match e with end
         end).

Definition subst_delay {I} {E : event I I} {X Y i} (f : X -> itree E Y i)
           : delay X -> itree E Y i :=
  cofix _subst_delay x :=
    go (match x.(_observe) with
       | RetF r => (f r).(_observe)
       | TauF t => TauF (_subst_delay t)
       | VisF e k => match e with end
       end).  

Definition bind_delay {I} {E : event I I} {X Y i}
  : delay X -> (X -> itree E Y i) -> itree E Y i
  := fun x f => subst_delay f x .
