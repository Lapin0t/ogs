From OGS Require Import Prelude.
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

(*
Definition subst_delay {I} {E : event I I} {X Y i} (f : X -> itree E Y i)
           : delay X -> itree E Y i :=
  cofix _subst_delay x :=
    go (match x.(_observe) with
       | RetF r => (f r).(_observe)
       | TauF t => TauF (_subst_delay t)
       | VisF e k => match e with end
       end).  
*)

From OGS.ITree Require Import Monad.

Definition ret_delay {X} : X -> delay X := fun x => Ret' x .

Definition tau_delay {X} : delay X -> delay X :=
  fun t => go (TauF (t : itree ∅ₑ (fun _ : T1 => X) T1_0)) .

Definition bind_delay {I} {E : event I I} {X Y i}
  : delay X -> (X -> itree E Y i) -> itree E Y i
  := fun x f => bind (emb_delay x) (fun _ '(Fib x) => f x) .

Definition fmap_delay {X Y} (f : X -> Y) : delay X -> delay Y :=
  fmap (fun 'T1_0 => f) T1_0 .

Definition iter_delay {X Y} : (X -> delay (X + Y)) -> X -> delay Y :=
  fun f => iter (fun 'T1_0 => f) T1_0 .
