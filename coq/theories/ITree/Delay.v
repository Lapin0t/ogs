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

Definition bind_delay' {X Y}
  : delay X -> (X -> delay Y) -> delay Y
  := fun x f => bind x (fun 'T1_0 y => f y).

Definition fmap_delay {X Y} (f : X -> Y) : delay X -> delay Y :=
  fmap (fun 'T1_0 => f) T1_0 .

Definition iter_delay {X Y} : (X -> delay (X + Y)) -> X -> delay Y :=
  fun f => iter (fun 'T1_0 => f) T1_0 .

(*
From Coinduction Require Import coinduction lattice rel tactics.
From OGS Require Import Utils.Rel.
From OGS Require Import ITree.Eq.

Lemma iter_unfold {X Y} (f : X -> delay (X + Y)) {x}
  :
      (iter_delay f x)
  ≊
      (bind_delay' (f x) (fun r => match r with
                                 | inl x => tau_delay (iter_delay f x)
                                 | inr y => ret_delay y end)).
Proof.
  apply (gfp_fp (it_eq_map ∅ₑ (eqᵢ _))).
  cbn; destruct (_observe (f x)).
  - change (iter _ T1_0 ?x) with (iter_delay f x).
    destruct r; econstructor; auto.
  - econstructor.
    eapply (it_eq_up2bind_t (eqᵢ (fun _ => (X + Y)%type)) _).
    econstructor.
    reflexivity.
    intros [] ? ? <-.
    cbn.

    cbv; reflexivity.
    + econstructor; auto.
    unfold
  try econstructor; eauto.
  unfold iter_delay at 1.
  unfold bind_delay.
  destruct (_observe (f x)).
  destruct r

*)
