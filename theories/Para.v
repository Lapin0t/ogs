From ITree Require Import
     Events.Dependent
     ITree
     Events.Exception.

Import ITreeNotations.

(** * get_hd
    Computes the first visible event of a tree, or its return value if the computation is pure.
    Diverges exclusively silently, and if and only if the tree diverges silently.
 *)
CoFixpoint get_hd {E X} (t : itree E X) : itree void1 (X + { Y : Type & E Y & (Y -> itree E X)}) :=
  match observe t with
  | RetF x => Ret (inl x)
  | TauF t => Tau (get_hd t)
  | VisF e k => Ret (inr (existT2 _ _ _ e k))
  end.

Definition embed_void {E X} (t : itree void1 X) : itree E X :=
  translate (fun _ (x : void1 _) => match x with end) t.

Section Interleave.
  Variable (E1 E2 : Type -> Type).
  Variable (X1 X2 : Type).

  Variant SchedE : Type -> Type := | Sched : SchedE bool.

  (* Parallel interleaving of two computations [t1] and [t2]:
     - Only returns when both computations return. In particular, does not observe the pure value computed by a terminating computation if the other one diverges.
     - Interprets each domain of events as disjoint
     - If one of the computations diverges silently, then the silent divergence is a valid behavior of the parallel composition even if the other computation is productive (i.e. we consider the unfair scheduler)
   *)

  Definition interleave : itree E1 X1 -> itree E2 X2 -> itree (SchedE +' E1 +' E2) (X1 * X2) :=
    cofix F (t1 : itree E1 X1) (t2 : itree E2 X2) :=
      b <- (trigger Sched: itree (SchedE +' E1 +' E2) _);;
      if b : bool 
      then embed_void (get_hd t1) >>=
                      (fun res : X1 + (sigT2 E1 (fun Y : Type => Y -> itree E1 X1)) =>
                         match res with
                         | inl x => ITree.map (fun y => (x,y)) (translate (fun _ e => inr1 (inr1 e)) t2)
                         | inr (existT2 _ _ x e k) => vis e (fun x0 : x => F (k x0) t2)
                         end) 
      else embed_void (get_hd t2) >>=
                      (fun res : X2 + (sigT2 E2 (fun Y : Type => Y -> itree E2 X2)) =>
                         match res with
                         | inl y => ITree.map (fun x => (x,y)) (translate (fun _ e => inr1 (inl1 e)) t1)
                         | inr (existT2 _ _ x e k) => vis e (fun x0 : x => F t1 (k x0))
                         end)
  . 


End Interleave.

Section Synchro.

  Variable (E1 E2 : Type -> Type).
  Variable (X1 X2 : Type).

  (* Parallel "strong" synchronization of two computations [t1] and [t2] ("zipper"):
     - Emits product of events at synchronization points.
     - After any synchronization, diverges silently iff one of the computations diverges silently.
     - If both computations return in synch, return the product of the results.
     - If a computation terminates while the other one still produces (i.e. if an event cannot be synchronize), fails.
   *)

  Definition FailureE := exceptE unit.
  Definition throw {A : Type} {E} `{FailureE -< E} : itree E A :=
    x <- trigger (Throw tt);; match x: void with end.

  Variant prod1 (E1 E2 : Type -> Type) : Type -> Type :=
  | pair1 X1 X2 (e1 : E1 X1) (e2 : E2 X2) : prod1 E1 E2 (X1 * X2).
  Infix "*'" := prod1 (at level 59, right associativity).
  Arguments pair1 {E1 E2 X1 X2}.

  Definition para_synch : itree E1 X1 -> itree E2 X2 -> itree ((E1 *' E2) +' FailureE) (X1 * X2) :=
    cofix para_synch (t1 : itree E1 X1) (t2 : itree E2 X2) :=
      match observe t1, observe t2 with
      | TauF t1, TauF t2 => Tau (para_synch t1 t2) 
      | TauF t1, _ => Tau (para_synch t1 t2) 
      | _, TauF t2 => Tau (para_synch t1 t2)
      | VisF e1 k1, VisF e2 k2 => vis (pair1 e1 e2)
                                     (fun '(x1,x2) => para_synch (k1 x1) (k2 x2))
      | RetF x1, RetF x2 => Ret (x1,x2)
      | _, _ => throw
      end.

End Synchro.
