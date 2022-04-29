(** misc notations *)

#[global] Notation endo T := (T -> T).
  
#[global] Notation "f ∘ g" := (fun x => f (g x))
 (at level 40, left associativity) : function_scope.  

Notation "a ,' b" := (existT _ a b) (at level 30).

(** currying *)

Definition uncurry {A B} {C : A -> B -> Type}
           (f : forall a b, C a b) (i : A * B)
  := f (fst i) (snd i).

Definition curry {A B} {C : A -> B -> Type} (f : forall i, C (fst i) (snd i)) a b :=
  f (a , b).

(* dependent versions (actually untyped) *)
Notation curry' := (fun f a b => f (a ,' b)).
Notation uncurry' := (fun f x => f (projT1 x) (projT2 x)).

(***************)
(* Finite sets *)

Variant T0 := .
Variant T1 := T1_0.
Variant T2 := T2_0 | T2_1.
Variant T3 := T3_0 | T3_1 | T3_2.

Definition ex_falso {A : Type} (bot : T0) : A := match bot with end.
