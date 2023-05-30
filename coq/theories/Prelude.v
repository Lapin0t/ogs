#[global] Set Primitive Projections.

From Equations Require Export Equations.
#[global] Set Equations Transparent.
#[global] Set Equations With UIP.

Require Export Coq.Program.Equality.
Export EqNotations.
Require Export Coq.Logic.StrictProp.

Axiom AxiomUIP : forall X : Type, UIP X.
#[global] Existing Instance AxiomUIP.

#[global] Notation endo T := (T -> T).
  
#[global] Notation "f ∘ g" := (fun x => f (g x))
 (at level 40, left associativity) : function_scope.  

#[global] Notation "a ,' b" := (existT _ a b) (at level 30).

Definition uncurry {A B} {C : A -> B -> Type} (f : forall a b, C a b) (i : A * B)
  := f (fst i) (snd i).

Definition curry {A B} {C : A -> B -> Type} (f : forall i, C (fst i) (snd i)) a b
  := f (a , b).

#[global] Notation curry' := (fun f a b => f (a ,' b)).
#[global] Notation uncurry' := (fun f x => f (projT1 x) (projT2 x)).

Variant T0 := .
Variant T1 := T1_0.
Variant T2 := T2_0 | T2_1.
Variant T3 := T3_0 | T3_1 | T3_2.
Derive NoConfusion for T0.
Derive NoConfusion for T1.
Derive NoConfusion for T2.
Derive NoConfusion for T3.

Definition ex_falso {A : Type} (bot : T0) : A := match bot with end.

Record sigS {X : Type} (P : X -> SProp) := { sub_elt : X ; sub_prf : P sub_elt }.
Arguments sub_elt {X P}.
Arguments sub_prf {X P}.
