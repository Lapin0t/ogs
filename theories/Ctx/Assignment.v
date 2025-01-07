(*|
Assignments
===========

In this file we define assignments for a given abstract context structure. We also define
several combinators based on them: the internal substitution hom, filled operations,
copairing, etc.

.. coq:: none
|*)
From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.
From OGS.Ctx Require Import Abstract Family.

Declare Scope asgn_scope.
Delimit Scope asgn_scope with asgn.

Reserved Notation "Γ =[ F ]> Δ" (at level 30).
Reserved Notation "u ≡ₐ v" (at level 50).
Reserved Notation "⟦ F , G ⟧₀" (at level 40).
Reserved Notation "⟦ F , G ⟧₁" (at level 40).
Reserved Notation "⟦ F , G ⟧₂" (at level 40).
Reserved Notation "O # F" (at level 30).
Reserved Notation "o ⦇ u ⦈" (at level 30).
Reserved Notation "!".
Reserved Notation "[ u , v ]" (at level 9).

Section with_param.
  Context {T C : Type} {CC : context T C} {CL : context_laws T C}.

(*|
Definition of assignments (Def. 5)
----------------------------------

We distinguish assignments, mapping variables in a context to terms, from
substitutions, applying an assignment to a term. Assignments are intrinsically
typed, mapping variables of a context Γ to open terms with variables in Δ.

.. coq::
   :name: asgn
|*)
  Definition assignment (F : Fam₁ T C) (Γ Δ : C) := forall x, Γ ∋ x -> F Δ x.

  Notation "Γ =[ F ]> Δ" := (assignment F Γ%ctx Δ%ctx).
(*|
.. coq:: none
|*)
  Bind Scope asgn_scope with assignment.
(*|
Pointwise equality of assignments.
|*)
  Definition asgn_eq {F : Fam₁ T C} Γ Δ : relation (Γ =[F]> Δ) := ∀ₕ _, ∀ₕ _, eq.
  Notation "u ≡ₐ v" := (asgn_eq _ _ u%asgn v%asgn).

  #[global] Instance asgn_equiv {F Γ Δ} : Equivalence (@asgn_eq F Γ Δ).
  Proof.
    econstructor.
    - now intros u ? i.
    - intros u h ? ? i; symmetry; now apply (H _ i).
    - intros u v w h1 h2 ? i; transitivity (v _ i); [ now apply h1 | now apply h2 ].
  Qed.
(*|
Internal hom functors. The monoidal product for substitution is a bit cumbersome as
it is expressed as a coend, that is, a quotient. Following the formalization by
Dima Szamozvancev, we instead prefer to express everything in terms of its adjoint,
the internal hom.

For example the monoidal multiplication map will not be typed ``X ⊗ X ⇒ X`` but
``X ⇒ ⟦ X , X ⟧``.

It is an end, that is, a subset, which are far more easy to work with as they can
simply be encoded as a record pairing an element and a proof. The proof part is not
written here but encoded later on.

The real one is ⟦-,-⟧₁, but in fact we can define an analogue to this bifunctor
for any functor category ``ctx → C``, which we do here for Fam₀ and Fam₂ (unsorted and
bisorted, scoped families). This will be helpful to define what it means to
substitute other kinds of syntactic objects.

See `Ctx/Abstract.v <Abstract.html>`_ for more details on the theory. This is called
the _power object_ (Def. 6) in the paper.

.. coq::
   :name: ihom
|*)
  Definition internal_hom₀ : Fam₁ T C -> Fam₀ T C -> Fam₀ T C
    := fun F G Γ => forall Δ, Γ =[F]> Δ -> G Δ.
  Definition internal_hom₁ : Fam₁ T C -> Fam₁ T C -> Fam₁ T C
    := fun F G Γ x => forall Δ, Γ =[F]> Δ -> G Δ x.
  Definition internal_hom₂ : Fam₁ T C -> Fam₂ T C -> Fam₂ T C
    := fun F G Γ x y => forall Δ, Γ =[F]> Δ -> G Δ x y.

  Notation "⟦ F , G ⟧₀" := (internal_hom₀ F G).
  Notation "⟦ F , G ⟧₁" := (internal_hom₁ F G).
  Notation "⟦ F , G ⟧₂" := (internal_hom₂ F G).
(*|
.. coq:: none
|*)
  #[global] Arguments internal_hom₀ _ _ _ /.
  #[global] Arguments internal_hom₁ _ _ _ _ /.
  #[global] Arguments internal_hom₂ _ _ _ _ _ /.
(*|
Constructing a sorted family of operations from O with arguments taken from the family F.

.. coq::
   :name: filledop
|*)
  Record filled_op (O : Oper T C) (F : Fam₁ T C) (Γ : C) (t : T) :=
    OFill { fill_op : O t ; fill_args : o_dom fill_op =[F]> Γ }.
  Notation "S # F" := (filled_op S F).
(*|
.. coq:: none
|*)
  Derive NoConfusion NoConfusionHom for filled_op.
  #[global] Arguments OFill {O F Γ t} o a%asgn : rename.
  #[global] Arguments fill_op {O F Γ t} _.
  #[global] Arguments fill_args {O F Γ t} _ _ /.
(*|
We can forget the arguments and get back a bare operation.
|*)
  Definition forget_args {O : Oper T C} {F} : (O # F) ⇒₁ ⦉ O ⦊
    := fun _ _ => fill_op.
(*|
The empty assignment.

.. coq::
   :name: asgnempty
|*)
  Definition a_empty {F Γ} : ∅ =[F]> Γ
    := fun _ i => match c_view_emp i with end.
(*|
The copairing of assignments.

.. coq::
   :name: asgncat
|*)
  Definition a_cat {F Γ1 Γ2 Δ} (u : Γ1 =[F]> Δ) (v : Γ2 =[F]> Δ) : (Γ1 +▶ Γ2) =[F]> Δ
    := fun t i => match c_view_cat i with
               | Vcat_l i => u _ i
               | Vcat_r j => v _ j
               end.
(*|
.. coq:: none
|*)
  #[global] Arguments a_cat _ _ _ _ _ _ _ _ /.
(*|
A kind relaxed of pointwise mapping.
|*)
  Definition a_map {F G : Fam₁ T C} {Γ Δ1 Δ2} (u : Γ =[F]> Δ1) (f : forall x, F Δ1 x -> G Δ2 x)
    : Γ =[G]> Δ2
    := fun _ i => f _ (u _ i) .
(*|
.. coq:: none
|*)
  #[global] Arguments a_map _ _ _ _ _ _ _ _ /.
(*|
Copairing respects pointwise equality.
|*)
  #[global] Instance a_cat_eq {F Γ1 Γ2 Δ}
    : Proper (asgn_eq _ _ ==> asgn_eq _ _ ==> asgn_eq _ _) (@a_cat F Γ1 Γ2 Δ).
  Proof.
    intros ?? Hu ?? Hv ??; cbn.
    destruct (c_view_cat a0); [ now apply Hu | now apply Hv ].
  Qed.
End with_param.
(*|
Registering all the notations...
|*)
#[global] Notation "Γ =[ F ]> Δ" := (assignment F Γ%ctx Δ%ctx).
#[global] Bind Scope asgn_scope with assignment.

#[global] Notation "u ≡ₐ v" := (asgn_eq _ _ u%asgn v%asgn).
#[global] Notation "⟦ F , G ⟧₀" := (internal_hom₀ F G).
#[global] Notation "⟦ F , G ⟧₁" := (internal_hom₁ F G).
#[global] Notation "⟦ F , G ⟧₂" := (internal_hom₂ F G).

#[global] Notation "S # F" := (filled_op S F).
#[global] Notation "o ⦇ u ⦈" := (OFill o u%asgn).

#[global] Notation "!" := (a_empty) : asgn_scope.
#[global] Notation "[ u , v ]" := (a_cat u v) : asgn_scope.
