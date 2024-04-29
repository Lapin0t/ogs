From OGS Require Import Prelude.
From OGS.Utils Require Import Family.
From OGS.Ctx Require Import Abstract.

Declare Scope asgn_scope.
Delimit Scope asgn_scope with asgn.

Reserved Notation "Γ =[ F ]> Δ" (at level 30).
Reserved Notation "u ≡ₐ v" (at level 50).
Reserved Notation "⟪ F , G ⟫" (at level 40).
Reserved Notation "O # F" (at level 30).
Reserved Notation "o ⦇ u ⦈" (at level 30).
Reserved Notation "!".
(*Reserved Notation "[ u , v ]" (at level 9).*)

Section with_param.
  Context `{CC : context C Xs} {CL : context_laws C Xs}.

(*|
Assignment
------------

We distinguish assignments, mapping variables in a context to terms, from
substitutions, applying an assignment to a term. Assignments are intrinsically
typed, mapping variables of a context Γ to open terms with variables in Δ.
|*)
  Definition assignment (F : Fam (C :: Xs)) (Γ Δ : C) := c_var Γ →ᵢ F Δ.

  Notation "Γ =[ F ]> Δ" := (assignment F Γ%ctx Δ%ctx).
  Bind Scope asgn_scope with assignment.

(*|
Pointwise equality of assignments.
|*)
  (*Definition asgn_eq {F : Fam₁ T C} Γ Δ : relation (Γ =[F]> Δ) := ∀ₕ _, ∀[ eqᵢ ]ᵣ.
  Notation "u ≡ₐ v" := (asgn_eq _ _ u%asgn v%asgn).

  #[global] Instance asgn_equiv {F Γ Δ} : Equivalence (@asgn_eq F Γ Δ).
  Proof.
    econstructor.
    - now intros u ? i.
    - intros u h ? ? i; symmetry; now apply (H _ i).
    - intros u v w h1 h2 ? i; transitivity (v _ i); [ now apply h1 | now apply h2 ].
  Qed.*)

(*|
A kind relaxed of pointwise mapping.
|*)
  Definition a_map {F G : Fam (C :: Xs)} {Γ1 Γ2 Γ3} (u : Γ1 =[F]> Γ2) (v : F Γ2 →ᵢ G Γ3)
    : Γ1 =[G]> Γ3
    := compF v u .


(*|
Internal hom functors. The monoidal product for substitution is a bit cumbersome as
it is expressed as a coend, that is, a quotient. Following the formalization by
Dima Szamozvancev, we instead prefer to express everything in terms of its adjoint,
the internal hom.

For example the monoidal multiplication map will not be typed `X ⊗ X ⇒ X` but
`X ⇒ ⟦ X , X ⟧`.

It is an end, that is, a subset, which are far more easy to work with as they can
simply be encoded as a record pairing an element and a proof. The proof part is not
written here but encoded later on.

The real one is ⟦-,-⟧₁, but in fact we can define an analogue to this bifunctor
for any functor category `ctx → C`, which we do here for Fam₀ and Fam₂ (unsorted and
bisorted, scoped families). This will be helpful to define what it means to
substitute other kinds of syntactic objects.
|*)
  Definition internal_hom₁ {Y} : Fam (C :: Xs) -> Fam [C;Y] -> Fam [C;Y]
    := fun F G Γ y => forall Δ, Γ =[F]> Δ -> G Δ y .
  Definition internal_hom {Ys} : Fam (C :: Xs) -> Fam (C :: Ys) -> Fam (C :: Ys)
    := fun F G Γ => λ… xs ⇒ internal_hom₁ F (uncurryF ∘ G) Γ xs .
  Notation "⟪ A , B ⟫" := (internal_hom A B) : fam_scope.

(*|
Experimental. The left action on maps of the internal hom bifunctor.
|*)
  Definition hom_bimap Ys {F1 F2 : Fam (C :: Xs)} {G1 G2 : Fam (C :: Ys)}
    (u : F2 →ᵢ F1) (v : G1 →ᵢ G2) : ⟪ F1 , G1 ⟫ →ᵢ ⟪ F2 , G2 ⟫ .
    hom_bimap []       u v := _ ;
    hom_bimap (Y :: Ys) u v := _ .
    cbn.
    refine (fun Γ => _); cbn in *.
    induction Ys; cbn in *.
    - refine (fun f _ a => (v _ (f _ (a_map a (u _))))).
    - refine (fun x => _).
      now apply IHYs.
  Defined.
  Print hom_bimap.
      refine (IHYs (fun Γ => G1 Γ)).
      
    cbn.
    refine (fun Γ => _).
    unfold internal_hom.
    change (∀[ ?])
    
    refine (λ… xs ⇒ _).
    := fun _ f _ a => f _ (fun _ i => m _ _ (a _ i)).
  Definition hom_precomp₁ {F1 F2 : Fam₁ T C} {G} (m : F1 ⇒₁ F2)
    : ⟦ F2 , G ⟧₁ ⇒₁ ⟦ F1 , G ⟧₁
    := fun _ _ f _ a => f _ (fun _ i => m _ _ (a _ i)).
  Definition hom_precomp₂ {F1 F2 : Fam₁ T C} {G} (m : F1 ⇒₁ F2)
    : ⟦ F2 , G ⟧₂ ⇒₂ ⟦ F1 , G ⟧₂
    := fun _ _ _ f _ a => f _ (fun _ i => m _ _ (a _ i)).

  #[global] Arguments hom_precomp₀ _ _ _ _ _ _ /.
  #[global] Arguments hom_precomp₁ _ _ _ _ _ _ _ /.
  #[global] Arguments hom_precomp₂ _ _ _ _ _ _ _ _ /.

(*|
Constructing a sorted family of operations from O with arguments taken from the family F.
|*)
  Record filled_op (O : Oper T C) (F : Fam₁ T C) (Γ : C) (t : T) :=
    OFill { fill_op : O t ; fill_args : o_dom fill_op =[F]> Γ }.

  Derive NoConfusion NoConfusionHom for filled_op.
  #[global] Arguments OFill {O F Γ t} o a%asgn : rename.
  #[global] Arguments fill_op {O F Γ t} _.
  #[global] Arguments fill_args {O F Γ t} _ _ /.
  Notation "S # F" := (filled_op S F).

(*|
We can forget the arguments and get back a bare operation.
|*)
  Definition forget_args {O : Oper T C} {F} : (O # F) ⇒₁ ⦉ O ⦊
    := fun _ _ => fill_op.

(*|
The empty assignment.
|*)
  Definition a_empty {F Γ} : ∅ =[F]> Γ
    := fun _ i => match c_view_emp i with end.

(*|
The copairing of assignments.
|*)
  Definition a_cat {F Γ1 Γ2 Δ} (u : Γ1 =[F]> Δ) (v : Γ2 =[F]> Δ) : (Γ1 +▶ Γ2) =[F]> Δ
    := fun t i => match c_view_cat i with
               | Vcat_l i => u _ i
               | Vcat_r j => v _ j
               end.
  #[global] Arguments a_cat _ _ _ _ _ _ _ _ /.

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
