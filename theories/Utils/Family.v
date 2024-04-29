(*|
Type families
===============

.. coq:: none
|*)
From OGS Require Import Prelude.
From OGS.Utils Require Import Rel.

Declare Scope fam_scope.
Delimit Scope fam_scope with fam.

Equations Fam : list Type -> Type :=
  Fam []       := Type ;
  Fam (X :: Xs) := X -> Fam Xs .

#[global] Bind Scope fam_scope with Fam.
#[global] Arguments Fam Ys%list.

Equations tuple : list Type -> Type :=
  tuple []       := T1 ;
  tuple (X :: Xs) := X × tuple Xs .

Definition PFam (Xs : list Type) := tuple Xs -> Type .

Equations uncurryF Xs : Fam Xs -> PFam Xs :=
  uncurryF []       A _        := A ;
  uncurryF (X :: Xs) A (x , xs) := uncurryF Xs (A x) xs .
#[global] Arguments uncurryF {Xs} A xs.
#[global] Notation "A @ᵢ xs" := (uncurryF A xs) (at level 40).

Equations curryF Xs : PFam Xs -> Fam Xs :=
  curryF []       A := A T1_0 ;
  curryF (X :: Xs) A := fun x => curryF Xs (fun xs => A (x , xs)) .
#[global] Arguments curryF {Xs} A.
#[global] Notation "𝒻… xs → A" := (curryF (fun xs => A)) (at level 40).

Equations forallF Xs : Fam Xs -> Type :=
  forallF []       A := A ;
  forallF (X :: Xs) A := forall x, forallF Xs (A x) .
#[global] Arguments forallF {Xs} F.
#[global] Notation "∀[ A ]ᵢ" := (forallF A%fam).
#[global] Notation "∀… xs , A" := (∀[ 𝒻… xs → A ]ᵢ) (at level 40).

Equations funF Xs : Fam Xs -> Fam Xs -> Fam Xs :=
  funF []       A B := A -> B ;
  funF (X :: Xs) A B := fun x => funF Xs (A x) (B x) .
#[global] Arguments funF {Xs} A G.
#[global] Notation "A ⇒ᵢ B" := (funF A B) (at level 50) : fam_scope.

Definition arrowF {Xs} (A B : Fam Xs) := ∀[ A ⇒ᵢ B ]ᵢ.
#[global] Notation "A →ᵢ B" := (arrowF A%fam B%fam) (at level 50) : type_scope.

Equations idF Xs (A : Fam Xs) : A →ᵢ A :=
  idF []       A := fun a => a ;
  idF (X :: Xs) A := fun x => idF Xs (A x) .
#[global] Arguments idF {Xs} A.

Definition arrowP {Xs} (A B : PFam Xs) := forall xs, A xs -> B xs .
#[global] Notation "A →ₚ B" := (arrowP A B) (at level 50) : type_scope.

Equations applyF Xs {A B : Fam Xs} (f : A →ᵢ B) : uncurryF A →ₚ uncurryF B :=
  applyF []       f _        a := f a ;
  applyF (X :: Xs) f (x , xs) a := applyF Xs (f x) xs a .
#[global] Arguments applyF {Xs A B} f [xs] a.
#[global] Notation "f $ᵢ a" := (applyF f a) (at level 40).

Equations bindF Xs {A B : Fam Xs} (f : uncurryF A →ₚ uncurryF B) : A →ᵢ B :=
  bindF []       f := f T1_0 ;
  bindF (X :: Xs) f := fun x => bindF Xs (fun xs => f (x , xs)) .
#[global] Arguments bindF {Xs A B} f.
#[global] Notation "λ… xs ⇒ t" := (bindF (fun xs => t)) (at level 40).

Definition arrowS {Xs} (A B : Fam Xs) := forall C, C →ᵢ A -> C →ᵢ B .
#[global] Notation "A →ₛ B" := (arrowS A%fam B%fam) (at level 50) : type_scope.

Definition idS {Xs} {A : Fam Xs} : A →ₛ A := fun _ k => k .
Definition compS {Xs} {A B C : Fam Xs} (f : B →ₛ C) (g : A →ₛ B) : A →ₛ C
  := fun _ k => f _ (g _ k).
Definition evalS {Xs} {A B : Fam Xs} (f : A →ₛ B) : A →ᵢ B := f _ (idF A) .

  forall (C : tuple Xs -> Type), (forall i, C i -> A i) -> (forall i, C i -> B i) . 

Equations constF (T : Type) Xs : Fam Xs :=
  constF T []       := T ;
  constF T (X :: Xs) := fun _ => constF T Xs .
#[global] Notation "⌊ T ⌋ᵢ" := (constF T%type _) : fam_scope.

Equations compF Xs {A B C : Fam Xs} (f : B →ᵢ C) (g : A →ᵢ B) : A →ᵢ C :=
  compF []       f g := fun a => f (g a) ;
  compF (X :: Xs) f g := fun x => compF Xs (f x) (g x) .
#[global] Arguments compF {Xs A B C} f g.

Lemma curry_uncurry {Xs} (A : tuple Xs -> Type) : forall xs, curryF A @ᵢ xs = A xs .
  induction Xs.
  - now intros [].
  - intros [ x xs ]; now apply IHXs.
Qed.

(*Definition predF {Xs} (A : Fam Xs) := forall xs, uncurryF A xs -> Type .
Definition elt_predF {Xs} {A : Fam Xs} (P : )*)

Definition a_to_smap {Xs} (A B : Fam Xs) (f : A →ᵢ B) : smap (uncurryF A) (uncurryF B) :=
  fun _ k _ c => f $ᵢ k _ c .

Definition smap_to_m {Xs} (A B : Fam Xs) : smap (uncurryF A) (uncurryF B) -> A →ᵢ B .
  intro F . unfold smap in F.
  
  cbn.

Definition idx Xs (A : Fam Xs) : smap (uncurryF A) (uncurryF A) :=
  fun _ f => f .

  intros C f i.


Equations relF Xs : Fam Xs -> Fam Xs :=
  relF []       A := relation A ;
  relF (X :: Xs) A := fun x => relF Xs (A x) .
#[global] Arguments relF {Xs} A.
#[global] Notation relᵢ A := ∀[ relF A%fam ]ᵢ.

Equations const_relF Xs {T : Type} : relation T -> relᵢ (constF T Xs) :=
  const_relF []       R := R ;
  const_relF (X :: Xs) R := fun _ => const_relF Xs R .
#[global] Arguments const_relF {Xs T} R.

Equations fun_relF Xs {A B : Fam Xs} : relᵢ A -> relᵢ B -> relᵢ (A ⇒ᵢ B) :=
  fun_relF []       RA RB := fun f1 f2 => forall x1 x2, RA x1 x2 -> RB (f1 x1) (f2 x2) ;
  fun_relF (X :: Xs) RA RB := fun x => fun_relF Xs (RA x) (RB x) .
#[global] Arguments fun_relF {Xs A B} RA RB.
#[global] Notation "RA ⇒ᵣ RB" := (fun_relF RA RB) (at level 30).

Equations eq_relF Xs (A : Fam Xs) : relᵢ A :=
  eq_relF []       A := eq ;
  eq_relF (X :: Xs) A := fun x => eq_relF Xs (A x) .
#[global] Arguments eq_relF {Xs A}.
#[global] Notation eqᵢ := eq_relF.

Equations forall_relF Xs {A : Fam Xs} : relᵢ A -> relation ∀[A]ᵢ :=
  forall_relF []       R := R ;
  forall_relF (X :: Xs) R := fun f1 f2 => forall x, forall_relF Xs (R x) (f1 x) (f2 x) .
#[global] Arguments forall_relF {Xs A} R.
#[global] Notation "∀[ R ]ᵣ" := (forall_relF R).
