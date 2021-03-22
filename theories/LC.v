From ExtLib.Structures Require Import Functor Monad.
From ExtLib.Data Require Import Nat Fin.
From ITree Require Import ITree Events.Dependent Basics.Basics.
Import Monads.
Import MonadNotation.
Open Scope monad_scope.

From Paco Require Import paco.
From Equations Require Import Equations.


(*************************)
(* notations and prelude *)
Notation endo T := (T -> T).
Arguments depE : clear implicits.  (* index is usually hard to infer *)
Notation "f # g" := (Basics.compose f g) (at level 60) : function_scope. 

Variant T0 := .
Variant T1 := t1_0.
Variant T2 := t2_0 | t2_1.
Variant T3 := t3_0 | t3_1 | t3_2.

Definition boom {A : Type} (bot : T0) : A := match bot with end.

Variant prod1 (D E : Type -> Type) : Type -> Type :=
  | pair1 : forall {X Y}, D X -> E Y -> prod1 D E (X * Y).

Notation "D *' E" := (prod1 D E) (at level 50).

(********************************************************)
(* Dependent version of stuff in ITree.Interp.Recursion *)
Section dep_rec.

Equations dcalling' {A B} {F : Type -> Type}
          (f : forall a, itree F (B a)) : depE A B ~> itree F :=
dcalling' f _ (Dep a) := f a.

Definition drec {E : Type -> Type} {A B}
           (body : forall a, itree (depE A B +' E) (B a)) :
  forall a, itree E (B a) :=
  fun a => mrec (dcalling' body) (Dep a).

Definition dcall {E A B} (a : A) : itree (depE A B +' E) (B a) :=
  ITree.trigger (inl1 (Dep a)).

(*Definition drec_fix {E : Type -> Type} {A B}
           (body : endo (forall a, itree E (B a)))
  : forall a, itree E (B a)
  := drec (body dcall).*)
End dep_rec.



(**************************)
(* terms and substitution *)

Record eF (E : Type -> Type) (X : Type) := EF {
  eF_R : Type ;
  eF_q : E eF_R ;
  eF_k : eF_R -> X
}.

Notation "[ E ]e" := (eF E).
Arguments EF {E} {X} {eF_R}.
Arguments eF_R {E} {X}.
Arguments eF_q {E} {X}.
Arguments eF_k {E} {X}.

Definition wrap {E X} (t : [ E ]e (itree E X)) : itree E X :=
  vis (eF_q t) (eF_k t).

Instance Functor_E {E} : Functor ([ E ]e) := {|
  fmap _ _ f := fun x => EF (eF_q x) (f # eF_k x)
|}. 
Search "Functor".

Instance Functor_E_itree {E} : Functor ([ E ]e # itree E) := {|
  fmap _ _ f := fun x => EF (eF_q x) (fmap f # eF_k x)
|}.

(*
   \o/ it works
   variation of ITree.Interp.Interp.interp that folds over events instead
   of mapping them
*)

Definition translate_rec {D E : Type -> Type}
           (ctx : D ~> itree (D +' E)) : itree D ~> itree E :=
  fun _ => @interp_mrec _ _ ctx _ # @translate _ _ inl1 _.

Definition foldE {E M X} {FM : Functor M} {MM : Monad M} {IM : MonadIter M}
           (h : [ E ]e (M X) -> M (itree E X + X)%type) : itree E X -> M X
  := iter (fun x => match observe x with
                 | RetF r => ret (inr r)
                 | TauF t => ret (inl t)
                 | VisF e k => h (EF e (iter (ret # inl) # k))
                 end).

Definition foldE_ad {E M A X} {FM : Functor M} {MM : Monad M} {IM : MonadIter M}
           (h : [ E ]e (stateT A M X) -> stateT A M _) (x : itree E X) : A -> M X
  := fmap snd # foldE h x.


Definition caseE {E M X Y} {FM : Functor M} {MM : Monad M} {IM : MonadIter M}
           (f : X -> Y) (x : itree E X) (h : [ E ]e (itree E X) -> M Y) : M Y
  := iter (fun x => match observe x with
                    | RetF r => ret (inr (f r))
                    | TauF t => ret (inl t)
                    | VisF e k => fmap inr (h (EF e k))
                    end) x.

(* usual term definition *)
Inductive term : Type :=
| Var : nat -> term
| App : term -> term -> term
| Lam : term -> term
.

(* itree term definitions *)
Variant termC : Type :=
| VarC : nat -> termC
| AppC : termC
| LamC : termC
.

Equations termA : termC -> Type :=
  termA (VarC _) := T0 ;
  termA AppC     := T2 ;
  termA LamC     := T1
.

Definition termE := depE termC termA.
Definition termT {X : Type} := itree termE X.
Definition termT0 : Type := itree termE T0.

Notation VarE i := (Dep (VarC i)).
Notation AppE := (Dep AppC).
Notation LamE := (Dep LamC).

Definition VarT {X} i : @termT X :=
  Vis (VarE i) (fun x : T0 => match x with end).
Definition AppT {X} u v : @termT X :=
  Vis AppE (fun x : T2 => match x with t2_0 => u | t2_1 => v end).
Definition LamT {X} u : @termT X :=
  Vis LamE (fun x : T1 => match x with t1_0 => u end).

Equations t_evalE : term -> termT0 :=
  t_evalE (Var i)   := VarT i ;
  t_evalE (App u v) := AppT (t_evalE u) (t_evalE v) ;
  t_evalE (Lam u)   := LamT (t_evalE u)
.


Equations t_shift_aux : [ termE ]e (stateT (nat -> nat) (itree termE) T0)
                      -> stateT (nat -> nat) (itree termE) T0 :=
  t_shift_aux (EF (VarE i) k) e := VarT (e i) ;
  t_shift_aux (EF AppE     k) e := AppT (k t2_0 e) (k t2_1 e) ;
  t_shift_aux (EF LamE     k) e := LamT (k t1_0 (fun i => match i with
                                                        | O => O
                                                        | S i => S (e i)
                                                        end)).
Definition t_shift : termT0 -> (nat -> nat) -> termT0 := foldE_ad (fmap inr # t_shift_aux).


Equations t_subst_aux : [ termE ]e (stateT (nat -> termT0) (itree termE) T0)
                      -> stateT (nat -> termT0) (itree termE) T0 :=
  t_subst_aux (EF (VarE i) k) e := fmap (fun x => pair e x) (e i) ;
  t_subst_aux (EF AppE k)     e := AppT (k t2_0 e) (k t2_1 e) ;
  t_subst_aux (EF LamE k)     e := LamT (k t1_0 (fun i => match i with
                                                  | O => VarT O
                                                  | S i => t_shift (e i) S
                                                  end)).
Definition t_subst : termT0 -> (nat -> termT0) -> termT0 := foldE_ad (fmap inr # t_subst_aux).

Equations env1 (u : termT0) : nat -> termT0 :=
  env1 u O     := u ;
  env1 u (S i) := VarT i.

Definition t_subst1 u v := t_subst u (env1 v).


(******************************)
(* normal forms and evaluation*)
Variant normC : Type := NLamC | NRedC : nat -> nat -> normC.
Equations normA : normC -> Type :=
  normA NLamC := T1 ;
  normA (NRedC _ i) := fin i.

Definition normE := depE normC normA.
Definition normT {X : Type} := itree normE X.
Definition normT0 := itree normE T0.

Notation NLamE := (Dep NLamC).
Notation NRedE i j := (Dep (NRedC i j)).

Definition NLamT {X} u : @normT X :=
  Vis NLamE (fun x : T1 => match x with t1_0 => u end).
Definition NRedT {X} (i j : nat) (f : fin j -> @normT X) : @normT X :=
  Vis (NRedE i j) f.

Equations norm2term_aux : [ normE ]e termT0 -> termT0 :=
  norm2term_aux (EF NLamE k)       := LamT (k t1_0);
  norm2term_aux (EF (NRedE i j) k) := spine j (VarT i) k
  where spine (n : nat) : termT0 -> (fin n -> termT0) -> termT0 := {
    spine O     x f := x ;
    spine (S i) x f := spine i (AppT x (f (F0))) (f # FS) }.
Definition norm2term : normT0 -> termT0 := foldE (fmap inr # norm2term_aux).

Equations eval_aux : [ termE ]e normT0 -> itree normE (termT0 + T0) :=
  eval_aux (EF (VarE i) k) := NRedT i 0 (fun i => match i with end) ;
  eval_aux (EF LamE k) := NLamT (fmap inr (k t1_0)) ;
  eval_aux (EF AppE k) := caseE inr (k t2_0) app_case
  where app_case : [ normE ]e _ ->  _ :=  {
        app_case (EF NLamE       k1) := ret (inl (t_subst1 (norm2term (k1 t1_0))
                                                           (norm2term (k t2_1)))) ;
        app_case (EF (NRedE i j) k1) := vis (NRedE i (S j)) red_arg
        where red_arg : normA (NRedC i (S j)) -> _ := {
              red_arg F0     := fmap inr (k t2_1) ;
              red_arg (FS i) := fmap inr (k1 i) }
        }.

Definition eval : termT0 -> normT0 := foldE eval_aux.
