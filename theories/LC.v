From Coq.Logic Require Import FunctionalExtensionality.
From ExtLib.Structures Require Import Functor Monad.
From ExtLib.Data Require Import Nat Fin.
From ITree Require Import ITree Events.Dependent Basics.Basics.
Import Monads.
Import MonadNotation.
Open Scope monad_scope.

From Paco Require Import paco.
From Equations Require Import Equations.

Set Primitive Projections.

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

(* foldE with additional data *)
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
Variant termF (X : Type) : Type :=
| VarF : nat -> termF X
| AppF : X -> X -> termF X
| LamF : X -> termF X
.

Arguments VarF {X}.
Arguments AppF {X}.
Arguments LamF {X}.

Equations tmap {X Y} (f : X -> Y) (t : termF X) : termF Y :=
  tmap f (VarF i) := VarF i;
  tmap f (AppF u v) := AppF (f u) (f v);
  tmap f (LamF u) := LamF (f u).

Inductive term : Type := T : termF term -> term.

Notation Var i := (T (VarF i)).
Notation App u v := (T (AppF u v)).
Notation Lam u := (T (LamF u)).
(* itree term definitions *)

Variant termE : Type -> Type :=
| VarC : nat -> termE T0
| AppC : termE T2
| LamC : termE T1
.

Equations t_E2F {X} (e : [ termE ]e X) : termF X :=
  t_E2F (EF (VarC i) k) := VarF i ;
  t_E2F (EF AppC     k) := AppF (k t2_0) (k t2_1) ;
  t_E2F (EF LamC     k) := LamF (k t1_0).

Equations t_F2E {X} (e : termF X) : [ termE ]e X :=
  t_F2E (VarF i) := EF (VarC i) (fun i : T0 => match i with end) ;
  t_F2E (AppF u v) := EF AppC (fun i : T2 => match i with t2_0 => u
                                                        | t2_1 => v end) ;
  t_F2E (LamF u) := EF LamC (fun i : T1 => match i with t1_0 => u end).
  
Lemma t_F2E2F {X} (e : termF X) : t_E2F (t_F2E e) = e.
destruct e; reflexivity.
Qed.

(* /!\ functional extensionality used here *)
Lemma t_E2F2E : forall {X} (e : [ termE ]e X), t_F2E (t_E2F e) = e.
  destruct e as [ R [] k ];
    rewrite ?t_E2F_equation_1, ?t_F2E_equation_1;
    rewrite ?t_E2F_equation_2, ?t_F2E_equation_2;
    rewrite ?t_E2F_equation_3, ?t_F2E_equation_3;
    apply f_equal, functional_extensionality;
    destruct x ;
    reflexivity.
Qed.

Definition termT {X : Type} := itree termE X.
Definition termT0 : Type := itree termE T0.
Definition VarT {X} i : @termT X := wrap (t_F2E (VarF i)).
Definition AppT {X} u v : @termT X := wrap (t_F2E (AppF u v)).
Definition LamT {X} u : @termT X := wrap (t_F2E (LamF u)).

Equations t_ind2it : term -> termT0 :=
  t_ind2it (Var i)   := VarT i ;
  t_ind2it (App u v) := AppT (t_ind2it u) (t_ind2it v) ;
  t_ind2it (Lam u)   := LamT (t_ind2it u)
.

Equations t_it2ind_aux (h : termT0 -> itree void1 term) (t : itree' termE T0) : itree void1 term :=
  t_it2ind_aux h (RetF x) := boom x ;
  t_it2ind_aux h (TauF x) := Tau (h x) ;
  t_it2ind_aux h (VisF (VarC i) k) := ret (Var i) ;
  t_it2ind_aux h (VisF AppC k) := bind (h (k t2_0)) (fun u =>
                                  bind (h (k t2_1)) (fun v => ret (App u v)));
  t_it2ind_aux h (VisF LamC k) := bind (h (k t1_0)) (fun u => ret (Lam u)).
  
               
Definition t_it2ind : termT0 -> itree void1 term :=
  cofix h t := t_it2ind_aux h (observe t).
.  cofix h.
  refine (fun t => t_it2ind_aux h (observe t)).
  cofix h.
  refine (fun t => match observe t with
          | RetF x => boom x
          | TauF t => h t
          | VisF e k => ret (T (tmap _ (t_E2F _)))
          end).
  refine (iter _).
  intro t.
  refine (caseE boom t _).
  intro x.
  refine (let y := t_E2F x in _).
  refine (t_E2F x).


Equations t_shift_aux : [ termE ]e (stateT (nat -> nat) (itree termE) T0)
                      -> stateT (nat -> nat) (itree termE) T0 :=
  t_shift_aux (EF (VarC i) k) e := VarT (e i) ;
  t_shift_aux (EF AppC     k) e := AppT (k t2_0 e) (k t2_1 e) ;
  t_shift_aux (EF LamC     k) e := LamT (k t1_0 (fun i => match i with
                                                        | O => O
                                                        | S i => S (e i)
                                                        end)).
Definition t_shift : termT0 -> (nat -> nat) -> termT0 :=
  foldE_ad (fmap inr # t_shift_aux).


Equations t_subst_aux : [ termE ]e (stateT (nat -> termT0) (itree termE) T0)
                      -> stateT (nat -> termT0) (itree termE) T0 :=
  t_subst_aux (EF (VarC i) k) e := fmap (fun x => pair e x) (e i) ;
  t_subst_aux (EF AppC k)     e := AppT (k t2_0 e) (k t2_1 e) ;
  t_subst_aux (EF LamC k)     e := LamT (k t1_0 (fun i => match i with
                                                  | O => VarT O
                                                  | S i => t_shift (e i) S
                                                  end)).
Definition t_subst : termT0 -> (nat -> termT0) -> termT0 :=
  foldE_ad (fmap inr # t_subst_aux).

Equations env1 (u : termT0) : nat -> termT0 :=
  env1 u O     := u ;
  env1 u (S i) := VarT i.

Definition t_subst1 u v := t_subst u (env1 v).


(******************************)
(* normal forms and evaluation*)

Variant normF (X : Type) : Type :=
| NLamF : X -> normF X
| NRedF : nat -> list X -> normF X
.
Arguments NLamF {X}.
Arguments NRedF {X}.

Inductive norm : Type := N : normF norm -> norm.

Notation NLam u := (N (NLamF u)).
Notation NRed i xs := (N (NRedF i xs)).

Variant normE : Type -> Type :=
| NLamC : normE T1
| NRedC : forall i j : nat, normE (fin j)
.




Definition normT {X : Type} := itree normE X.
Definition normT0 := itree normE T0.

Definition NLamT {X} u : @normT X :=
  Vis NLamC (fun x : T1 => match x with t1_0 => u end).
Definition NRedT {X} (i j : nat) (f : fin j -> @normT X) : @normT X :=
  Vis (NRedC i j) f.

Equations app_many (n : nat) : termT0 -> (fin n -> termT0) -> termT0 :=
  app_many O     x f := x ;
  app_many (S n) x f := AppT (app_many n x (f # FS)) (f F0).

Equations norm2term_aux : [ normE ]e termT0 -> termT0 :=
  norm2term_aux (EF NLamC k)       := LamT (k t1_0);
  norm2term_aux (EF (NRedC i j) k) := app_many j (VarT i) k.

Definition norm2term : normT0 -> termT0 :=
  foldE (fmap inr # norm2term_aux).

Equations eval_aux : [ termE ]e normT0 -> itree normE (termT0 + T0) :=
  eval_aux (EF (VarC i) k) := NRedT i 0 (fun i => match i with end) ;
  eval_aux (EF LamC k) := NLamT (fmap inr (k t1_0)) ;
  eval_aux (EF AppC k) := caseE inr (k t2_0) app_case
  where app_case : [ normE ]e _ ->  _ :=  {
        app_case (EF NLamC       k1) := ret (inl (t_subst1 (norm2term (k1 t1_0))
                                                           (norm2term (k t2_1)))) ;
        app_case (EF (NRedC i j) k1) := vis (NRedC i (S j)) red_arg
        where red_arg : fin (S j) -> _ := {
              red_arg F0     := fmap inr (k t2_1) ;
              red_arg (FS i) := fmap inr (k1 i) }}.
Definition eval : termT0 -> normT0 := foldE eval_aux.
