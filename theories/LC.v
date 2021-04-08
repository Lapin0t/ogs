From Coq.Logic Require Import FunctionalExtensionality.
Require Import RelationClasses.
From ExtLib.Structures Require Import Functor Monad.
From ExtLib.Data Require Import Nat Fin.
From ITree Require Import
     ITree
     Events.Dependent
     Basics.Basics
     Eq.Eq
     Interp.InterpFacts
     Interp.RecursionFacts
     Interp.TranslateFacts.
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

Instance Functor_E_itree {E} : Functor ([ E ]e # itree E) := {|
  fmap _ _ f := fun x => EF (eF_q x) (fmap f # eF_k x)
|}.

(*****************)

(*
Section euttG_bind.
Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).
Context (rL rH gL gH : itree E R1 -> itree E R2 -> Prop).
Variant euttG_bind_clo : itree E R1 -> itree E R2 -> Prop :=
| i_gbind_clo t1 t2 k1 k2 :
      euttG RR rL rH gL gH t1 t2 ->
      (forall u1 u2, RR u1 u2 -> euttG RR rL rH gL gH (k1 u1) (k2 u2))
  ->  euttG_bind_clo (ITree.bind t1 k1) (ITree.bind t2 k2)
.
Hint Constructors euttG_bind_clo: core.
Print eqit_.
Lemma euttG_clo_bind vclo
      (MON: monotone2 vclo)
      (CMP: compose (eqitC RR b1 b2) vclo <3= compose vclo (eqitC RR b1 b2))
      (ID: id <3= vclo) :
    euttG_bind_clo b1 b2 <3= gupaco2 (eqit_ RR b1 b2 vclo) (eqitC RR b1 b2).
*)

(*****************)

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

Inductive t_ctx (X : Type) : Type :=
| CHole : t_ctx X
| CVar : nat -> t_ctx X
| CApp_l : X -> t_ctx X -> t_ctx X
| CApp_r : t_ctx X -> X -> t_ctx X
| CLam : t_ctx X -> t_ctx X
.

Equations plug (C : t_ctx term) (x : term) : term :=
  plug CHole        t := t ;
  plug (CVar i)     t := Var i ;
  plug (CApp_l u C) t := App u (plug C t) ;
  plug (CApp_r C u) t := App (plug C t) u ;
  plug (CLam C)     t := Lam (plug C t).


(* itree term definitions *)


Equations t_rename (f : nat -> nat) (t : term) : term :=
  t_rename f (Var i) := Var (f i) ;
  t_rename f (App u v) := App (t_rename f u) (t_rename f v) ;
  t_rename f (Lam u) := Lam (t_rename f' u)
    where f' : nat -> nat := {
          f' O     := O ;
          f' (S i) := S (f i)}.

Equations t_subst (f : nat -> term) (t : term) : term :=
  t_subst f (Var i) := f i ;
  t_subst f (App u v) := App (t_subst f u) (t_subst f v) ;
  t_subst f (Lam u) := Lam (t_subst f' u)
    where f' : nat -> term := {
          f' O     := Var O ;
          f' (S i) := t_rename S (f i)}.

Equations env1 (u : term) : nat -> term :=
  env1 u O     := u ;
  env1 u (S i) := Var i.

Definition t_subst1 u v := t_subst (env1 v) u.


(******************************)
(* normal forms and evaluation*)

Variant normF (X : Type) : Type :=
| NLamF : X -> normF X
| NAppF : nat -> list X -> normF X
.

Arguments NLamF {X}.
Arguments NAppF {X}.

Variant whn : Type := W : normF term -> whn.
Inductive norm : Type := N : normF norm -> norm.

Search "whn".

Notation WLam u := (W (NLamF u)).
Notation WApp i xs := (W (NAppF i xs)).
Notation NLam u := (N (NLamF u)).
Notation NApp i xs := (N (NAppF i xs)).

Variant boehmE : Type -> Type :=
| BLamC : boehmE T1
| BAppC : forall i j : nat, boehmE (fin j)
.

Equations l_get {X} (xs : list X) : fin (length xs) -> X :=
  l_get (cons x xs) F0     := x ;
  l_get (cons x xs) (FS i) := l_get xs i.

Definition BLamT {X} u : itree boehmE X :=
  Vis BLamC (fun x => match x with t1_0 => u end).
Definition BAppT {X} i xs : itree boehmE X :=
  Vis (BAppC i (length xs)) (l_get xs).
Check (@Vis _ _).


Definition normT := itree boehmE T0.

Equations app_many : term -> list term -> term :=
  app_many a nil := a ;
  app_many a (cons x xs) := App (app_many a xs) x.

Equations term_of_whn (w : whn) : term :=
  term_of_whn (WLam u) := Lam u ;
  term_of_whn (WApp i xs) := app_many (Var i) xs.

Equations ev_whn' (t : term) : itree (callE term whn +' void1) whn :=
  ev_whn' (Var i) := ret (WApp i nil) ;
  ev_whn' (App u v) :=
    u' <- call u ;;
    v' <- call v ;;
    match u' with
    | WLam w => call (t_subst1 w (term_of_whn v'))
    | WApp i xs => ret (WApp i (cons (term_of_whn v') xs))
    end ;
  ev_whn' (Lam u) := ret (WLam u).

Definition ev_whn : term -> itree void1 whn := rec ev_whn'.

Equations term_of_norm (u : norm) : term :=
  term_of_norm (NLam u) := Lam (term_of_norm u) ;
  term_of_norm (NApp i xs) := app_many (Var i) (List.map term_of_norm xs).

Equations ev_norm' (t : term) : itree (callE term norm +' void1) norm :=
  ev_norm' (Var i) := ret (NApp i nil) ;
  ev_norm' (App u v) :=
    u' <- call u ;;
    v' <- call v ;;
    match u' with
    | NLam w => call (t_subst1 (term_of_norm w) (term_of_norm v'))
    | NApp i xs => ret (NApp i (cons v' xs))
    end ;
  ev_norm' (Lam u) := u' <- call u ;; ret (NLam u').

Definition ev_norm : term -> itree void1 norm := rec ev_norm'.

Lemma norm_cong (s t : term) (p : ev_norm s ≈ ev_norm t)
  : forall C : t_ctx term, ev_norm (plug C s) ≈ ev_norm (plug C t).
  induction C.
  + rewrite 2 plug_equation_1.
    eauto.
  + reflexivity.
  + rewrite 2 plug_equation_3.
    unfold ev_norm.
    rewrite 2 rec_as_interp.
    rewrite 2 ev_norm'_equation_2; unfold ";;";simpl.
    rewrite 2 interp_bind.
    apply eutt_eq_bind.
    intro u.
    rewrite 2 interp_bind.
    eapply eutt_clo_bind.
    - rewrite 2 interp_recursive_call.
      exact IHC.
    - intros u1 u2 e; rewrite e; reflexivity.
  + rewrite 2 plug_equation_4.
    unfold ev_norm.
    rewrite 2 rec_as_interp.
    rewrite 2 ev_norm'_equation_2; unfold ";;"; simpl.
    rewrite 2 interp_bind.
    eapply eutt_clo_bind.
    - rewrite 2 interp_recursive_call.
      exact IHC.
    - intros u1 u2 e; rewrite e; reflexivity.
  + rewrite 2 plug_equation_5.
    unfold ev_norm.
    rewrite 2 rec_as_interp.
    rewrite 2 ev_norm'_equation_3; unfold ";;"; simpl.
    rewrite 2 interp_bind.
    eapply eutt_clo_bind.
    - rewrite 2 interp_recursive_call.
      exact IHC.
    - intros u1 u2 e; rewrite e; reflexivity.
Qed.


(* w_inj k (W x) := wrap (F2E (fmap k x)) *)
(* this is because normF == [ boehmE ]e *)
Equations w_inj {X} : (term -> itree boehmE X) -> whn -> itree boehmE X :=
  w_inj k (WLam u) := Vis BLamC (fun x => match x with t1_0 => k u end);
  w_inj k (WApp i xs) := Vis (BAppC i (length xs)) (k # l_get xs).

(* magic :D *)
Definition ev_boehmE' (t : term) : itree boehmE (term + T0) :=
  ITree.bind (translate elim_void1 (ev_whn t)) (w_inj (ret # inl)).
Definition eval_boehmE : term -> normT := iter ev_boehmE'.

Equations elim_r {T} (x : T + T0) : T := elim_r (inl t) := t.

(*
Lemma boehmE'_cong {C : t_ctx term} (s t : term) (p : eval_boehmE s ≈ eval_boehmE t)
  : eutt (fun a b => eval_boehmE (elim_r a) ≈ eval_boehmE (elim_r b))
         (ev_boehmE' (plug C s))
         (ev_boehmE' (plug C t)).
  induction C.
  + rewrite 2 plug_equation_1.
*)

Lemma boehmE_cong {C : t_ctx term} (s t : term) (p : eval_boehmE s ≈ eval_boehmE t)
  : eval_boehmE (plug C s) ≈ eval_boehmE (plug C t).
  induction C.
  + rewrite 2 plug_equation_1.
    exact p.
  + rewrite 2 plug_equation_2.
    reflexivity.
  + rewrite 2 plug_equation_3.
    unfold eval_boehmE, ";;", iter, MonadIter_itree; simpl.
    rewrite 2 unfold_iter.
    eapply eutt_clo_bind.
    * unfold ev_boehmE', ev_whn.
      rewrite 2 rec_as_interp.
      eapply eutt_clo_bind.
      - eapply eutt_translate'.
        rewrite 2 ev_whn'_equation_2; unfold ";;"; simpl.
        rewrite 2 interp_bind.
        eapply eutt_clo_bind.
          reflexivity.
          intros u1 u2 e.
          rewrite 2 interp_bind.
          eapply eutt_clo_bind.
          rewrite 2 interp_recursive_call.
          fold ev_whn.
          
      eapply eutt_clo_bind.
      - rewrite 2 interp_bind.
        Search translate.
        eapply eutt_translate'.
      Search translate.
  unfold eval_boehmE, ";;", iter, MonadIter_itree; simpl.
  rewrite 2 unfold_iter.
  rewrite 2 bind_bind.
  + 
  Search ITree.iter.
  induction C.
    Search ITree.iter.
    rewrite 2 unfold_iter.
    rewrite 2 bind_bind; simpl.
  
  + rewrite plug_equation_1,plug_equation_1.
    exact (@RelationClasses.reflexivity _ _ (Reflexive_eqit eq _ _ _) _).
  + rewrite plug_equation_2,plug_equation_2.
    compute [eval_boehmE].
    rewrite unfold_iter,unfold_iter.
    Search ITree.iter.
