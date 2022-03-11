Set Primitive Projections.

From Coq Require Import Logic.
Import EqNotations.
Require Import Psatz.

From ExtLib.Data Require Import List Fin.

From OGS Require Import Utils.
From OGS.ITree Require Import Cat Event Dual ITree Rec Angelic Eq.
From OGS.STLC Require Import Ctx Syntax.

From Equations Require Import Equations.
Set Equations Transparent.


From OGS.ITree Require Import Eq.
From Paco Require Import paco.
Require Import Coq.Program.Equality.

Variant kont : Type :=
| KCtx : ty -> kont
| KVar : neg_ty -> kont
.

Equations k_move : kont -> Type :=
  k_move (KCtx x) := a_val x ;
  k_move (KVar x) := t_obs x .

Equations k_next (k : kont) : k_move k -> list kont :=
  k_next (KCtx x) a := map KVar (a_cext a) ;
  k_next (KVar x) o := cons (KCtx (t_obs_goal o)) (map KVar (t_obs_args o)) .

(*
Definition base : half_game (list kont) (list kont) :=
  {| move := any k_move ;
     next := any_elim k_next |} .

Definition g_lassen : game' (list kont) (list kont * list kont) :=
  {| client := {| move := fun xs => any k_move xs ;
                  next := fun xs m => (any_elim k_next xs m , xs) |} ;
     server := {| move := fun ys => any k_move (fst ys) ;
                  next := fun ys m => app (any_elim k_next (fst ys) m) (snd ys) |} |} .
*)

Definition half_ogs : half_game (list kont * list kont) (list kont * list kont) :=
  {| move := fun xs => any k_move (fst xs) ;
     next := fun xs m => (app (any_elim k_next _ m) (snd xs) , fst xs) |} .

Definition g_ogs : game' (list kont * list kont) (list kont * list kont) :=
  {| client := half_ogs ; server := half_ogs |}.

Definition ogs := itree g_ogs ∅ᵢ.

Section composition.
  
Variant _compo_arg (showₚ showₒ hideₚ hideₒ fullₚ fullₒ : list kont) : Type :=
| _c_ap  : ogs (fullₚ , fullₒ)
         -> iforest g_ogs ∅ᵢ (hideₚ , hideₒ)
         -> _compo_arg showₚ showₒ hideₚ hideₒ fullₚ fullₒ
| _c_pa : iforest g_ogs ∅ᵢ (fullₒ , fullₚ)
        -> ogs (hideₒ , hideₚ)
        -> _compo_arg showₚ showₒ hideₚ hideₒ fullₚ fullₒ
  .
Arguments _c_pa {showₚ showₒ hideₚ hideₒ fullₚ fullₒ} a b.
Arguments _c_ap {showₚ showₒ hideₚ hideₒ fullₚ fullₒ} a b.

Definition _compo : forall showₚ showₒ hideₚ hideₒ fullₚ fullₒ
                    , showₚ ⊎ hideₚ ≡ fullₚ
                    -> showₒ ⊎ hideₒ ≡ fullₒ
                    -> _compo_arg showₚ showₒ hideₚ hideₒ fullₚ fullₒ
                    -> ogs (showₚ , showₒ).
  cofix CIH.
  intros ? ? ? ? ? ? cₚ cₒ [a b|a b].
  - destruct (observe a).
    + destruct r.
    + exact (Tau (CIH _ _ _ _ _ _ cₚ cₒ (_c_ap t b))).
    + destruct e as [x i m].
      destruct (cover_split cₚ i) as [j|j].
      * refine (Vis (Any _ _ j m : qry g_ogs (_,_)) (fun r => _)).
        refine (CIH _ _ _ _ _ _ _ (ext_cover_l _ cₒ)
                    (_c_ap (k (r_any (r_cover_l (ext_cover_l _ cₒ)) r)) b)).
        refine (@cat_cover _ _ _ _ ∅ _ _ cₚ _); destruct r; refine (cover_nil_r).
      * exact (Tau (CIH _ _ _ _ _ _ cₚ (ext_cover_r _ cₒ)
                        (_c_pa k (b (Any _ _ j m))))).
  - destruct (observe b).
    + destruct r.
    + exact (Tau (CIH _ _ _ _ _ _ cₚ cₒ (_c_pa a t))).
    + destruct e as [x i m].
      exact (Tau (CIH _ _ _ _ _ _ (ext_cover_r _ cₚ) cₒ
                      (_c_ap (a (Any _ _ (r_cover_r cₒ i) m)) k))).      
Defined.
Arguments _compo {_ _ _ _ _ _}.

Definition compo_ap {showₚ showₒ hideₚ hideₒ fullₚ fullₒ}
      (cₚ : showₚ ⊎ hideₚ ≡ fullₚ) (cₒ : showₒ ⊎ hideₒ ≡ fullₒ)
      (a : ogs (fullₚ , fullₒ)) (b : iforest g_ogs ∅ᵢ (hideₚ , hideₒ))
      : ogs (showₚ , showₒ)
  := _compo cₚ cₒ (_c_ap a b).

Definition compo_pa {showₚ showₒ hideₚ hideₒ fullₚ fullₒ}
      (cₚ : showₚ ⊎ hideₚ ≡ fullₚ) (cₒ : showₒ ⊎ hideₒ ≡ fullₒ)
      (a : iforest g_ogs ∅ᵢ (fullₒ , fullₚ)) (b : ogs (hideₒ , hideₚ))
      : ogs (showₚ , showₒ)
  := _compo cₚ cₒ (_c_pa a b).

(**********)
(* PROOFS *)
(**********)


Variant _compo_arg_eq (showₚ showₒ hideₚ hideₒ fullₚ fullₒ : list kont) : Type :=
| _c_pa2 (a0 a1 : iforest g_ogs ∅ᵢ (fullₒ , fullₚ)) (b0 b1 : ogs (hideₒ , hideₚ))
  : (forall r, a0 r ≈ a1 r) -> b0 ≈ b1 -> _compo_arg_eq showₚ showₒ hideₚ hideₒ fullₚ fullₒ 
| _c_ap2 (a0 a1 : ogs (fullₚ , fullₒ)) (b0 b1 : iforest g_ogs ∅ᵢ (hideₚ , hideₒ))
  : a0 ≈ a1 -> (forall r, b0 r ≈ b1 r) -> _compo_arg_eq showₚ showₒ hideₚ hideₒ fullₚ fullₒ 
  .
Arguments _c_pa2 {showₚ showₒ hideₚ hideₒ fullₚ fullₒ} a0 a1 b0 b1 ea eb.
Arguments _c_ap2 {showₚ showₒ hideₚ hideₒ fullₚ fullₒ} a0 a1 b0 b1 ea eb.

Equations _c_arg_eq_l {sₚ sₒ hₚ hₒ fₚ fₒ}
  : _compo_arg_eq sₚ sₒ hₚ hₒ fₚ fₒ -> _compo_arg sₚ sₒ hₚ hₒ fₚ fₒ :=
  _c_arg_eq_l (_c_pa2 a0 a1 b0 b1 ea eb) := _c_pa a0 b0 ;
  _c_arg_eq_l (_c_ap2 a0 a1 b0 b1 ea eb) := _c_ap a0 b0 .
    
Equations _c_arg_eq_r {sₚ sₒ hₚ hₒ fₚ fₒ}
  : _compo_arg_eq sₚ sₒ hₚ hₒ fₚ fₒ -> _compo_arg sₚ sₒ hₚ hₒ fₚ fₒ :=
  _c_arg_eq_r (_c_pa2 a0 a1 b0 b1 ea eb) := _c_pa a1 b1 ;
  _c_arg_eq_r (_c_ap2 a0 a1 b0 b1 ea eb) := _c_ap a1 b1 .
    

(* bisimilarity of composition of pairwise bisimilar arguments *)
Lemma _compo_cong {sₚ sₒ hₚ hₒ fₚ fₒ} (cₚ : sₚ ⊎ hₚ ≡ fₚ) (cₒ : sₒ ⊎ hₒ ≡ fₒ)
      (a : _compo_arg_eq sₚ sₒ hₚ hₒ fₚ fₒ)
      : _compo cₚ cₒ (_c_arg_eq_l a) ≈ _compo cₚ cₒ (_c_arg_eq_r a).
  revert sₚ sₒ hₚ hₒ fₚ fₒ cₚ cₒ a.
  pcofix CIH; pstep.
  intros ? ? ? ? ? ? ? ? [ a0 a1 b0 b1 ea eb | a0 a1 b0 b1 ea eb ].
  - cbv [eqit_ observe]; cbn; cbv [observe].
    punfold eb; cbv [eqit_ observe _observe] in eb; cbn in eb.
    dependent induction eb; cbv [_observe]; try rewrite <- x0; try rewrite <- x.
    + destruct r1.
    + econstructor; right.
      refine (CIH _ _ _ _ _ _ _ _ (_c_pa2 _ _ _ _ ea _)).
      destruct REL; [exact H|destruct H].
    + destruct e.
      econstructor; right.
      refine (CIH _ _ _ _ _ _ _ _ (_c_ap2 _ _ _ _ (ea (Any k_move _ _ _)) _)).
      intro r0; destruct (REL r0); [exact H|destruct H].
    + econstructor; auto.
      cbv [observe]; cbn; cbv [observe].
      exact (IHeb CIH _ _ _ _ _ _ ea eq_refl eq_refl).
    + econstructor; auto.
      cbv [observe]; cbn; cbv [observe].
      exact (IHeb CIH _ _ _ _ _ _ ea eq_refl eq_refl).
  - cbv [eqit_ observe]; cbn; cbv [observe].
    punfold ea; cbv [eqit_ observe _observe] in ea; cbn in ea.
    dependent induction ea; cbv [_observe]; try rewrite <- x0; try rewrite <- x.
    + destruct r1.
    + econstructor; right.
      refine (CIH _ _ _ _ _ _ _ _ (_c_ap2 _ _ _ _ _ eb)).
      destruct (REL); [exact H|destruct H].
    + destruct e; destruct (cover_split cₚ h).
      * econstructor; right.
        refine (CIH _ _ _ _ _ _ _ _ (_c_ap2 _ _ _ _ _ eb)).
        destruct (REL (r_any (r_cover_l (ext_cover_l _ cₒ)) v));
          [exact H|destruct H].
      * econstructor; right.
        refine (CIH _ _ _ _ _ _ _ _ (_c_pa2 _ _ _ _ _ (eb (Any _ _ _ _)))).
        intro r0; destruct (REL r0); [exact H|destruct H].
    + econstructor; auto.
      cbv [observe]; cbn; cbv [observe].
      refine (IHea CIH _ _ _ _ _ _ eq_refl eq_refl eb).
    + econstructor; auto.
      cbv [observe]; cbn; cbv [observe].
      refine (IHea CIH _ _ _ _ _ _ eq_refl eq_refl eb).
Qed.
Check _compo_cong.

(***
lem1 : norm a ≈ norm b -> inj_ogs a ≈ inj_ogs b
lem2 : inj_ogs a ≈ inj_ogs b -> norm a ≈ norm b

a ≈obs b := forall E, norm (E[a]) ≈ norm (E[b]) 

lem2 : inj_ogs (E[t]) = _compo (inj_ogs_ctx E, inj_ogs t)


THM1: inj_ogs a ≈ inj_ogs b -> a ≈obs b
THM2: a ≈obs b -> inj_ogs a ≈ inj_ogs b
***)
