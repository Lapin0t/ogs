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

Definition k_ctx : Type := Ctx.ctx kont.
Bind Scope ctx_scope with k_ctx.

Equations k_move : kont -> Type :=
  k_move (KCtx x) := a_val x ;
  k_move (KVar x) := t_obs x .

Definition lassen_c_ix : Type := frame .
Definition lassen_s_ix : Type := (frame + neg_ctx) * frame .

Equations lassen_c_move : lassen_c_ix -> Type :=
  lassen_c_move c_i := any t_obs (fst c_i) + a_val (snd c_i) .

Equations lassen_c_next c_i : lassen_c_move c_i -> lassen_s_ix :=
  lassen_c_next c_i (inl a) := (inl (any_elim (@t_obs_nxt) _ a) , c_i) ;
  lassen_c_next c_i (inr a) := (inr (a_cext a) , c_i) .

Equations lassen_s_move : lassen_s_ix -> Type :=
  lassen_s_move (inl s_i , _) := any t_obs (fst s_i) + a_val (snd s_i) ;
  lassen_s_move (inr s_i , _) := any t_obs s_i .

Equations lassen_s_next s_i : lassen_s_move s_i -> lassen_c_ix :=
  lassen_s_next (inl s_i , c_i) (inl a) :=
    ((fst c_i +▶ any_elim (@t_obs_args) _ a)%ctx ,
     any_elim (@t_obs_goal) _ a) ;
  lassen_s_next (inl s_i , c_i) (inr a) := ((fst c_i +▶ a_cext a)%ctx , snd c_i) ;
  lassen_s_next (inr s_i , c_i) a :=
    ((fst c_i +▶ any_elim (@t_obs_args) _ a)%ctx ,
     any_elim (@t_obs_goal) _ a) .

Definition g_lassen : game' lassen_c_ix lassen_s_ix :=
  {| client := {| move := lassen_c_move ;
                  next := lassen_c_next |} ;
     server := {| move := lassen_s_move ;
                  next := lassen_s_next |} |} .

(*
Definition kctx_of_nctx (Γ : neg_ctx) : k_ctx := map KVar Γ .
Definition kctx_of_frame (s : frame) : k_ctx := kctx_of_nctx (fst s) ▶ KCtx (snd s).

Variant k_ext : Type :=
| KPush : frame -> k_ext
| KPop : neg_ctx -> k_ext
.

Equations kctx_of_kext : k_ext -> k_ctx :=
  kctx_of_kext (KPush s) := kctx_of_frame s ;
  kctx_of_kext (KPop Δ)  := kctx_of_nctx Δ .

Definition ext_kctx (ks : k_ctx) (e : k_ext) : k_ctx
  := ks +▶ kctx_of_kext e.

Equations ext_frame : frame -> k_ext -> frame :=
  ext_frame u (KPush v) := ((fst u +▶ fst v)%ctx , snd v) ;
  ext_frame u (KPop Γ)  := ((fst u +▶ Γ)%ctx , snd u) .

Equations k_next (k : kont) : k_move k -> k_ext :=
  k_next (KCtx x) a := KPop (a_cext a) ;
  k_next (KVar x) o := KPush (t_obs_nxt o) .

Definition g_lassen : game' frame (k_ctx * frame) :=
  {| client := {| move := fun i => any k_move (kctx_of_frame i) ;
                  next := fun i m => (kctx_of_kext (any_elim k_next _ m) , i) |} ;
     server := {| move := fun i => any k_move (fst i) ;
                  next := fun i m => ext_frame (snd i) (any_elim k_next _ m) |} |} .

Equations inj_ogs_enf {s} : e_nf' s -> itree g_lassen (eval_arg' +ᵢ ∅ᵢ) s :=
  inj_ogs_enf (NVal v) := Vis (Any _ _ top (a_of_val v) : qry g_lassen _) _ ;
  inj_ogs_enf (NRed E i v) := _ .

  destruct s as [Γ x]; intros [ v | ? ? E i e ]; cbn in *.
  + unshelve refine (Vis (Any _ _ top _ : qry g_lassen _) _).
    refine (a_of_val v).
    intros [k i m]; cbn in i |- *.
    revert m.
    rewrite <- (has_map2 _ _ i).
    intros m. cbn in m. cbn.
    refine (Ret (inl _)).
    refine (earg_start (t_obs_apply m (cext_get _ v (has_map1 _ _ i)))).
  + unshelve refine (Vis _ _).
    destruct (neg_var i).
    refine (Any _ _ (pop _) _). refine (map_has KVar _ (has_map1 _ _ i)).
    cbn. Check (has_map2 of_n_ty Γ i).
    cbn.
    cbn. Check (t)
    cbn. Check (cext_get).
    destruct r.
    dependent elimination x0.
    - shelve.

*)

Definition half_ogs : half_game (k_ctx * k_ctx) (k_ctx * k_ctx) :=
  {| move := fun i => any k_move (fst i) ;
     next := fun i m => (ext_kctx (snd i) (any_elim k_next _ m) , fst i) |} .

Definition g_ogs : game' (k_ctx * k_ctx) (k_ctx * k_ctx) :=
  {| client := half_ogs ; server := half_ogs |}.

Definition ogs := itree g_ogs ∅ᵢ.

Section composition.

Variant _compo_arg (hideₚ hideₒ fullₚ fullₒ : k_ctx) : Type :=
| _c_ap  : ogs (fullₚ , fullₒ) -> iforest g_ogs ∅ᵢ (hideₚ , hideₒ)
         -> _compo_arg hideₚ hideₒ fullₚ fullₒ
| _c_pa : iforest g_ogs ∅ᵢ (fullₒ , fullₚ) -> ogs (hideₒ , hideₚ)
        -> _compo_arg hideₚ hideₒ fullₚ fullₒ
  .
Arguments _c_pa {hideₚ hideₒ fullₚ fullₒ} a b.
Arguments _c_ap {hideₚ hideₒ fullₚ fullₒ} a b.

Definition _compo : forall showₚ showₒ hideₚ hideₒ fullₚ fullₒ
                    , showₚ ⊎ hideₚ ≡ fullₚ
                    -> showₒ ⊎ hideₒ ≡ fullₒ
                    -> _compo_arg hideₚ hideₒ fullₚ fullₒ
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

Definition compo_ap {sₚ sₒ hₚ hₒ fₚ fₒ} (cₚ : sₚ ⊎ hₚ ≡ fₚ) (cₒ : sₒ ⊎ hₒ ≡ fₒ)
      := fun a b => _compo cₚ cₒ (_c_ap a b).

Definition compo_pa {sₚ sₒ hₚ hₒ fₚ fₒ} (cₚ : sₚ ⊎ hₚ ≡ fₚ) (cₒ : sₒ ⊎ hₒ ≡ fₒ)
      := fun a b => _compo cₚ cₒ (_c_pa a b).
Check compo_ap.

(**********)
(* PROOFS *)
(**********)


Variant _compo_arg_eq (hideₚ hideₒ fullₚ fullₒ : list kont) : Type :=
| _c_pa2 (a0 a1 : iforest g_ogs ∅ᵢ (fullₒ , fullₚ)) (b0 b1 : ogs (hideₒ , hideₚ))
  : (forall r, a0 r ≈ a1 r) -> b0 ≈ b1 -> _compo_arg_eq hideₚ hideₒ fullₚ fullₒ 
| _c_ap2 (a0 a1 : ogs (fullₚ , fullₒ)) (b0 b1 : iforest g_ogs ∅ᵢ (hideₚ , hideₒ))
  : a0 ≈ a1 -> (forall r, b0 r ≈ b1 r) -> _compo_arg_eq hideₚ hideₒ fullₚ fullₒ 
  .
Arguments _c_pa2 {hideₚ hideₒ fullₚ fullₒ} a0 a1 b0 b1 ea eb.
Arguments _c_ap2 {hideₚ hideₒ fullₚ fullₒ} a0 a1 b0 b1 ea eb.

Equations _c_arg_eq_l {hₚ hₒ fₚ fₒ} : _compo_arg_eq hₚ hₒ fₚ fₒ
                                    -> _compo_arg hₚ hₒ fₚ fₒ :=
  _c_arg_eq_l (_c_pa2 a0 a1 b0 b1 ea eb) := _c_pa a0 b0 ;
  _c_arg_eq_l (_c_ap2 a0 a1 b0 b1 ea eb) := _c_ap a0 b0 .
    
Equations _c_arg_eq_r {hₚ hₒ fₚ fₒ} : _compo_arg_eq hₚ hₒ fₚ fₒ
                                    -> _compo_arg hₚ hₒ fₚ fₒ :=
  _c_arg_eq_r (_c_pa2 a0 a1 b0 b1 ea eb) := _c_pa a1 b1 ;
  _c_arg_eq_r (_c_ap2 a0 a1 b0 b1 ea eb) := _c_ap a1 b1 .
    

(* bisimilarity of composition of pairwise bisimilar arguments *)
Lemma _compo_cong {sₚ sₒ hₚ hₒ fₚ fₒ} (cₚ : sₚ ⊎ hₚ ≡ fₚ) (cₒ : sₒ ⊎ hₒ ≡ fₒ)
      (a : _compo_arg_eq hₚ hₒ fₚ fₒ)
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

a ≈obs b := forall E, norm (E[a]) ≈ norm (E[b]) 

lem2 : inj_ogs (E[t]) = _compo (inj_ogs_ctx E, inj_ogs t)


THM1: inj_ogs a ≈ inj_ogs b -> a ≈obs b
THM2: a ≈obs b -> inj_ogs a ≈ inj_ogs b
***)
