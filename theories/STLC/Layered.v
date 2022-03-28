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

(*|
``move_t`` can be seen as an extension of negative types, ``KVar``
being an injection and ``KCtx x`` encoding something like ``¬ x``, or ``x → ⊥``.
|*)
Variant move_t : Type :=
| KCtx : ty -> move_t
| KVar : neg_ty -> move_t
.
Derive NoConfusion for move_t.

Equations k_move : move_t -> Type :=
  k_move (KCtx x) := a_val x ;
  k_move (KVar x) := t_obs x .

Definition k_ctx : Type := Ctx.ctx move_t.
Bind Scope ctx_scope with k_ctx.

Definition KVars (Γ : neg_ctx) : k_ctx := map KVar Γ .
Definition k_has_vars (ks : k_ctx) (Γ : neg_ctx) := KVars Γ ⊆ ks.
Definition k_has_ty (ks : k_ctx) (x : ty) := ks ∋ KCtx x.
Definition k_has_frame (ks : k_ctx) (f : frame) :=
  k_has_vars ks (fst f) * k_has_ty ks (snd f) .

Variant move_ext : move_t -> Type :=
| KECtx {x} : frame -> move_ext (KCtx x)
| KEVar {x} : neg_ctx -> move_ext (KVar x)
.
Derive NoConfusion for move_ext.

Equations move_ext_valid (ks : k_ctx) (k : move_t) : move_ext k -> Type :=
  move_ext_valid ks (KCtx x) (KECtx f) := k_has_frame ks f ;
  move_ext_valid ks (KVar x) (KEVar Γ) := k_has_vars ks Γ.

Equations move_ext_valid_lift {ks ks'} (k : move_t) (e : move_ext k)
  : move_ext_valid ks k e -> move_ext_valid (ks +▶ ks') k e :=
  move_ext_valid_lift (KCtx x) (KECtx s) v :=
    (fun _ i => r_concat_l _ _ _ (fst v _ i) ,
     r_concat_l _ _ _ (snd v)) ;
  move_ext_valid_lift (KVar x) (KEVar s) v := fun _ i => r_concat_l _ _ _ (v _ i) .

Definition move_ext' : Type := { k : move_t & move_ext k }.

(*|
Consequently, ``k_move`` extends the set of observations (or "moves" or "queries")
on extended negative types.
|*)
Equations k_val (k : move_t) : move_ext k -> Type :=
  k_val (KCtx x) (KECtx f) := e_ctx (fst f) (snd f) x ;
  k_val (KVar x) (KEVar Γ) := e_val Γ x .
Definition k_val' (k : move_ext') : Type := k_val (projT1 k) (projT2 k).

Variant k_ext : Type :=
| KPush : frame -> k_ext
| KPop  : neg_ctx -> k_ext
.

Equations k_next (k : move_t) : k_move k -> k_ext :=
  k_next (KCtx x) a := KPop (a_cext a) ;
  k_next (KVar x) o := KPush (t_obs_nxt o) .

Equations kctx_of_kext : k_ext -> k_ctx :=
  kctx_of_kext (KPush s) := KVars (fst s) ▶ KCtx (snd s)  ;
  kctx_of_kext (KPop Δ)  := KVars Δ .

Definition ext_kctx (ks : k_ctx) (e : k_ext) : k_ctx
  := ks +▶ kctx_of_kext e.

Equations ext_frame : frame -> k_ext -> frame :=
  ext_frame u (KPush v) := ((fst u +▶ fst v)%ctx , snd v) ;
  ext_frame u (KPop Γ)  := ((fst u +▶ Γ)%ctx , snd u) .

Record pos_ogs : Type := POgs { p_ctx : k_ctx ; o_ctx : k_ctx }.
Definition p_swap (p : pos_ogs) := POgs p.(o_ctx) p.(p_ctx).

Definition half_ogs : half_game pos_ogs pos_ogs :=
  {| move := fun i   => any k_move i.(p_ctx) ;
     next := fun i m => {| p_ctx := ext_kctx i.(o_ctx) (any_elim k_next _ m) ;
                        o_ctx := i.(p_ctx) |} |} .

Definition g_ogs : game' pos_ogs pos_ogs :=
  {| client := half_ogs ; server := half_ogs |}.

(* ogs: ensemble des stratégies sur l'OGS (a.k.a. LTS de typage ?) *)
Definition ogs := itree g_ogs ∅ᵢ.

Record conf_p (p : pos_ogs) : Type := ConfP {
    (* extended continuation typing of *opponent* k_ctx *)
    C_moves_t : forall k, p.(p_ctx) ∋ k -> move_ext k ;
    (* compatibility of extended typing with *player* k_ctx *)
    C_moves_v : forall k i, move_ext_valid p.(o_ctx) k (C_moves_t k i) ;
    (* actual content: continuation data at extended typing *)
    C_moves : forall k i, k_val k (C_moves_t k i)
}.
Arguments ConfP {p}.
Arguments C_moves_t {p}.
Arguments C_moves_v {p}.
Arguments C_moves {p}.

Record conf_a (ks : k_ctx) : Type := ConfA {
    C_focus_t : frame ;
    C_focus_v : k_has_frame ks C_focus_t ;
    C_focus : eval_arg' C_focus_t ;
}.
Arguments ConfA {ks}.
Arguments C_focus_t {ks}.
Arguments C_focus_v {ks}.
Arguments C_focus {ks}.

Definition conf (p : pos_ogs) : Type := conf_a p.(p_ctx) * conf_p (p_swap p) .

Equations? conf_p_lift (p : pos_ogs) {ks}
  : conf_p p -> conf_p (POgs p.(p_ctx) (p.(o_ctx) +▶ ks)%ctx) :=
  conf_p_lift p c := ConfP _ _ _ .
+ refine (c.(C_moves_t) k X).
+ refine (move_ext_valid_lift k _ (c.(C_moves_v) k i)).
+ refine (c.(C_moves) k i).
Defined.

Equations? conf_p_cat (p : pos_ogs) {ks}
  : conf_p p -> conf_p (POgs ks p.(o_ctx)) -> conf_p (POgs (p.(p_ctx) +▶ ks)%ctx p.(o_ctx)) :=
  conf_p_cat _ c d := ConfP _ _ _ .
- destruct (concat_split _ _ X).
  + refine (c.(C_moves_t) k h).
  + refine (d.(C_moves_t) k h).
- destruct (concat_split _ _ i).
  + refine (c.(C_moves_v) k h).
  + refine (d.(C_moves_v) k h).
- destruct (concat_split _ _ i).
  + refine (c.(C_moves) k h).
  + refine (d.(C_moves) k h).
Defined.

Equations? k_move_apply {ks} (k : move_t) (m : k_move k)
          (e : move_ext k) (v : move_ext_valid ks k e)
          (val : k_val k e) : conf_a (ext_kctx ks (k_next k m)) :=
  k_move_apply (KCtx x) m (KECtx f) verif val :=
    ConfA ((fst f +▶ a_cext m)%ctx , snd f)
          (_ , r_concat_l _ _ _ (snd verif))
          (EArg (e_rename r_concat_l' val)
                (t_rename r_concat_r' (t_of_a m))
            : eval_arg' (_ , _)) ;
  k_move_apply (KVar x) m (KEVar Γ) verif val :=
    ConfA ((Γ +▶ t_obs_args m)%ctx , t_obs_goal m)
          (_ , top)
          (EArg EHole (t_obs_apply m val) : eval_arg' (_ , _)) .
- cbv [KVars] in X; r_fixup.
  destruct (concat_split _ _ X).
  + refine (r_concat_l _ _ _ (fst verif _ h)).
  + refine (r_concat_r _ _ _ h).
- cbv [KVars] in X; r_fixup.
  destruct (concat_split _ _ X).
  + refine (pop (r_concat_l _ _ _ (verif _ h))).
  + refine (pop (r_concat_r _ _ _ h)).
Defined.

Equations conf_p_select {p} (c : conf_p p) : iforest g_ogs (conf +ᵢ ∅ᵢ) p :=
  conf_p_select c (@Any _ _ _ k i m) :=
    Ret (inl (k_move_apply k m _ (c.(C_moves_v) k i) (c.(C_moves) k i) ,
              conf_p_lift p c) : conf (POgs _ _) + _) .



Definition inj_ogs_aux p (c : conf p) : itree g_ogs (conf +ᵢ ∅ᵢ) p.
  refine (emb_comp _ _ (eval_enf (fst c).(C_focus)) !>= _).
  intros [].
  - refine (Vis (Any _ _ (snd (fst c).(C_focus_v)) (a_of_val e) : qry g_ogs _) _).
    refine (conf_p_select (conf_p_cat _ (snd c) _)).
    unshelve econstructor.
    + intros k i. cbn in i.
      rewrite <- (has_map2 _ _ i).
      refine (KEVar (fst (C_focus_t (fst c)))).
    + intros k i. cbn in i. cbn.
      rewrite <- (has_map2 _ _ i); cbn.
      refine (fst (fst c).(C_focus_v)).
    + intros k i. cbn in *.
      rewrite <- (has_map2 _ _ i); cbn.
      refine (cext_get _ e (has_map1 _ _ i)).
  - pose (ni := neg_var h); dependent elimination ni.
    dependent elimination e0.
    refine (Vis (Any _ _ (fst (fst c).(C_focus_v) _ (map_has KVar _ (neg_upgrade h NArr)))
                         (a_of_val e0) : qry g_ogs _) _).
    refine (conf_p_select (conf_p_cat _ (snd c) _)).
    unshelve econstructor.
    + intros k i.
      dependent elimination i.
      * refine (KECtx (fst c).(C_focus_t)).
      * rewrite <- (has_map2 _ _ h0).
        refine (KEVar (fst (fst c).(C_focus_t))).
    + intros k i.
      dependent elimination i.
      * refine ((fst c).(C_focus_v)).
      * cbv [KVars] in h0; cbn in *. rewrite <- (has_map2 _ _ h0).
        refine (fst (fst c).(C_focus_v)).
    + intros k i.
      dependent elimination i.
      * refine e.
      * cbv [KVars] in h0; cbn in *. rewrite <- (has_map2 _ _ h0).
        refine (cext_get _ e0 (has_map1 _ _ h0)).
Defined.

Definition inj_ogs : forall p, conf p -> itree g_ogs ∅ᵢ p := iter inj_ogs_aux.

Section composition.

Variant _compo_arg (hideₚ hideₒ fullₚ fullₒ : k_ctx) : Type :=
| _c_ap  : ogs (POgs fullₚ fullₒ) -> iforest g_ogs ∅ᵢ (POgs hideₚ hideₒ)
         -> _compo_arg hideₚ hideₒ fullₚ fullₒ
| _c_pa : iforest g_ogs ∅ᵢ (POgs fullₒ fullₚ) -> ogs (POgs hideₒ hideₚ)
        -> _compo_arg hideₚ hideₒ fullₚ fullₒ
  .
Arguments _c_pa {hideₚ hideₒ fullₚ fullₒ} a b.
Arguments _c_ap {hideₚ hideₒ fullₚ fullₒ} a b.

Definition _compo : forall showₚ showₒ hideₚ hideₒ fullₚ fullₒ
                    , showₚ ⊎ hideₚ ≡ fullₚ
                    -> showₒ ⊎ hideₒ ≡ fullₒ
                    -> _compo_arg hideₚ hideₒ fullₚ fullₒ
                    -> ogs (POgs showₚ showₒ).
  cofix CIH.
  intros ? ? ? ? ? ? cₚ cₒ [a b|a b].
  - destruct (observe a).
    + destruct r.
    + exact (Tau (CIH _ _ _ _ _ _ cₚ cₒ (_c_ap t b))).
    + destruct e as [x i m].
      destruct (cover_split cₚ i) as [j|j].
      * refine (Vis (Any _ _ j m : qry g_ogs (POgs _ _)) (fun r => _)).
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
                      (_c_ap (a (Any _ _ (r_cover_r cₒ x i) m)) k))).
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


Variant _compo_arg_eq (hideₚ hideₒ fullₚ fullₒ : k_ctx) : Type :=
| _c_pa2 (a0 a1 : iforest g_ogs ∅ᵢ (POgs fullₒ fullₚ)) (b0 b1 : ogs (POgs hideₒ hideₚ))
  : (forall r, a0 r ≈ a1 r) -> b0 ≈ b1 -> _compo_arg_eq hideₚ hideₒ fullₚ fullₒ
| _c_ap2 (a0 a1 : ogs (POgs fullₚ fullₒ)) (b0 b1 : iforest g_ogs ∅ᵢ (POgs hideₚ hideₒ))
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

DEFS
norm : term -> triv-strategy (normal-form)
inj_ogs : term -> ogs-strategy

a ≈obs b := forall E, norm (E[a]) ≈ norm (E[b])
s_a ≈cio s_b := forall s_x, (s_x ∘ s_a) ≈ (s_x ∘ s_b) 

### CHEMIN 1 (peio, ≈obs est la plus grand rel compatible&adequate)

lem1 : norm a ≈ norm b -> inj_ogs a ≈ inj_ogs b

lem_joker: t diverges iff inj_ogs(t) diverges?
t ≈ spin <-> inj_ogs(t) ≈ spin
inf_ogs(t) ≈ norm(t);;?k

COEUR DE LA PREUVE:
lem2 : inj_ogs (E[t]) ≈ (inj_ogs_ctx E) ∘ (inj_ogs t)

  Preuve par coinduction.
  - inj_ogs (E[t]) calcule donc E[t] calcule donc t calcul et on case split

  Attaque: quid si
  t = E'[f v]
  inj_ogs(t) ≈ _compo (inj_ogs_ctx E', inj_ogs (f v))
  inj_ogs_ctx E ∘ inj_ogs t ≈
  inj_ogs_ctx E ∘ (inj_ogs_ctx E' ∘ inj_ogs (f v))
  ≈
  (inj_ogs_ctx E ∘ inj_ogs_ctx E') ∘ inj_ogs (f v)
  ≈ (?)
  (inj_ogs_ctx (E ∘ E')) ∘ inj_ogs (f v)

  Défense: E[E'[f v]] == E↺E'[f v]

### CHEMIN 2 (guilhem, rel CIO)











-----------
THM1 (soundness):
forall {Γ : neg_ctx} {τ} (a b : term Γ τ)
 (BIS : inj_ogs a ≈ inj_ogs b),
 a ≈obs b
Proof.



THM2 (full abstraction):
forall {Γ : neg_ctx} {τ} (a b : term Γ τ),
 a ≈obs b ->
 inj_ogs a ≈ inj_ogs b

***)
