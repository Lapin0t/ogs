From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.
From OGS.Ctx Require Import Abstract Family Assignment Renaming.

Section with_param.
  Context {T C : Type} {CC : context T C} {CL : context_laws T C}.

  Inductive c_expr : Type :=
  | CE_emb : C -> c_expr
  | CE_emp : c_expr
  | CE_cat : c_expr -> c_expr -> c_expr
  .
  Derive NoConfusion NoConfusionHom for c_expr.

  Declare Scope ctx_expr.
  Delimit Scope ctx_expr with ctx_e.
  Bind Scope ctx_expr with c_expr.
  Notation "`c Γ" := (CE_emb Γ%ctx) (at level 10) : ctx_expr.
  Notation "`∅" := (CE_emp) (at level 1) : ctx_expr.
  Notation "Γ1 `+▶ Γ2" := (CE_cat Γ1 Γ2) (at level 40) : ctx_expr.

  Inductive r_expr : c_expr -> c_expr -> Type :=
  | RE_emb {Γ1 Γ2} : Γ1 ⊆ Γ2 -> r_expr (`c Γ1) (`c Γ2)
  | RE_id {Γ} : r_expr Γ Γ
  | RE_seq {Γ1 Γ2 Γ3} : r_expr Γ1 Γ2 -> r_expr Γ2 Γ3 -> r_expr Γ1 Γ3
  | RE_emp {Γ} : r_expr `∅ Γ
  | RE_cat {Γ1 Γ2 Γ3} : r_expr Γ1 Γ3 -> r_expr Γ2 Γ3 -> r_expr (Γ1 `+▶ Γ2) Γ3 
  | RE_cat_l {Γ1 Γ2} : r_expr Γ1 (Γ1 `+▶ Γ2)
  | RE_cat_r {Γ1 Γ2} : r_expr Γ2 (Γ1 `+▶ Γ2)
  .

  Equations c_eval : c_expr -> C :=
    c_eval (`c Γ)     := Γ ; 
    c_eval (`∅)       := ∅%ctx ;
    c_eval (Γ1 `+▶ Γ2) := (c_eval Γ1 +▶ c_eval Γ2)%ctx .
  Notation "c⟦ Γ ⟧" := (c_eval Γ%ctx_e) : ctx_scope.

  Equations r_embed {Γ1 Γ2} : r_expr Γ1 Γ2 -> c⟦ Γ1 ⟧ ⊆ c⟦ Γ2 ⟧ :=
    r_embed (RE_emb r)   := r ;
    r_embed (RE_id)      := r_id ;
    r_embed (RE_seq r s) := r_embed r ᵣ⊛ r_embed s ;
    r_embed (RE_emp)     := ! ;
    r_embed (RE_cat r s) := [ r_embed r , r_embed s ] ;
    r_embed (RE_cat_l)   := r_cat_l ;
    r_embed (RE_cat_r)   := r_cat_r .
  Notation "r⟦ r ⟧" := (r_embed r).

  Inductive r_ne : c_expr -> c_expr -> Type :=
  | RNE_emb {Γ1 Γ2} : Γ1 ⊆ Γ2 -> r_ne (`c Γ1) (`c Γ2)
  | RNE_id {Γ} : r_ne (`c Γ) (`c Γ)
  | RNE_proj_l {Γ1 Γ2 Γ3} : r_ne Γ1 Γ2 -> r_ne Γ1 (Γ2 `+▶ Γ3)
  | RNE_proj_r {Γ1 Γ2 Γ3} : r_ne Γ1 Γ3 -> r_ne Γ1 (Γ2 `+▶ Γ3)
  .

  Inductive r_nf : c_expr -> c_expr -> Type :=
  | RNF_ne {Γ1 Γ2} : r_ne Γ1 Γ2 -> r_nf Γ1 Γ2
  | RNF_emp {Γ} : r_nf `∅ Γ
  | RNF_cat {Γ1 Γ2 Γ3} : r_nf Γ1 Γ3 -> r_nf Γ2 Γ3 -> r_nf (Γ1 `+▶ Γ2) Γ3
  .

  Equations r_ne_embed {Γ1 Γ2} : r_ne Γ1 Γ2 -> c⟦ Γ1 ⟧ ⊆ c⟦ Γ2 ⟧ :=
    r_ne_embed (RNE_emb r)    := r ;
    r_ne_embed (RNE_id)       := r_id ;
    r_ne_embed (RNE_proj_l r) := r_ne_embed r ᵣ⊛ r_cat_l ;
    r_ne_embed (RNE_proj_r r) := r_ne_embed r ᵣ⊛ r_cat_r .

  Equations r_nf_embed {Γ1 Γ2} : r_nf Γ1 Γ2 -> c⟦ Γ1 ⟧ ⊆ c⟦ Γ2 ⟧ :=
    r_nf_embed (RNF_ne r)    := r_ne_embed r ;
    r_nf_embed (RNF_emp)     := ! ;
    r_nf_embed (RNF_cat r s) := [ r_nf_embed r , r_nf_embed s ] .

  Equations r_sem : c_expr -> c_expr -> Type :=
    r_sem (`c Γ)      Δ := r_ne (`c Γ) Δ ;
    r_sem (`∅)        Δ := T1 ;
    r_sem (Γ1 `+▶ Γ2) Δ := r_sem Γ1 Δ × r_sem Γ2 Δ .

  Equations r_sem_embed Γ1 {Γ2} : r_sem Γ1 Γ2 -> c⟦ Γ1 ⟧ ⊆ c⟦ Γ2 ⟧ :=
    r_sem_embed (`c _)    s := r_ne_embed s ;
    r_sem_embed (`∅)      s := ! ;
    r_sem_embed (_ `+▶ _) s := [ r_sem_embed _ (fst s) , r_sem_embed _ (snd s) ] .

  Equations r_sem_proj_l Γ1 {Γ2 Γ3} : r_sem Γ1 Γ2 -> r_sem Γ1 (Γ2 `+▶ Γ3) :=
    r_sem_proj_l (`c _)    s := RNE_proj_l s ;
    r_sem_proj_l (`∅)      s := T1_0 ;
    r_sem_proj_l (_ `+▶ _) s := (r_sem_proj_l _ (fst s) , r_sem_proj_l _ (snd s)) .

  Equations r_sem_proj_r Γ1 {Γ2 Γ3} : r_sem Γ1 Γ2 -> r_sem Γ1 (Γ3 `+▶ Γ2) :=
    r_sem_proj_r (`c _)    s := RNE_proj_r s ;
    r_sem_proj_r (`∅)      s := T1_0 ;
    r_sem_proj_r (_ `+▶ _) s := (r_sem_proj_r _ (fst s) , r_sem_proj_r _ (snd s)) .

  Lemma r_sem_proj_l_eq {Γ1 Γ2 Γ3} (r : r_sem Γ1 Γ2)
    : r_sem_embed _ (@r_sem_proj_l _ _ Γ3 r) ≡ₐ r_sem_embed _ r ᵣ⊛ r_cat_l .
    funelim (r_sem_proj_l Γ1 r); cbn; eauto.
    - intros ? i; destruct (c_view_emp i).
    - intros ? i; cbn; destruct (c_view_cat i).
      + now apply H.
      + now apply H0.
  Qed.

  Lemma r_sem_proj_r_eq {Γ1 Γ2 Γ3} (r : r_sem Γ1 Γ2)
    : r_sem_embed _ (@r_sem_proj_r _ _ Γ3 r) ≡ₐ r_sem_embed _ r ᵣ⊛ r_cat_r .
    funelim (r_sem_proj_r Γ1 r); cbn; eauto.
    - intros ? i; destruct (c_view_emp i).
    - intros ? i; cbn; destruct (c_view_cat i).
      + now apply H.
      + now apply H0.
  Qed.

  Equations r_sem_id Γ : r_sem Γ Γ :=
    r_sem_id (`c Γ)      := RNE_id ;
    r_sem_id (`∅)        := T1_0 ;
    r_sem_id (Γ1 `+▶ Γ2) := (r_sem_proj_l _ (r_sem_id _) , r_sem_proj_r _ (r_sem_id _)) .

  Lemma r_sem_id_eq {Γ} : r_sem_embed Γ (r_sem_id Γ) ≡ₐ r_id .
    funelim (r_sem_id Γ); cbn; eauto.
    - intros ? i; destruct (c_view_emp i).
    - intros ? i; cbn; destruct (c_view_cat i); cbn.
      + rewrite r_sem_proj_l_eq; cbn; f_equal; now apply H.
      + rewrite r_sem_proj_r_eq; cbn; f_equal; now apply H0.
  Qed.

  Equations r_ne_ren_l {Γ1 Γ2 Γ3} : Γ1 ⊆ Γ2 -> r_ne (`c Γ2) Γ3 -> r_ne (`c Γ1) Γ3 :=
    r_ne_ren_l r (RNE_emb s) := RNE_emb (r ᵣ⊛ s) ;
    r_ne_ren_l r (RNE_id) := RNE_emb r ;
    r_ne_ren_l r (RNE_proj_l s) := RNE_proj_l (r_ne_ren_l r s) ;
    r_ne_ren_l r (RNE_proj_r s) := RNE_proj_r (r_ne_ren_l r s) .

  Lemma r_ne_ren_l_eq {Γ1 Γ2 Γ3} (r : Γ1 ⊆ Γ2) (s : r_ne (`c Γ2) Γ3)
    : r_ne_embed (r_ne_ren_l r s) ≡ₐ r ᵣ⊛ r_ne_embed s .
    funelim (r_ne_ren_l r s); cbn; eauto.
    - now refine (a_ren_l_eq _ _ _ r_cat_l r_cat_l _).
    - now refine (a_ren_l_eq _ _ _ r_cat_r r_cat_r _).
  Qed.

  Equations r_ne_seq {Γ1 Γ2 Γ3} : r_ne Γ1 Γ2 -> r_sem Γ2 Γ3 -> r_sem Γ1 Γ3 :=
    r_ne_seq (RNE_emb r)    s := r_ne_ren_l r s ;
    r_ne_seq (RNE_id)    s := s ;
    r_ne_seq (RNE_proj_l r) s := r_ne_seq r (fst s) ;
    r_ne_seq (RNE_proj_r r) s := r_ne_seq r (snd s) .

  Lemma r_ne_seq_eq {Γ1 Γ2 Γ3} (r : r_ne Γ1 Γ2) (s : r_sem Γ2 Γ3)
    : r_sem_embed _ (r_ne_seq r s) ≡ₐ r_ne_embed r ᵣ⊛ r_sem_embed _ s .
    funelim (r_ne_seq r s); cbn; eauto.
    - apply r_ne_ren_l_eq.
    - etransitivity; [ exact H | ].
      intros ? i; cbn; now rewrite c_view_cat_simpl_l.
    - etransitivity; [ exact H | ].
      intros ? i; cbn; now rewrite c_view_cat_simpl_r.
  Qed.

  Equations r_sem_seq Γ1 {Γ2 Γ3} : r_sem Γ1 Γ2 -> r_sem Γ2 Γ3 -> r_sem Γ1 Γ3 :=
    r_sem_seq (`c _)    r s := r_ne_seq r s ;
    r_sem_seq (`∅)      r s := T1_0 ;
    r_sem_seq (_ `+▶ _) r s := (r_sem_seq _ (fst r) s , r_sem_seq _ (snd r) s) .

  Lemma r_sem_seq_eq {Γ1 Γ2 Γ3} (r : r_sem Γ1 Γ2) (s : r_sem Γ2 Γ3)
    : r_sem_embed _ (r_sem_seq _ r s) ≡ₐ r_sem_embed _ r ᵣ⊛ r_sem_embed _ s .
    funelim (r_sem_seq Γ1 r s); cbn; eauto.
    - exact (r_ne_seq_eq r s).
    - intros ? i; destruct (c_view_emp i).
    - intros ? i; cbn; destruct (c_view_cat i).
      + apply H.
      + apply H0.
  Qed.

  Equations r_eval {Γ1 Γ2} : r_expr Γ1 Γ2 -> r_sem Γ1 Γ2 :=
    r_eval (RE_emb r)   := RNE_emb r ;
    r_eval (RE_id)      := r_sem_id _ ;
    r_eval (RE_seq r s) := r_sem_seq _ (r_eval r) (r_eval s) ;
    r_eval (RE_emp)     := T1_0 ;
    r_eval (RE_cat r s) := (r_eval r , r_eval s) ;
    r_eval (RE_cat_l)   := r_sem_proj_l _ (r_sem_id _) ;
    r_eval (RE_cat_r)   := r_sem_proj_r _ (r_sem_id _) .

  Lemma r_eval_eq {Γ1 Γ2} (r : r_expr Γ1 Γ2) : r_sem_embed _ (r_eval r) ≡ₐ r_embed r .
    funelim (r_eval r); cbn; eauto.
    - apply r_sem_id_eq.
    - etransitivity; [ apply r_sem_seq_eq | ].
      apply a_ren_l_eq; [ exact H | exact H0 ].
    - intros ? i; cbn; destruct (c_view_cat i).
      + apply H.
      + apply H0.
    - etransitivity; [ apply r_sem_proj_l_eq | ].
      refine (a_ren_l_eq _ r_id _ r_cat_l r_cat_l _); eauto.
      apply r_sem_id_eq.
    - etransitivity; [ apply r_sem_proj_r_eq | ].
      refine (a_ren_l_eq _ r_id _ r_cat_r r_cat_r _); eauto.
      apply r_sem_id_eq.
  Qed.

  Equations r_reify Γ1 {Γ2} : r_sem Γ1 Γ2 -> r_nf Γ1 Γ2 :=
    r_reify (`c _)    f := RNF_ne f ;
    r_reify (`∅)      f := RNF_emp ;
    r_reify (_ `+▶ _) f := RNF_cat (r_reify _ (fst f)) (r_reify _ (snd f)) .

  Lemma r_reify_eq {Γ1 Γ2} (s : r_sem Γ1 Γ2) : r_nf_embed (r_reify _ s) ≡ₐ r_sem_embed _ s .
    funelim (r_reify Γ1 s); cbn; eauto.
    - intros ? i; cbn; destruct (c_view_cat i).
      + apply H.
      + apply H0.
  Qed.

  Definition r_norm {Γ1 Γ2} : r_expr Γ1 Γ2 -> r_nf Γ1 Γ2 :=
    fun e => r_reify _ (r_eval e).

  Definition r_norm_ev {Γ1 Γ2} : r_expr Γ1 Γ2 -> c⟦ Γ1 ⟧ ⊆ c⟦ Γ2 ⟧ :=
    fun e => r_nf_embed (r_norm e).

  Lemma r_norm_eq {Γ1 Γ2} (r : r_expr Γ1 Γ2) : r_norm_ev r ≡ₐ r⟦ r ⟧ .
    etransitivity; [ apply r_reify_eq | apply r_eval_eq ].
  Qed.

  Lemma r_norm_sound {Γ1 Γ2} (r s : r_expr Γ1 Γ2)
    : r_norm_ev r ≡ₐ r_norm_ev s -> r⟦ r ⟧ ≡ₐ r⟦ s ⟧ .
    intro H.
    etransitivity; [ symmetry; apply r_norm_eq | ].
    etransitivity; [ apply H | apply r_norm_eq ].
  Qed.
End with_param.

Ltac quote_ctx t :=
 match eval hnf in t with
 | c_emp => constr:(CE_emp)
 | c_cat ?x ?y =>
     let x' := quote_ctx x in
     let y' := quote_ctx y in
     constr:(CE_cat x' y')
 | _ => constr:(CE_emb t)
 end.

Ltac quote_ren t :=
  lazymatch eval cbv beta iota zeta
          delta - [ a_empty a_cat a_ren_l r_id r_cat_l r_cat_r ]
        in t with
 | a_empty => constr:(RE_emp)
 | a_cat ?x ?y =>
     let x' := quote_ren x in
     let y' := quote_ren y in
     constr:(RE_cat x' y')
 | a_ren_l ?x ?y =>
     let x' := quote_ren x in
     let y' := quote_ren y in
     constr:(RE_seq x' y')
 | @r_id _ _ _ ?x =>
     let x' := quote_ctx x in
     constr:(RE_id (Γ := x'))
 | @r_cat_l _ _ _ _ ?x ?y =>
     let x' := quote_ctx x in
     let y' := quote_ctx y in
     constr:(RE_cat_l (Γ1 := x') (Γ2 := y'))
 | @r_cat_r _ _ _ _ ?x ?y =>
     let x' := quote_ctx x in
     let y' := quote_ctx y in
     constr:(RE_cat_r (Γ1 := x') (Γ2 := y'))
 | _ => constr:(RE_emb t)
 end.

Ltac exact_quote_ctx t := let t' := quote_ctx t in exact t'.
Ltac exact_quote_ren t := let t' := quote_ren t in exact t'.

Ltac ren_norm :=
  match goal with
  | [ |- ?r ≡ₐ ?s ] =>
      let r' := quote_ren r in
      let s' := quote_ren s in
      refine (r_norm_sound r' s' _)
  end.
Ltac ren_auto := ren_norm; reflexivity.

(* test *)
Goal forall T C (CC : context T C) (CL : context_laws T C) Γ1 Γ2 Γ3,
       @r_assoc_l _ _ _ _ Γ1 Γ2 Γ3 ᵣ⊛ @r_assoc_r _ _ _ _ Γ1 Γ2 Γ3 ≡ₐ r_id  .
  intros.
  unfold r_assoc_l, r_assoc_r, r_cat3_1, r_cat3_3.
  ren_auto.
Qed.
