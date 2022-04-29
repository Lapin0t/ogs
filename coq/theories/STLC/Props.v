Set Primitive Projections.
From Equations Require Import Equations.
From OGS Require Import Utils Ctx EventD CatD ITreeD EqD AngelicD LCD.

(*********************************************)
(* Notations for equivalence of lassen trees *)

Definition eqv_lassen {Γ : neg_ctx} {x} : term Γ x -> term Γ x -> Prop :=
  fun u v => eval_lassen u ≈ eval_lassen v.

Infix "≈L" := eqv_lassen (at level 40).

(****************************************)
(* various proofs on eager normal forms *)

Equations e_plug {Γ x y} : e_ctx Γ y x -> term Γ x -> term Γ y :=
  e_plug EHole         t := t ;
  e_plug (EApp_r E u)  t := e_plug E (App u t) ;
  e_plug (EApp_l E u)  t := e_plug E (App t u) ;
  e_plug (EPair_r E u) t := e_plug E (Pair u t) ;
  e_plug (EPair_l E u) t := e_plug E (Pair t u) ;
  e_plug (EPMatch E u) t := e_plug E (PMatch t u) ;
  e_plug (EInl E)      t := e_plug E (Inl t) ;
  e_plug (EInr E)      t := e_plug E (Inr t) ;
  e_plug (ESMatch E u v) t := e_plug E (SMatch t u v) .

Equations t_of_red {Γ x y} : term Γ x -> e_redex Γ x y -> term Γ y :=
  t_of_red e (RApp v) := App e (t_of_val v) ;
  t_of_red e (RPMatch u) := PMatch e u ;
  t_of_red e (RSMatch u v) := SMatch e u v .

Equations t_of_e_term {Γ x} : e_term Γ x -> term Γ x :=
  t_of_e_term (EVal v) := t_of_val v ;
  t_of_e_term (ERed E v r) := e_plug E (t_of_red (t_of_val v) r) .

Equations t_of_e_nf {Γ x} : e_nf Γ x -> term Γ x :=
  t_of_e_nf (NVal v) := t_of_val v ;
  t_of_e_nf (NRed E i r) := e_plug E (t_of_red (Var i) r).


(* WIP from here (other interesting stuff are at the end of the file)

Lemma e_split_correct {Γ x y} (E : e_ctx Γ x y) (t : term Γ y) : t_of_e_term (e_focus (EA E t)) = e_plug E t.
  funelim (e_focus (EA E t)); intros.

Lemma e_split_val {Γ x} (v : e_val Γ x) : e_focus' EHole (t_of_val v) = EVal v.
  induction v; auto.
  unfold e_focus' in *; simpl in *.
  rewrite focus_aux.focus_aux_equation_5.

  rewrite 
  destruct v; auto.
  unfold e_focus'. simpl. Search (focus_aux.focus_aux _ (inl (Pair _ _))).
  Search (focus_aux.focus_aux (EPair_l _ _) _).
  destruct (v1); auto.
  rewrite focus_aux.focus_aux_equation_13.
  
Qed.


Lemma e_split_correct {Γ x} (t : term Γ x) : t_of_e_term (e_split t) = t.
  funelim (e_split t); intros; cbn in *.
  + f_equal.
  + f_equal.
  + rewrite Heq in Hind. rewrite Heq, <-Hind. reflexivity.
  + rewrite Heq0; cbn; rewrite Heq.
    rewrite Heq in Hind; rewrite Heq0 in Hind0.
    rewrite <-Hind, <-Hind0. reflexivity.
  + rewrite Heq0; cbn; rewrite Heq.
    rewrite Heq in Hind; rewrite Heq0 in Hind0.
    rewrite <-Hind, <-Hind0. reflexivity.
Qed.

Lemma e_split_coherent {Γ x} (t : e_term Γ x) : e_split (t_of_e_term t) = t.
  funelim (t_of_e_term t).
  + destruct e; auto.
  + revert e1 e2; induction e0; intros; cbn.
    - destruct (e_split (t_of_val e2)) eqn:H; cbn;
        rewrite (e_split_val e2) in H;
        try discriminate H;
        injection H as ->.
      destruct (e_split (t_of_val e1)) eqn:H; cbn;
        rewrite (e_split_val e1) in H;
        try discriminate H;
        injection H as ->.
      reflexivity.
    - cbn in IHe0; rewrite (IHe0 e1 e2); reflexivity.
    - destruct (e_split (t_of_val e)) eqn:H; cbn;
        rewrite (e_split_val e) in H;
        try discriminate H;
        injection H as ->.
      cbn in IHe0; rewrite (IHe0 e1 e2); reflexivity.
Qed.

Lemma e_split_unique {Γ x} {a : term Γ x} {b} : a = t_of_e_term b <-> e_split a = b.
  econstructor; intro p.
  rewrite<- (e_split_coherent b); f_equal; exact p.
  rewrite<- (e_split_correct a); f_equal; exact p.
Qed.

Lemma e_split_inj {Γ a} {x y : term Γ a} (p : e_split x = e_split y) : x = y.
  rewrite<- e_split_correct, e_split_unique.
  exact p.
Qed.
*)

(**********************************)
(* various proofs on lassen trees *)

Equations eq_fin1 (x : Fin.fin 1) : x = Fin.F0 :=
  eq_fin1 (Fin.F0) := eq_refl.

Equations eq_neg {Γ : neg_ctx} {a b : ty} (i : (Γ : ctx) ∋ (a → b)%ty) : neg_var i = @NArr a b :=
  eq_neg i with neg_var i := { | NArr := eq_refl } .

From Paco Require Import paco.

Definition unfold_iter {I} {E : event I I} {X Y : I -> Type} (body : X ⇒ᵢ itree E (X +ᵢ Y))
           {i} (x : X i) 
           : observe (RecD.iter body i x) = observe (ITreeD.bind (body i x) (fun _ y => match y with
                             | inl x' => Tau (RecD.iter body _ x')
                             | inr y => Ret y
                             end)).
  reflexivity.
  Qed.

Definition unfold_iterₐ {I} {E : event I I} {X Y i} (body : X -> itreeₐ E i i (X + Y)) (x : X)
  : observe (iterₐ body x)
    = observe (body x !>= fun r => match r with
                             | inl x => tauₐ (iterₐ body x)
                             | inr y => retₐ y
              end).
  Proof. reflexivity. Qed.

(*
Definition subst_ret_obs {I} {E : event I I} {X Y} (f : X ⇒ᵢ itree E Y) {i} (x : X i)
        : observe (subst f (Ret x)) = observe (f i x) := eq_refl.

Definition subst_ret {I} {E : event I I} {X Y} (f : X ⇒ᵢ itree E Y) {i} (x : X i)
        : subst f (Ret x) = f i x := eq_refl.

  lazy delta beta.
  lazy iota.
  replace (Ret x) with ({| _observe := RetF x : itreeF E _ _ i |}).
Definition subst {I} {E : event I I} {X Y} (f : X ⇒ᵢ itree E Y)
                 : itree E X ⇒ᵢ itree E Y :=
*)

Theorem lassen_eta {Γ : neg_ctx} {a b} (i : (Γ : ctx) ∋ (a → b)%ty)
  : Var i ≈L Lam (App (Var (pop i)) (Var top)).

  (* 1. step *)
  apply paco3.paco3_fold.
  unfold eqit_; cbn.
  econstructor.
  intros [x v]; revert v.
  rewrite (eq_fin1 x). cbn. clear x. intro v.

  (* 2. step *)
  left. apply paco3.paco3_fold.
  cbn. econstructor. left.
  cbn [ r_shift has_case ]. cbn.
  pose (j := @r_concat_l' Γ (a_cext v) (a → b) i). fold j.
  unfold eval_lassen'.

  (* 3. step *)
  apply paco3.paco3_fold.
  rewrite 2 unfold_iter.
  destruct v.
  + 
    cbn [ t_of_a fst snd ].
    unfold eval_enf, bindₐ, sub, MonadItree.
    cbv [ bind RecD.emb_comp iterₐ ].
    unfold bindₐ.
    unfold sub.
    unfold MonadItree.
    cbn.
    rewrite 2 unfold_iterₐ.
    cbn [ eval_enf ].

  (* expand lots of stuff (too much) *)
  lazy beta delta [RecD.iter ].
  cbn [ fst snd
         MonadItree Basics.compose pin
         observe _observe
         bind subst sub
         ret AngelicD.retₐ tau AngelicD.tauₐ fiber_into
         RecD.iter RecD.emb_comp RecD.translate_fwd
         eval_enf
         AngelicD.bindₐ AngelicD.iterₐ AngelicD.ret₀
         e_focus
         ].

  (** Left branch **)
  (* compute through focus_aux *)
  rewrite focus_aux.focus_aux_equation_4,
          focus_aux.focus_aux_equation_1,
          focus_aux.focus_aux_equation_11,
          focus_aux.focus_aux_equation_1,
          focus_aux.focus_aux_equation_12.

  (* compute through eval_aux *)
  rewrite eval_aux_equation_2,
          lassen_enf_equation_2,
          (eq_neg j),  (* unstuck trivial proof *)
          lassen_enf_clause_2_equation_1.


  (** Right branch **)
  rewrite focus_aux.focus_aux_equation_4.
  rewrite focus_aux.focus_aux_equation_2.
  rewrite focus_aux.focus_aux_equation_11.
  rewrite focus_aux.focus_aux_equation_1.
  rewrite focus_aux.focus_aux_equation_12.
  rewrite eval_aux_equation_3.
  cbn.
  fold (@focus_aux.focus_aux Γ).
  econstructor; auto.
  econstructor.
  
  Locate "/ₛ".
  unfold t_subst1.
  unfold t_subst1_clause_1_f.
  simpl t_subst.
  Search eval_aux.
                         eval_aux
                           (ERed EHole (VLam (App (Var (pop j)) (Var top)))
                              (RApp (VVar top)))
  rewrite eval_aux_equation_1.
  rewrite lassen_enf_equation_2.

  
                           (focus_aux.focus_aux EHole
                              (inl
                                 (App (Lam (App (Var (pop j)) (Var top))) (Var top))))
  change (neg_var j) with (@NArr (a → b0) b).
  simpl lassen_enf.
  cbn.
  Search lassen_enf_clause_2
  Search "focus_aux".
  (focus_aux.focus_aux EHole (inl (App (Var j) (Var top))))
                                 Subterm.FixWf Fix Fix_F wellfounded
                                 Telescopes.wf_tele_measure Subterm.lt_wf Wf.measure_wf ].
  unfold eval_enf.




  RecD.emb_comp RecD.translate_fwd 
                         AngelicD.bindₐ AngelicD.iterₐ AngelicD.ret₀
                         AngelicD.tauₐ tau AngelicD.retₐ 
                         ret tau vis
                         eval_enf
                         fiber_into
                         MonadItree Basics.compose pin
                         e_focus focus_aux.focus_aux ].
  lazy iota beta delta [ observe _observe
                         bind subst sub
                         RecD.iter RecD.emb_comp RecD.translate_fwd 
                         AngelicD.bindₐ AngelicD.iterₐ AngelicD.ret₀
                         AngelicD.tauₐ tau AngelicD.retₐ 
                         ret tau vis
                         eval_enf
                         fiber_into
                         MonadItree Basics.compose pin
                         e_focus focus_aux.focus_aux ].
  cbn.
  unfold lassen_enf_clause_2.
  lazy iota beta.
  lazy iota beta delta [ r_concat_l' r_concat_l eq_rect_r ].
  unfold r_concat_l'.
  Search "lassen_enf_clause_2".
  lazy delta [ eval_enf ].
  Locate "=<<".
  Check sub.
  
  cbn.
  lazy iota beta delta [ eval_enf ].
  lazy iota beta delta [ observe ].
.  lazy iota beta delta -[ observe RecD.iter subst fiber_into RecD.emb_comp ].
  lazy iota beta zeta delta [ r_shift has_case apply_noConfusion noConfusion_retr noConfusion_inv noConfusion NoConfusion ].
  lazy iota beta zeta delta [ observe RecD.iter ].
  lazy iota beta delta [ observe RecD.iter ].
  unfold observe.
  cbn.
  destruct v.
  unfold t_of_a.
  unfold eval_enf.
  cbn.
  unfold r_shift.
  lazy iota beta delta [ has_case ].
  cbn.
  cbn.
  
  
  Locate (_ \/)
  apply paco3.upaco3_mon_bot.
  Search paco3.upaco3.
  unfold lassen_val, subst.
  cbn.
  repeat lazy cofix.
  lazy beta match cofix.
  simpl.
  lazy.
  lazy beta iota.
  
  Print go.
  Print
  replace (Ret (inl (EA EHole (apply_obs (VVar i) v)))) with ({| _observe := RetF (inl (EA EHole (apply_obs (VVar i) v))) |} : lassen (eval_arg' +ᵢ ∅ᵢ) _).
  compute.
  vm_compute.
  unfold lassen_val.
  unfold subst.
  unfold observe.


  unfold subst.
  cbn.
  cbn
  cbn in v.
  destruct v.
  cbn.
  destruct x.
  case x.
  unfold enf_k_rsp in v.

  destruct x.
  cbn in v.
  destruct (u_rsp enf_e (LVal (@AArr Γ a b) : u_qry enf_e (_ , _))).
  Check subst
  cbn in v.
  edestruct v as [n x].
  cbn.
  destruct n.
  cbn in x.
  cbn in k.
  destruct x.
  destruct x.
  unfold id.
  Search paco3.upaco3.
  cbn in v.

  From Coq Require Import Morphisms.
  Check eqitF.
  Check (Proper _ )
