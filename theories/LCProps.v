From Equations Require Import Equations.
From OGS Require Import Utils Ctx EventD CatD ITreeD EqD LCD.

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

Theorem lassen_eta {Γ : neg_ctx} {a b} (i : (Γ : ctx) ∋ (a → b)%ty)
  : Var i ≈L Lam (App (Var (pop i)) (Var top)).
Admitted.


