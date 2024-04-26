From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.
From OGS.Ctx Require Import Abstract Family Assignment.

Reserved Notation "Γ ⊆ Δ" (at level 30).
Reserved Notation "u ᵣ⊛ v" (at level 14).

Section with_param.
  Context {T C : Type} {CC : context T C} {CL : context_laws T C}.

(*|
Renaming
---------
Context inclusion is defined as an assignment of variables in Γ to variables in Δ.
|*)
  Notation "Γ ⊆ Δ" := (@assignment T C CC c_var Γ%ctx Δ%ctx).

(*|
The identity inclusion, whose renaming is the identity.
|*)
  Definition r_id {Γ} : Γ ⊆ Γ := fun _ i => i .
  #[global] Arguments r_id _ _ /.

(*|
Renaming assignments on the left by precomposition.
|*)
  Definition a_ren_l {F Γ1 Γ2 Γ3} : Γ1 ⊆ Γ2 -> Γ2 =[F]> Γ3 -> Γ1 =[F]> Γ3 := a_map.
  #[global] Arguments a_ren_l _ _ _ _ _ _ _ /.
  Notation "r ᵣ⊛ u" := (a_ren_l r u) : asgn_scope.

  #[global] Instance a_ren_l_eq {F Γ1 Γ2 Γ3}
    : Proper (asgn_eq _ _ ==> asgn_eq _ _ ==> asgn_eq _ _)
             (@a_ren_l F Γ1 Γ2 Γ3) .
  Proof. intros ?? H1 ?? H2 ??; cbn; now rewrite H1, H2. Qed.

  Lemma a_ren_l_id {F Γ1 Γ2} (a : Γ1 =[F]> Γ2) : r_id ᵣ⊛ a ≡ₐ a .
  Proof. reflexivity. Qed.

  Lemma a_ren_l_comp {F Γ1 Γ2 Γ3 Γ4} (u : Γ1 ⊆ Γ2) (v : Γ2 ⊆ Γ3) (w : Γ3 =[F]> Γ4) 
        : (u ᵣ⊛ v) ᵣ⊛ w ≡ₐ u ᵣ⊛ (v ᵣ⊛ w).
  Proof. reflexivity. Qed.

  Lemma view_cat_irr {Γ1 Γ2 x i} (a b : c_cat_view Γ1 Γ2 x i) : a = b .
  Proof.
    dependent elimination a; dependent induction b.
    - apply r_cat_l_inj in x1.
      now rewrite x1 in x |-; rewrite x.
    - symmetry in x1; destruct (r_cat_disj _ _ x1).
    - destruct (r_cat_disj _ _ x1).
    - apply r_cat_r_inj in x1.
      now rewrite x1 in x |-; rewrite x.
  Qed.

  Lemma c_view_cat_simpl_l {Γ1 Γ2 x} (i : Γ1 ∋ x)
        : c_view_cat (r_cat_l i) = (Vcat_l i : c_cat_view Γ1 Γ2 x _) .
  Proof. apply view_cat_irr. Qed.

  Lemma c_view_cat_simpl_r {Γ1 Γ2 x} (i : Γ2 ∋ x)
        : c_view_cat (r_cat_r i) = (Vcat_r i : c_cat_view Γ1 Γ2 x _) .
  Proof. apply view_cat_irr. Qed.

  Lemma a_cat_proj_l {F Γ1 Γ2 Δ} (u : Γ1 =[F]> Δ) (v : Γ2 =[F]> Δ)
       : r_cat_l ᵣ⊛ [ u , v ] ≡ₐ u .
  Proof. intros ? i; cbn; now rewrite c_view_cat_simpl_l. Qed.

  Lemma a_cat_proj_r {F Γ1 Γ2 Δ} (u : Γ1 =[F]> Δ) (v : Γ2 =[F]> Δ)
       : r_cat_r ᵣ⊛ [ u , v ] ≡ₐ v .
  Proof. intros ? i; cbv; now rewrite c_view_cat_simpl_r. Qed.

  Lemma a_cat_uniq {F Γ1 Γ2 Δ}
    (u : Γ1 =[F]> Δ) (v : Γ2 =[F]> Δ) (w : (Γ1 +▶ Γ2) =[F]> Δ)
    (H1 : u ≡ₐ r_cat_l ᵣ⊛ w)
    (H2 : v ≡ₐ r_cat_r ᵣ⊛ w)
    : [ u , v ] ≡ₐ w .
  Proof.
    intros ? i; cbv.
    destruct (c_view_cat i); [ exact (H1 _ i) | exact (H2 _ j) ].
  Qed.

  Lemma a_cat_id {Γ1 Γ2} : [ r_cat_l , r_cat_r ] ≡ₐ @r_id (Γ1 +▶ Γ2)%ctx  .
  Proof. now apply a_cat_uniq. Qed.

  Definition r_cat₂ {Γ1 Γ2 Δ1 Δ2} (r1 : Γ1 ⊆ Δ1) (r2 : Γ2 ⊆ Δ2) : (Γ1 +▶ Γ2) ⊆ (Δ1 +▶ Δ2)
    := [ r1 ᵣ⊛ r_cat_l , r2 ᵣ⊛ r_cat_r ] .
  #[global] Arguments r_cat₂ _ _ _ _ _ _ _ _ /.

  Definition r_shift {Γ Δ} R (r : Γ ⊆ Δ) : (Γ +▶ R) ⊆ (Δ +▶ R) := r_cat₂ r r_id . 
  #[global] Arguments r_shift _ _ _ _ _ _ /.

  Lemma r_shift_id {Γ R} : r_shift R (@r_id Γ) ≡ₐ r_id .
  Proof. now apply a_cat_uniq. Qed.

  Lemma r_shift_comp {Γ1 Γ2 Γ3 R} (r1 : Γ1 ⊆ Γ2) (r2 : Γ2 ⊆ Γ3)
        : r_shift R (r1 ᵣ⊛ r2) ≡ₐ r_shift R r1 ᵣ⊛ r_shift R r2 .
  Proof.
    intros ? i; cbv; destruct (c_view_cat i).
    - remember (r1 _ i) as j; now rewrite c_view_cat_simpl_l.
    - now rewrite c_view_cat_simpl_r.
  Qed.

  #[global] Instance r_shift_eq {Γ Δ R}
    : Proper (asgn_eq _ _ ==> asgn_eq _ _) (@r_shift Γ Δ R).
  Proof.
    intros ?? H ? i; cbv; destruct (c_view_cat i); eauto.
    now rewrite H.
  Qed.

  Definition r_cat3_1 {Γ1 Γ2 Γ3} : (Γ1 +▶ Γ2) ⊆ (Γ1 +▶ (Γ2 +▶ Γ3)) :=
    [ r_cat_l , r_cat_l ᵣ⊛ r_cat_r ].

  Definition r_cat3_2 {Γ1 Γ2 Γ3} : (Γ1 +▶ Γ3) ⊆ (Γ1 +▶ (Γ2 +▶ Γ3)) :=
    [ r_cat_l , r_cat_r ᵣ⊛ r_cat_r ].

  Definition r_cat3_3 {Γ1 Γ2 Γ3} : (Γ2 +▶ Γ3) ⊆ ((Γ1 +▶ Γ2) +▶ Γ3) :=
    [ r_cat_r ᵣ⊛ r_cat_l , r_cat_r ].

  Definition r_assoc_r {Γ1 Γ2 Γ3} : ((Γ1 +▶ Γ2) +▶ Γ3) ⊆ (Γ1 +▶ (Γ2 +▶ Γ3))
    := [ r_cat3_1 , r_cat_r ᵣ⊛ r_cat_r ].

  Definition r_assoc_l {Γ1 Γ2 Γ3} : (Γ1 +▶ (Γ2 +▶ Γ3)) ⊆ ((Γ1 +▶ Γ2) +▶ Γ3)
    := [ r_cat_l ᵣ⊛ r_cat_l , r_cat3_3 ] .

  Lemma r_assoc_rl {Γ1 Γ2 Γ3} : @r_assoc_l Γ1 Γ2 Γ3 ᵣ⊛ @r_assoc_r Γ1 Γ2 Γ3 ≡ₐ r_id .
  Proof.
    intros ? i; cbv; destruct (c_view_cat i).
    - now rewrite 2 c_view_cat_simpl_l.
    - destruct (c_view_cat j).
      + now rewrite c_view_cat_simpl_l, c_view_cat_simpl_r.
      + now rewrite c_view_cat_simpl_r.
  Qed.

  Lemma r_assoc_lr {Γ1 Γ2 Γ3} : @r_assoc_r Γ1 Γ2 Γ3 ᵣ⊛ @r_assoc_l Γ1 Γ2 Γ3 ≡ₐ r_id .
  Proof.
    intros ? i; cbv; destruct (c_view_cat i).
    - destruct (c_view_cat i).
      + now rewrite c_view_cat_simpl_l.
      + now rewrite c_view_cat_simpl_r, c_view_cat_simpl_l.
    - now rewrite 2 c_view_cat_simpl_r.
  Qed.
End with_param.

Ltac asgn_unfold :=
  repeat unfold a_empty, a_cat, a_map, r_id, a_ren_l, a_cat, r_cat₂, r_shift, r_cat3_1,
    r_cat3_2, r_cat3_3, r_assoc_r, r_assoc_l.

#[global] Notation "Γ ⊆ Δ" := (assignment c_var Γ%ctx Δ%ctx).
#[global] Notation "r ᵣ⊛ u" := (a_ren_l r u) : asgn_scope.
