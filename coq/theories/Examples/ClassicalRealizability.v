From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel Ctx.
From OGS.Examples Require Import MuMuTildeClean.
Set Equations Transparent.

Record ortho : Type := {
  pole : forall Γ, conf Γ -> Type ;
  expand : forall Γ (c1 c2 : conf Γ), mu_red c1 c2 -> pole Γ c2 -> pole Γ c1
}.

Definition mk_ortho_simple (P : forall Γ, conf Γ -> Type) : ortho :=
  {| pole := fun Γ c => sigT (fun c' => mu_red_star c c' * P Γ c')%type ;
     expand := fun Γ c1 c2 r p => (_ ,' (RStep r (fst (projT2 p)), snd (projT2 p))) |} .

Definition is_ortho (O : ortho) {Γ a} (u : term Γ (t+ a)) (v : term Γ (t- a))
  := O.(pole) Γ (Cut u v) .

Definition SUB (a : ty) : Type := forall Γ, term Γ a -> Type .

Definition entails {a} (P Q : SUB a) : Type :=
  forall Γ (u : term Γ a), P Γ u -> Q Γ u .

Record biset (a : ty0) := { pos : SUB (t+ a) ; neg : SUB (t- a) } .
Arguments pos {a}.
Arguments neg {a}.

Definition def_ord {a} (P Q : biset a) : Type :=
  entails P.(pos) Q.(pos) * entails P.(neg) Q.(neg) .

Definition sub_ord {a} (P Q : biset a) : Type :=
  entails P.(pos) Q.(pos) * entails Q.(neg) P.(neg) .

Definition sub_eqv {a} (P Q : biset a) : Type :=
  def_ord P Q * def_ord Q P .

Section real.
  Context (O : ortho).

  Definition negP {a} (P : SUB (t+ a)) : SUB (t- a) :=
    fun Γ k => forall (u : term Γ (t+ a)), P Γ u -> is_ortho O u k .

  Definition negN {a} (P : SUB (t- a)) : SUB (t+ a) :=
    fun Γ u => forall (k : term Γ (t- a)), P Γ k -> is_ortho O u k .

  Definition negB {a} (P : biset a) : biset a :=
    {| pos := negN P.(neg) ; neg := negP P.(pos) |}.

  Definition ortho_cand {a} (P : biset a) := sub_eqv P (negB P).

  Definition def_contra {a} (P Q : biset a) (H : def_ord P Q) : def_ord (negB Q) (negB P)
    := ( fun Γ u q k p => q k (snd H Γ k p) ,
         fun Γ u q v p => q v (fst H Γ v p) ) .

  Definition sub_mono {a} (P Q : biset a) (H : sub_ord P Q) : sub_ord (negB P) (negB Q)
    := ( fun Γ u q k p => q k (snd H Γ k p) ,
         fun Γ u q v p => q v (fst H Γ v p) ) .

  Definition DNI {a} (P : biset a) : def_ord P (negB (negB P))
    := ( fun Γ u p k q => q u p ,
         fun Γ u p k q => q u p ).
 
  Definition TNE {a} (P : biset a) : def_ord (negB (negB (negB P))) (negB P)
    := def_contra _ _ (DNI P) .

  Definition ortho_sound {a} {P : biset a} (H : ortho_cand P)
    {Γ u k} : P.(pos) Γ u -> P.(neg) Γ k -> is_ortho O u k
    := fun p q => fst (fst H) Γ u p k q .

  Definition complP {a} (P : SUB (t+ a)) : biset a :=
    negB {| pos := P ; neg := negP P |} .

  Definition complN {a} (P : SUB (t- a)) : biset a :=
    negB {| pos := negN P ; neg := P |} .

  Definition compP_ortho {a} (P : SUB (t+ a)) : ortho_cand (complP P)
    := ((fun _ _ p => p , snd (DNI {| pos := P ; neg := negP P |})) ,
        (fun _ _ p => p , snd (TNE {| pos := P ; neg := negP P |}))) .

  Definition compN_ortho {a} (P : SUB (t- a)) : ortho_cand (complN P)
    := ((fst (DNI {| pos := negN P ; neg := P |}) , fun _ _ p => p) ,
        (fst (TNE {| pos := negN P ; neg := P |}) , fun _ _ p => p)) .

  Definition interp_ty0 (a : ty0) : biset a.
    induction a.
    - apply complN.
      intros Γ k; dependent elimination k.
      * exact T0.
      * exact T0.
      * exact T1.
    - apply complP.
      intros Γ u; dependent elimination u.
      * exact T0.
      * exact T0.
      * exact T1.
    - apply complN.
      intros Γ k; dependent elimination k.
      * exact T0.
      * exact T0.
      * exact (IHa1.(neg) _ t6).
      * exact (IHa2.(neg) _ t7).
    - apply complP.
      intros Γ u; dependent elimination u.
      * exact T0.
      * exact T0.
      * exact (IHa1.(pos) _ t).
      * exact (IHa2.(pos) _ t0).
    - apply complN.
      intros Γ k; dependent elimination k.
      * exact T0.
      * exact T0.
      * exact (IHa1.(pos) _ t4 * IHa2.(neg) _ t5)%type.
  Defined.

  Definition interp_ortho a : ortho_cand (interp_ty0 a).
    destruct a.
    - apply compN_ortho.
    - apply compP_ortho.
    - apply compN_ortho.
    - apply compP_ortho.
    - apply compN_ortho.
  Defined.

  Definition interp_ty {a} : forall Γ, term Γ a -> Type :=
    match a with
    | t+ a => (interp_ty0 a).(pos)
    | t- a => (interp_ty0 a).(neg)
    end .

  Definition realizer_a {Γ Δ} (ρ : Γ =[term]> Δ) : Type
    := forall a (i : Γ ∋ a), interp_ty Δ (ρ a i) .
  
  Definition realizer_t {Γ a} (u : term Γ a) : Type
    := forall Δ (ρ : Γ =[term]> Δ), realizer_a ρ -> interp_ty Δ (t_subst ρ _ u) .
  
  Definition realizer_c {Γ} (c : conf Γ) : Type
    := forall Δ (ρ : Γ =[term]> Δ), realizer_a ρ -> O.(pole) Δ (c_subst ρ c) .

  Scheme term_mutT := Induction for term Sort Type
    with conf_mutT := Induction for conf Sort Type.

  Definition t_adequacy_P Γ a (u : term Γ a) := realizer_t u .
  Definition c_adequacy_P Γ (s : conf Γ) := realizer_c s .

  Definition t_adequacy : forall Γ a (u : term Γ a), realizer_t u .
  eapply (term_mutT t_adequacy_P c_adequacy_P).
  all: unfold t_adequacy_P, c_adequacy_P.
  all: repeat intro; cbn.
  - exact (X _ h).
  - apply (fst (snd (interp_ortho a))).
    intros k p.
    apply (O.(expand) _ _ _ RMu).
    unfold c_subst1. rewrite c_sub_sub. 
    apply X.
    intros ? i; dependent elimination i.
    * exact p.
    * unfold a_comp, a_shift, t_shift; cbn. rewrite t_sub_ren.
      rewrite (t_sub_eq (@ass1 _ (t- _) k ⊛ᵣ s_pop) s_var (fun _ _ => eq_refl) _ _ _ eq_refl).
      rewrite t_sub_id_l.
      exact (X0 _ h).
  - apply (snd (snd (interp_ortho a))).
    intros v p.
    apply (O.(expand) _ _ _ RMu').
    unfold c_subst1. rewrite c_sub_sub. 
    apply X.
    intros ? i; dependent elimination i.
    + exact p.
    + unfold a_comp, a_shift, t_shift; cbn. rewrite t_sub_ren.
      erewrite (t_sub_eq (@ass1 _ (t+ _) v ⊛ᵣ s_pop) s_var (fun _ _ => eq_refl) _ _ _ eq_refl).
      rewrite t_sub_id_l.
      exact (X0 _ h).
  - exact (X0 OneI T1_0).
  - exact (X1 (Inl _) (X _ _ X0)).
  - exact (X1 (Inr _) (X _ _ X0)).
  - dependent elimination k; cbn in *; try inversion X1.
    apply (O.(expand) _ _ _ RApp).
    unfold t_subst1; rewrite t_sub_sub. 
    apply (fst (fst (interp_ortho _))).
    + apply X.
      intros ? i; dependent elimination i; cbn.
      * exact X2.
      * unfold t_shift. rewrite t_sub_ren.
      erewrite (t_sub_eq (@ass1 _ (t+ _) t5 ⊛ᵣ s_pop) s_var (fun _ _ => eq_refl) _ _ _ eq_refl).
      rewrite t_sub_id_l.
      exact (X0 _ h).
    + exact X3.
  - dependent elimination k; cbn in *; try inversion X2.
    + apply (O.(expand) _ _ _ RFst).
      apply (fst (fst (interp_ortho _))).
      * exact (X _ _ X1).
      * exact X2.
    + apply (O.(expand) _ _ _ RSnd).
      apply (fst (fst (interp_ortho _))).
      * exact (X0 _ _ X1).
      * exact X2.
  - exact (X0 ZerK T1_0).
  - exact (X2 (App _ _) (X _ _ X1 , X0 _ _ X1)).
  - exact (X1 (Fst _) (X _ _ X0)).
  - exact (X1 (Snd _) (X _ _ X0)).
  - dependent elimination u; cbn in *; try inversion X2.
    + apply (O.(expand) _ _ _ RInl).
      unfold c_subst1; rewrite c_sub_sub. 
      refine (X _ ((a_comp (ass1 t) (a_shift ρ))) _).
      intros ? i; dependent elimination i; cbn.
      * exact X2.
      * unfold t_shift. rewrite t_sub_ren.
      erewrite (t_sub_eq (@ass1 _ (t+ _) t ⊛ᵣ s_pop) s_var (fun _ _ => eq_refl) _ _ _ eq_refl).
      rewrite t_sub_id_l.
      exact (X1 _ h).
    + apply (O.(expand) _ _ _ RInr).
      unfold c_subst1; rewrite c_sub_sub. 
      refine (X0 _ ((a_comp (ass1 t0) (a_shift ρ))) _).
      intros ? i; dependent elimination i; cbn.
      * exact X2.
      * unfold t_shift. rewrite t_sub_ren.
      rewrite (t_sub_eq (@ass1 _ (t+ _) t0 ⊛ᵣ s_pop) s_var (fun _ _ => eq_refl) _ _ _ eq_refl); auto.
      rewrite t_sub_id_l.
      exact (X1 _ h).
  - apply (fst (fst (interp_ortho _))).
    + exact (X _ _ X1).
    + exact (X0 _ _ X1).
  Defined.

  Definition c_adequacy : forall Γ (c : conf Γ), realizer_c c.
    intros _ [Γ a u k] Δ ρ H.
    apply (fst (fst (interp_ortho _))).
    + exact (t_adequacy _ _ u  _ _ H).
    + exact (t_adequacy _ _ k  _ _ H).
  Defined.
  
    
End real.
