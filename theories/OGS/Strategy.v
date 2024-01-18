From Coinduction Require Import coinduction tactics.

From OGS Require Import Prelude.
From OGS.Utils Require Import Ctx Rel.
From OGS.Game Require Import HalfGame Event.
From OGS.OGS Require Import Subst Obs Machine Game.
From OGS.ITree Require Import ITree Eq Delay Structure Properties Guarded.

Section withFam.

(*|
We consider a language abstractly captured as a machine
|*)
  Context {bT : baseT}.
  Context {bV : baseV}.
  Context {bC : baseC}.
  Context {sV : subst_monoid bV}.
  Context {sC : subst_module bV bC}.
  Context {oS : observation_structure}.
  Context {M: machine}.
(*|
Satisfying an appropriate axiomatization
|*)
  Context {sVL: subst_monoid_laws}.
  Context {sCL: subst_module_laws}.
  Context {VA : var_assumptions} .
  Context {ML: machine_laws}.

(*|
Env*
Env M Δ player es : environment part of the player (aka active at es) configuration at (Δ + es)
Env M Δ opponent es : environment part of the opponent (aka passive at es) configuration at (Δ + es)
|*)
  Inductive alt_env (Δ1 Δ2 : context) : bool -> alt_ext -> Type :=
  | ENil {b} : alt_env Δ1 Δ2 b ∅
  | EConT {Φ Γ} : alt_env Δ2 Δ1 Ⓞ Φ -> alt_env Δ1 Δ2 Ⓟ (Φ ▶ Γ)
  | EConF {Φ Γ} : alt_env Δ2 Δ1 Ⓟ Φ -> Γ ⇒ᵥ (Δ1 +▶ ↓⁺Φ) -> alt_env Δ1 Δ2 Ⓞ (Φ ▶ Γ)
  .
  Arguments ENil {Δ1 Δ2 b}.
  Arguments EConT {Δ1 Δ2 Φ Γ}.
  Arguments EConF {Δ1 Δ2 Φ Γ}.
  (* Derive Signature for alt_env. *)
  (* Derive NoConfusionHom for alt_env. *)

  Notation εₑ := (ENil) .
  Notation "u ▶ₑ⁺" := (EConT u) (at level 40).
  Notation "u ▶ₑ⁻ e" := (EConF u e) (at level 40).

  (* flattens an alternating environment into an unstructured one *)
  Equations concat0 {Δ1 Δ2 b Φ} (u : alt_env Δ1 Δ2 b Φ) : ↓[negb b]Φ ⇒ᵥ ((if b then Δ2 else Δ1) +▶ ↓[b]Φ) :=
    concat0 (εₑ)     := a_empty ;
    concat0 (u ▶ₑ⁺)   := r_concat3_1 ᵣ⊛ concat0 u ;
    concat0 (u ▶ₑ⁻ e) := [ concat0 u , e ] .

(*|
Flattens a pair of alternating environments for both player and opponent into a "closed" substitution.
|*)
  Equations concat1 {Δ} Φ {b} :
    alt_env Δ Δ b Φ -> alt_env Δ Δ (negb b) Φ -> ↓[b]Φ ⇒ᵥ Δ :=
    concat1 ∅       _       _         := a_empty ;
    concat1 (Φ ▶ _) (u ▶ₑ⁺)  (v ▶ₑ⁻ e) := [ concat1 Φ u v , [ v_var , concat1 Φ v u ] ⊛ e ] ;
    concat1 (Φ ▶ _) (u ▶ₑ⁻ e) (v ▶ₑ⁺)  := concat1 Φ u v .

  Arguments concat1 {Δ Φ b}.

(*|

|*)
  Lemma concat_fixpoint {Δ Φ} (u : alt_env Δ Δ Ⓟ Φ) (v : alt_env Δ Δ Ⓞ Φ)
    :  [ v_var , concat1 u v ] ⊛ concat0 u ≡ₐ concat1 v u
     /\ [ v_var , concat1 v u ] ⊛ concat0 v ≡ₐ concat1 u v .
    induction Φ; dependent destruction u; dependent destruction v; cbn; split.
    - cbn. intros ? i; dependent elimination i.
    - intros ? i; dependent elimination i.
    - simp concat1.
      rewrite <- e_comp_ren_l.
      rewrite <- (proj2 (IHΦ v u)).
      apply e_comp_proper; [ | reflexivity ].
      symmetry; apply s_eq_cover_uniq.
      * unfold r_concat3_1.
        now rewrite <- s_ren_comp, 2 s_eq_cat_l.
      * unfold r_concat3_1.
        now rewrite <- s_ren_comp, s_eq_cat_r, s_ren_comp, s_eq_cat_r, s_eq_cat_l.
    - simp concat1. symmetry; apply s_eq_cover_uniq.
      * rewrite <- e_comp_ren_r, s_eq_cat_l.
        symmetry; apply IHΦ.
      * now rewrite <- e_comp_ren_r, s_eq_cat_r.
  Qed.

  Definition m_strat_act Δ : psh alt_ext := fun Φ => (conf (Δ +▶ ↓⁺Φ) * alt_env Δ Δ Ⓟ Φ)%type.
  Definition m_strat_pas Δ : psh alt_ext := fun Φ => alt_env Δ Δ Ⓞ Φ.

  Definition m_strat_wrap {Δ Φ} (x : alt_env Δ Δ Ⓟ Φ)
     : nf' (Δ +▶ ↓⁺ Φ) -> (obs∙ Δ + h_actv ogs_hg (m_strat_pas Δ) Φ) :=
      fun u =>
        match cat_split (fst (projT2 u)) with
        | CLeftV h => inl (_ ,' (h , nf'_obs u))
        | CRightV h => inr ((_ ,' (h , nf'_obs u)) ,' (x ▶ₑ⁻ nf'_val u))
        end .

  Definition m_strat_play {Δ Φ} (x : m_strat_act Δ Φ)
    : delay (obs∙ Δ + h_actv ogs_hg (m_strat_pas Δ) Φ)
    := (fun _ => m_strat_wrap (snd x)) <$> eval (fst x).

  Definition m_strat_resp {Δ Φ} (x : m_strat_pas Δ Φ)
    : h_pasv ogs_hg (m_strat_act Δ) Φ
    := fun m => (app (r_concat3_1 ᵣ⊛ᵥ concat0 x _ (fst (projT2 m)))
                   (snd (projT2 m))
                   (v_var ⊛ᵣ r_concat_r ⊛ᵣ r_concat_r) ,
               x ▶ₑ⁺) .

  Definition m_strat {Δ} : m_strat_act Δ ⇒ᵢ ogs_act Δ :=
    cofix _m_strat Φ e :=
      emb_delay (m_strat_play e) >>=
        fun j (r : (_ @ Φ) j) =>
          go (match r in (fiber _ b) return (itree' ogs_e (fun _ : alt_ext => obs∙ Δ) b) with
              | Fib (inl m) => RetF (m : (fun _ : alt_ext => obs∙ Δ) Φ)
              | Fib (inr (x ,' p)) => VisF (x : ogs_e.(e_qry) Φ)
                                          (fun r => _m_strat (g_next r) (m_strat_resp p r))
              end).

  Lemma unfold_mstrat {Δ a} (x : m_strat_act Δ a) :
    m_strat a x
    ≊ (emb_delay (m_strat_play x) >>=
        fun j (r : (_ @ a) j) =>
          match r in (fiber _ b) return (itree ogs_e (fun _ : alt_ext => obs∙ Δ) b)
          with
          | Fib (inl m) => Ret' (m : (fun _ : alt_ext => obs∙ Δ) a)
          | Fib (inr (x ,' p)) => Vis' (x : ogs_e.(e_qry) _)
                                       (fun r => m_strat (g_next r) (m_strat_resp p r))
          end).
    revert a x; unfold it_eq; coinduction R CIH; intros a x.
    cbn -[m_strat_play].
    destruct (_observe (m_strat_play x)) as [ [ | [] ] | | [] ]; econstructor; auto.
    eapply (ft_t (it_eq_up2bind_t _ _)); econstructor; [ reflexivity | ].
    intros ? ? x2 ->; destruct x2 as [ [ | [] ] ]; auto.
  Qed.

  Definition m_stratp {Δ} : m_strat_pas Δ ⇒ᵢ ogs_pas Δ :=
    fun _ x m => m_strat _ (m_strat_resp x m).

  Definition m_strat_act_eqv {Δ} : relᵢ (m_strat_act Δ) (m_strat_act Δ) :=
    fun i x y => m_strat i x ≈ m_strat i y.
  Notation "x ≈ₐ y" := (m_strat_act_eqv _ x y) (at level 50).

  Definition m_strat_pas_eqv {Δ} : relᵢ (m_strat_pas Δ) (m_strat_pas Δ) :=
    fun i x y => forall m, m_strat_resp x m ≈ₐ m_strat_resp y m .
  Notation "x ≈ₚ y" := (m_strat_pas_eqv _ x y) (at level 50).

  Definition inj_init_act Δ {Γ} (c : conf Γ) : m_strat_act Δ (∅ ▶ Γ) :=
    ((r_concat_r ⊛ᵣ r_concat_r) ᵣ⊛ₜ c , εₑ ▶ₑ⁺).

  Definition inj_init_pas {Δ Γ} (γ : Γ ⇒ᵥ Δ) : m_strat_pas Δ (∅ ▶ Γ) :=
    εₑ ▶ₑ⁻ (r_concat_l ᵣ⊛ γ).

  Definition m_conf_eqv Δ : relᵢ conf conf :=
    fun Γ u v => inj_init_act Δ u ≈ₐ inj_init_act Δ v .
  Notation "x ≈⟦ogs Δ ⟧≈ y" := (m_conf_eqv Δ _ x y) (at level 50).

  Definition reduce_t (Δ : context) : Type :=
    ⦉ m_strat_act Δ ×ᵢ m_strat_pas Δ ⦊ᵢ .

  Equations compo_body {Δ} : reduce_t Δ -> delay (reduce_t Δ + obs∙ Δ) :=
    compo_body x :=
      m_strat_play (fst (projT2 x)) >>= fun _ r =>
          match r with
          | inl r => Ret' (inr r)
          | inr e => Ret' (inl (_ ,' (m_strat_resp (snd (projT2 x)) (projT1 e) , (projT2 e))))
          end.

  Definition compo {Δ a} (u : m_strat_act Δ a) (v : m_strat_pas Δ a) :
    delay (obs∙ Δ) :=
    iter_delay compo_body (a ,' (u , v)).
  Notation "u ∥ v" := (compo u v) (at level 40).

End withFam.

#[global] Notation εₑ := (ENil) .
Arguments ENil {_ _ Δ1 Δ2 b}.
Arguments EConT {_ _ Δ1 Δ2 Φ Γ}.
Arguments EConF {_ _ Δ1 Δ2 Φ Γ}.
#[global] Notation "u ▶ₑ⁺" := (EConT u) (at level 40).
#[global] Notation "u ▶ₑ⁻ e" := (EConF u e) (at level 40).
#[global] Notation "x ≈ₐ y" := (m_strat_act_eqv _ x y) (at level 50).
#[global] Notation "x ≈ₚ y" := (m_strat_pas_eqv _ x y) (at level 50).
#[global] Notation "u ∥ v" := (compo u v) (at level 40).
#[global] Notation "x ≈⟦ogs Δ ⟧≈ y" := (m_conf_eqv Δ _ x y) (at level 50).
