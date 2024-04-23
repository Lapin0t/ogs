From OGS Require Import Prelude.
From OGS.Utils Require Import Ctx Psh Rel.
From OGS.OGS Require Import Subst.

Open Scope ctx_scope.

#[global] Notation "'Fam_2' X" := (ctx X -> X -> X -> Type) (at level 30).


Class baseEctx `{baseT} : Type :=
  { ectx : Fam_2 typ }.  

Class baseTerm `{baseT} : Type :=
  { term : Famₛ typ }.

Section withFam.
  Context {bTy : baseT}.
  Context {bV : baseV}.
  Context {bEc : baseEctx}.
  Context {bTe : baseTerm}.
  Context {bVmon : subst_monoid bV}.

  Class subst_monoid_ectx : Type := {
      ectx_var {Γ τ} : ectx Γ τ τ  ; (* the hole context *)
      ectx_sub {Γ τ1 τ2 τ3} :  ectx Γ τ2 τ3 -> ectx Γ τ1 τ2 -> ectx Γ τ1 τ3;
    }.

  Notation "•" := ectx_var.
  Notation "E @ₑ F" := (ectx_sub E F) (at level 20).

  Class subst_monoid_ectx_laws `{subst_monoid_ectx} : Prop := 
    {
      ectx_var_sub {Γ τ1 τ2} (e : ectx Γ τ1 τ2): ectx_sub ectx_var e = e ;
      ectx_sub_var {Γ τ1 τ2} (e : ectx Γ τ1 τ2): ectx_sub e ectx_var = e ;
      ectx_sub_sub {Γ τ1 τ2 τ3 τ4} 
        (E1 : ectx Γ τ1 τ2) (E2 : ectx Γ τ2 τ3) (E3 : ectx Γ τ3 τ4) :
        E3 @ₑ (E2 @ₑ E1) = (E3 @ₑ E2) @ₑ E1 ;
    }.

  Class subst_module_ectx : Type := {
    esub_val {Γ Δ τ1 τ2} : Γ =[val]> Δ -> ectx Γ τ1 τ2 -> ectx Δ τ1 τ2
  }.

  Notation "u ⊛ₑ E" := (esub_val u E) (at level 30).

  Class subst_module_ctx_laws `{subst_module_ectx} := {
    (* esub_val_proper {Γ Δ} :: Proper (ass_eq Γ Δ ==> forall_relation (fun i => eq ==> eq)) esub_val ; *)
    esub_val_id {Γ τ1 τ2} (e : ectx Γ τ1 τ2) : esub_val v_var e = e;
    esub_val_comp {τ1 τ2 Γ1 Γ2 Γ3} (u : Γ2 ⇒ᵥ Γ3) (v : Γ1 ⇒ᵥ Γ2) (e : ectx Γ1 τ1 τ2) : 
      esub_val u (esub_val v e) = esub_val (u ⊛ v) e
  }.

  Class ectx_module_term  : Type := {
    fill {Γ τ1 τ2} : (ectx  Γ τ1 τ2) -> (term Γ τ1) -> (term Γ τ2)
  }.

  Notation "E @ₜ t" := (fill E t) (at level 20).
  
  Class ectx_module_term_laws `{ectx_module_term} `{subst_monoid_ectx} := {
    fill_id {Γ τ1} (t : term Γ τ1) : • @ₜ t = t;
    fill_comp  {Γ τ1  τ2  τ3} (E1 : ectx Γ τ1 τ2) (E2 : ectx Γ τ2 τ3) (t : term Γ τ1) :
      E2 @ₜ (E1 @ₜ t) = (E2 @ₑ E1) @ₜ t ;
  }.

  Class subst_module_term : Type := {
    t_sub {Γ Δ} : Γ ⇒ᵥ Δ -> term Γ ⇒ᵢ term Δ ;
  }.
  
  Notation "u ⊛ₜ t" := (t_sub u _ t) (at level 30).

  Class subst_module_term_laws {CM : subst_module_term} : Prop := {
   (*t_sub_proper {Γ Δ} :: Proper (ass_eq Γ Δ ==> eq ==> eq) c_sub ; *)
    t_var_sub {Γ τ} (t : term Γ τ) : v_var ⊛ₜ t = t ;
    t_sub_sub {Γ1 Γ2 Γ3 τ} (u : Γ2 ⇒ᵥ Γ3) (v : Γ1 ⇒ᵥ Γ2) (t : term Γ1 τ)
      : u ⊛ₜ (v ⊛ₜ t) = (u ⊛ v) ⊛ₜ t ;
  } .

  Class coherence_subst_fill_term `{ectx_module_term} `{subst_module_term} `{subst_module_ectx} : Prop := {
    tfill_sub {Γ Δ τ1 τ2} (u : Γ ⇒ᵥ Δ) (E : ectx  Γ τ1 τ2) (t : term  Γ τ1): 
      u ⊛ₜ (E @ₜ t) = (u ⊛ₑ E) @ₜ (u ⊛ₜ t);
  }.

  Class coherence_subst_fill_ectx `{subst_monoid_ectx} `{subst_module_ectx} : Prop := {
    efill_sub {Γ Δ τ1 τ2 τ3} (u : Γ ⇒ᵥ Δ) (E1 : ectx  Γ τ1 τ2) (E2 : ectx  Γ τ2 τ3): 
      u ⊛ₑ (E2 @ₑ E1) = (u ⊛ₑ E2) @ₑ (u ⊛ₑ E1);
  }.
End withFam.

Section translation.
  Variable source_ty : baseT.
  Variable source_val : @baseV source_ty.
  Variable source_ectx : @baseEctx source_ty.
  Variable source_term : @baseTerm source_ty.
  Variable val_monoid : subst_monoid source_val.
  Variable ectx_monoid : subst_monoid_ectx.
  Variable ectx_valmodule : subst_module_ectx.
  Variable term_ectxmodule : ectx_module_term.
  Variable term_valmodule : subst_module_term.


Variant interactive_type := | ValTy (t:typ) | CtxTy (t:typ).

Notation "¬ x" := (CtxTy x) (at level 50).

Equations restrict_valTy : ctx interactive_type -> ctx typ :=
restrict_valTy ∅ := ∅;
restrict_valTy (Γ ▶ (ValTy τ)) := (restrict_valTy Γ) ▶ τ;
restrict_valTy (Γ ▶ ¬τ) := (restrict_valTy Γ).

Definition interactive_baseT : baseT := {|typ := interactive_type|}.

Variant ival : Famₛ interactive_type :=
  | IVal {Γ τ} (v : val (restrict_valTy Γ) τ) : ival Γ (ValTy τ)
  | ICtx {Γ τ σ} (α:Γ ∋ ¬σ) (E : ectx (restrict_valTy Γ) τ σ) : ival Γ (¬τ).

Program Definition interactive_baseV  : @baseV interactive_baseT :=
{|val := ival |}.

Record namedTerm (Γ : ctx (interactive_type) ) := 
  {σ : typ; α:Γ ∋ ¬σ;  te : term (restrict_valTy Γ) σ}.

Arguments Build_namedTerm {_ _}.

Program Definition interactive_baseC  : @baseC interactive_baseT :=
{|conf := namedTerm |}.

Lemma restrict_invert {Γ σ} (i: Γ ∋ ValTy σ) : restrict_valTy Γ ∋ σ.
clear -i. dependent induction i.
cbn.
- apply Ctx.top.
- destruct y. cbn. 
  * eapply Ctx.pop. eapply IHi; eauto.
  * cbn. eapply IHi; eauto.
Qed. 

Lemma inject_to_restrict {Γ σ} (i : restrict_valTy Γ ∋ σ) : Γ ∋ ValTy σ.
clear -Γ σ i.
dependent induction i.
- induction Γ.
  * inversion x.
  * destruct x1.
    + cbn in x. inversion x. apply Ctx.top.
    + cbn in x. apply Ctx.pop. exact (IHΓ x).
- induction Γ.
 * inversion x.
 * destruct x1.
    + cbn in x. inversion x. exact (Ctx.pop (IHi Γ H0)).
    + cbn in x. apply Ctx.pop. exact (IHΓ x).
Qed.

Definition restrict_val_ival {Γ Δ} (γ : Γ =[ival]> Δ) : (restrict_valTy Γ) =[val]> (restrict_valTy Δ).
intros τ i. clear -i γ τ.
pose (γ (ValTy τ) (inject_to_restrict i)).
inversion i0.
apply v.
Qed.


Definition ival_monoid : subst_monoid interactive_baseV.
split.
- refine (fun Γ τ => match τ with ValTy σ => fun i => IVal (v_var _ (restrict_invert i)) 
| CtxTy σ => fun i => ICtx i ectx_var end).
- intros Γ Δ γ τ v. destruct τ; cbn; cbn in v.
  * apply IVal.
    refine (@v_sub source_ty source_val val_monoid (restrict_valTy Γ) (restrict_valTy Δ) _ _ _).
    + exact (restrict_val_ival γ).
    + inversion v; eauto.
  * inversion v. pose (γ (¬σ0) α0). inversion v0.  eapply (ICtx α1). eapply (ectx_sub E0).
    exact (esub_val (restrict_val_ival γ) E).
Defined.

Definition nterm_module : subst_module interactive_baseV interactive_baseC.
  split. intros Γ Δ γ M. destruct M. pose (γ (¬σ0) α0). inversion v.
  pose (restrict_val_ival γ) as δ.
  pose (fill E (t_sub δ _ te0)). 
  cbn.
  eexact {|α := α1; te := t|}.
Defined.
