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

  Class subst_module_ctx_laxs `{subst_module_ectx} := {
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

Variant interactive_type (source_ty : Type) := | ValTy (t:source_ty) | CtxTy (t:source_ty).
Arguments ValTy {source_ty} t.
Arguments CtxTy {source_ty} t.

Notation "¬ x" := (CtxTy x) (at level 50).

Equations restrict_valTy {source_ty : Type} : ctx (interactive_type source_ty) -> ctx source_ty :=
restrict_valTy ∅ := ∅;
restrict_valTy (Γ ▶ (ValTy τ)) := (restrict_valTy Γ) ▶ τ;
restrict_valTy (Γ ▶ (CtxTy τ)) := (restrict_valTy Γ).

Definition interactive_baseT (source_ty : baseT) : baseT := {|typ := interactive_type typ|}.

Variant interactive_value {source_ty : baseT} (source_val : @baseV source_ty) (source_ectx : @baseEctx source_ty) : Famₛ (interactive_type typ) :=
  | IVal {Γ τ} (v : val (restrict_valTy Γ) τ) : interactive_value source_val source_ectx Γ (ValTy τ)
  | ICtx {Γ τ σ} (α:Γ ∋ ¬σ) (E : ectx (restrict_valTy Γ) τ σ) : interactive_value source_val source_ectx Γ (¬τ).

Program Definition interactive_baseV (source_ty : baseT) (source_val : @baseV source_ty) (source_ectx : @baseEctx source_ty) : @baseV (interactive_baseT source_ty) :=
{|val := interactive_value source_val source_ectx |}.

Record namedTerm {source_ty : baseT} (interactive_ty : interactive_type typ) (source_term : @baseTerm source_ty) (Γ : ctx (interactive_type typ) ) {σ : typ} := 
  {α:Γ ∋ ¬σ;  te : term (restrict_valTy Γ) σ}.
  
Class isubst_monoid {source_ty : baseT} (source_val : @baseV source_ty) (source_ectx : @baseEctx source_ty) : Type := {
  iv_var {Γ} : Γ =[interactive_value source_val source_ectx]> Γ ; (* Γ ∋ x -> val Γ x *)
  iv_sub {Γ Δ} : Γ =[interactive_value source_val source_ectx]> Δ -> interactive_value source_val source_ectx Γ ⇒ᵢ interactive_value source_val source_ectx Δ ;
}.

Notation "u ⊛ᵢ v" := (iv_sub u _ v) (at level 30).
Notation "Γ ⇒ᵢᵥ Δ" := (Γ =[interactive_value]> Δ) (at level 30). (*To be corrected *)

(* TODO 
Class subst_monoid_laws {source_ty : baseT} (source_val : @baseV source_ty) (source_ectx : @baseEctx source_ty) : Prop :=
{
  iv_sub_var {Γ1 Γ2} (p : Γ1 =[interactive_value source_val source_ectx]> Γ2) : p ⊛ᵢ iv_var ≡ₐ p ;
  iv_var_sub {Γ1 Γ2} (p : Γ1 ⇒ᵥ Γ2) : v_var ⊛ p ≡ₐ p ;
  iv_sub_sub {Γ1 Γ2 Γ3 Γ4} (p : Γ3 ⇒ᵥ Γ4) (q : Γ2 ⇒ᵥ Γ3) (r : Γ1 ⇒ᵥ Γ2) :
  p ⊛ (q ⊛ r) ≡ₐ (p ⊛ q) ⊛ r ;
} .

*)