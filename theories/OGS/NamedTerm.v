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
Notation "•" := ectx_var.
Notation "E @ₑ F" := (ectx_sub E F) (at level 20).
Notation "u ⊛ₑ E" := (esub_val u E) (at level 30).
Notation "E @ₜ t" := (fill E t) (at level 20).
Notation "u ⊛ₜ t" := (t_sub u _ t) (at level 30).


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


(* ptet on pourrait renommer à ityp.. *)
Variant interactive_type := | ValTy (t:typ) | CtxTy (t:typ).
(*
le NoConfusion c'est un truc dont Equations a besoin pour faire
proprement du pattern matching dépendent. Globalement ça dérive une
relation qui ressemble à l'égalité mais qui est mieux plus
pratique. Tu peux checker:

Print NoConfusion_interactive_type.
Print NoConfusionPackage.
*)
Derive NoConfusion for interactive_type.

(* petite notation en plus pour ValTy *)
Notation "+ x" := (ValTy x) (at level 5).
Notation "¬ x" := (CtxTy x) (at level 5).

(* petit renommage et notation pour la restriction de contexte *)
Equations restrict : ctx interactive_type -> ctx typ :=
restrict ∅ := ∅;
restrict (Γ ▶ +τ) := (restrict Γ) ▶ τ;
restrict (Γ ▶ ¬τ) := (restrict Γ).
Notation "↓ Γ" := (restrict Γ) (at level 5).

Definition interactive_baseT : baseT := {|typ := interactive_type|}.

Variant ival : Famₛ interactive_type :=
| IVal {Γ τ} (v : val ↓Γ τ) : ival Γ +τ
| ICtx {Γ τ σ} (α : Γ ∋ ¬σ) (E : ectx ↓Γ τ σ) : ival Γ ¬τ.
Derive NoConfusion for ival.

Program Definition interactive_baseV  : @baseV interactive_baseT :=
  {| val := ival |}.

(* juste des petits noms plus cohérents avec le reste, aussi les champs c'est bien qu'ils
 aient des noms explicites vu que ça devient des accesseurs. *)
Record iterm (Γ : ctx interactive_type) := ITerm {
  itm_ty : typ ;
  itm_var : Γ ∋ ¬itm_ty ;
  itm_tm : term ↓Γ itm_ty ;
}.
#[global] Arguments ITerm {Γ σ} i t : rename.
#[global] Arguments itm_ty {Γ}.
#[global] Arguments itm_var {Γ}.
#[global] Arguments itm_tm {Γ}.

Program Definition interactive_baseC  : @baseC interactive_baseT :=
  {| conf := iterm |}.

(* on embed une variable du sous-context

note: la technique pour faire du équations c'est de commencer par utiliser
Equations? (avec le ?), qui va te mettre direct en proof mode. Et après de
raffiner les clauses successivement, genre:

Equations? restrict_emb Γ {σ} (i : ↓Γ ∋ σ) : Γ ∋ +σ :=
  restrict_emb Γ i := _ .

puis 

Equations? restrict_emb Γ {σ} (i : ↓Γ ∋ σ) : Γ ∋ +σ :=
  restrict_emb ∅       i := _ ;
  restrict_emb (Γ ▶ τ) i := _ .

Là on se rend compte que dans le cas 1, il n'y a aucun i possible, du coup soit
on écrit:

Equations? restrict_emb Γ {σ} (i : ↓Γ ∋ σ) : Γ ∋ +σ :=
  restrict_emb ∅       (!) ;
  restrict_emb (Γ ▶ τ) i   := _ .

Soit juste on enlève (normalement il trouve tout seul)

Equations? restrict_emb Γ {σ} (i : ↓Γ ∋ σ) : Γ ∋ +σ :=
  restrict_emb (Γ ▶ τ) i   := _ .

Puis

Equations? restrict_emb Γ {σ} (i : ↓Γ ∋ σ) : Γ ∋ +σ :=
  restrict_emb (Γ ▶ +τ) i   := _ ;
  restrict_emb (Γ ▶ ¬τ) i   := _ .

etc.
*)

Equations restrict_emb Γ {σ} (i : ↓Γ ∋ σ) : Γ ∋ +σ :=
  restrict_emb (Γ ▶ +τ) Ctx.top     := Ctx.top ;
  restrict_emb (Γ ▶ +τ) (Ctx.pop i) := Ctx.pop (restrict_emb Γ i) ;
  restrict_emb (Γ ▶ ¬τ) i           := Ctx.pop (restrict_emb Γ i) .
#[global] Arguments restrict_emb {Γ σ} i.

(* plus tard on aura besoin de savoir que c'est injectif *)
Lemma restrict_emb_inj {Γ σ} (i j : ↓Γ ∋ σ) : restrict_emb i = restrict_emb j -> i = j.
Admitted.

(* on défini les fibres de restrict_emb *)
Variant restrict_view {Γ σ} : Γ ∋ +σ -> Type :=
| RestrictV (i : restrict Γ ∋ σ) : restrict_view (restrict_emb i)
.

(* on montre que toute fibre est habitée *)
Lemma view_restrict {Γ σ} (i : Γ ∋ +σ) : restrict_view i .
  clear -i; induction Γ.
  - dependent elimination i.
  - dependent elimination i.
    + exact (@RestrictV (_ ▶ +_) σ Ctx.top).
    + specialize (IHΓ h).
      dependent elimination IHΓ.
      destruct y.
      exact (@RestrictV (_ ▶ +_) _ (Ctx.pop i)).
      exact (@RestrictV (_ ▶ ¬_) _ i).
Qed.

(* maintenant pour inverser il suffit de pattern-matcher sur un
élément de la fibre *)
Equations restrict_get {Γ σ} (i : Γ ∋ +σ) : restrict Γ ∋ σ :=
  restrict_get i with view_restrict i := {
     | RestrictV j := j
  }.

(* des petits accesseurs pour ival *)
Equations ival_v_get_val {Γ σ} (iv : ival Γ +σ) : val ↓Γ σ :=
  ival_v_get_val (IVal v) := v .

Equations ival_e_get_ty {Γ σ} (iv : ival Γ ¬σ) : typ :=
  ival_e_get_ty (@ICtx Γ τ1 τ2 i E) := τ2 .

Equations ival_e_get_var {Γ σ} (iv : ival Γ ¬σ) : Γ ∋ ¬(ival_e_get_ty iv) :=
  ival_e_get_var (@ICtx Γ τ1 τ2 i E) := i .

Equations ival_e_get_ectx {Γ σ} (iv : ival Γ ¬σ) : ectx ↓Γ σ (ival_e_get_ty iv) :=
  ival_e_get_ectx (@ICtx Γ τ1 τ2 i E) := E .

(* downgrade des assignations (j'ai renommé un changé l'implem pour
utiliser les nouveaux outils) *)
Definition restrict_ass {Γ Δ} (γ : Γ =[ival]> Δ) : ↓Γ =[val]> ↓Δ :=
  fun σ i => ival_v_get_val (γ +σ (restrict_emb i)) .

(* j'ai extrait les defs qui étaient en tactiques inline, pour utiliser equations *)
Equations ival_var {Γ} σ : Γ ∋ σ -> ival Γ σ :=
  ival_var (+ σ) i := IVal (v_var _ (restrict_get i)) ;
  ival_var (¬ σ) i := ICtx i ectx_var .
Arguments ival_var {Γ σ} i.

Equations ival_sub {Γ Δ} (γ : Γ =[ival]> Δ) {σ} (v : ival Γ σ) : ival Δ σ :=
  ival_sub γ (IVal v)   := IVal (restrict_ass γ ⊛ᵥ v) ;
  ival_sub γ (ICtx i E) :=
    let i' := ival_e_get_var (γ _ i) in
    let E' := ival_e_get_ectx (γ _ i) in
    ICtx i' (E' @ₑ (restrict_ass γ ⊛ₑ E)) .

Definition iterm_sub {Γ Δ} (γ : Γ =[ival]> Δ) (t : iterm Γ) : iterm Δ :=
  let i' := ival_e_get_var (γ _ t.(itm_var)) in
  let E' := ival_e_get_ectx (γ _ t.(itm_var)) in
  ITerm i' (E' @ₜ (restrict_ass γ ⊛ₜ t.(itm_tm))).

Program Definition ival_monoid : subst_monoid interactive_baseV :=
  {| v_var := @ival_var ; v_sub := @ival_sub |}.

Program Definition nterm_module : subst_module interactive_baseV interactive_baseC :=
  {| c_sub := @iterm_sub |}.

End translation.
