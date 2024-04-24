From OGS Require Import Prelude.
From OGS.Utils Require Import Ctx Psh Rel.
From OGS.OGS Require Import Subst.

Open Scope ctx_scope.

#[global] Notation "'Fam₂' X" := (ctx X -> X -> X -> Type) (at level 30).

(* hole and composition of contexts *)
Class fill_monoid {T} (ectx : Fam₂ T) : Type := {
  e_hole {Γ τ} : ectx Γ τ τ ;
  e_fill {Γ τ1 τ2 τ3} : ectx Γ τ2 τ3 -> ectx Γ τ1 τ2 -> ectx Γ τ1 τ3 ;
}.

#[global] Notation "∙" := e_hole.
#[global] Notation "E @ₑ F" := (e_fill E F) (at level 20).

Class fill_monoid_laws {T} (ectx : Fam₂ T) {EM : fill_monoid ectx} : Prop := {
  e_hole_fill {Γ τ1 τ2} (e : ectx Γ τ1 τ2) : ∙ @ₑ e = e ;
  e_fill_hole {Γ τ1 τ2} (e : ectx Γ τ1 τ2) : e @ₑ ∙ = e ;
  e_fill_fill {Γ τ1 τ2 τ3 τ4} 
    (E1 : ectx Γ τ1 τ2) (E2 : ectx Γ τ2 τ3) (E3 : ectx Γ τ3 τ4) :
    E3 @ₑ (E2 @ₑ E1) = (E3 @ₑ E2) @ₑ E1 ;
}.

(* substitution of a Fam₂-shaped family by values *)
Class subst_module2 {T} (val : Famₛ T) (ectx : Fam₂ T) : Type := {
  e_sub {Γ Δ} : Γ =[val]> Δ -> forall τ1 τ2, ectx Γ τ1 τ2 -> ectx Δ τ1 τ2
}.
#[global] Notation "u ⊛ₑ E" := (e_sub u _ _ E) (at level 30).

Class subst_module2_laws {T} (val : Famₛ T) (ectx : Fam₂ T)
      {VM : subst_monoid val} {ESM : subst_module2 val ectx} := {
  e_sub_proper {Γ Δ} :: Proper (ass_eq Γ Δ ==> ∀ₕ _, ∀ₕ _, eq ==> eq) e_sub ;
  e_sub_id {Γ τ1 τ2} (e : ectx Γ τ1 τ2) : v_var ⊛ₑ e = e;
  e_sub_comp {τ1 τ2 Γ1 Γ2 Γ3} (u : Γ2 =[val]> Γ3) (v : Γ1 =[val]> Γ2) (e : ectx Γ1 τ1 τ2)
    : u ⊛ₑ (v ⊛ₑ e) = (u ⊛ v) ⊛ₑ e
}.

(* filling a context with a term *)
Class fill_module {T} (ectx : Fam₂ T) (term : Famₛ T) : Type := {
  t_fill {Γ τ1 τ2} : ectx Γ τ1 τ2 -> term Γ τ1 -> term Γ τ2
}.
#[global] Notation "E @ₜ t" := (t_fill E t) (at level 20).

Class fill_module_laws {T} (ectx : Fam₂ T) (term : Famₛ T)
      {EFM : fill_monoid ectx} {TFM : fill_module ectx term} := {
  t_fill_id {Γ τ1} (t : term Γ τ1) : ∙ @ₜ t = t ;
  t_fill_comp  {Γ τ1 τ2 τ3} (E1 : ectx Γ τ1 τ2) (E2 : ectx Γ τ2 τ3) (t : term Γ τ1)
    : E2 @ₜ (E1 @ₜ t) = (E2 @ₑ E1) @ₜ t ;
}.

(* substituting a Famₛ-shaped family *)
Class subst_module1 {T} (val : Famₛ T) (term : Famₛ T) : Type := {
  t_sub {Γ Δ} : Γ =[val]> Δ -> term Γ ⇒ᵢ term Δ ;
}.
#[global] Notation "u ⊛ₜ t" := (t_sub u _ t) (at level 30).

Class subst_module1_laws {T} (val : Famₛ T) (term : Famₛ T)
      {VM : subst_monoid val} {TSM : subst_module1 val term} : Prop := {
  t_sub_proper {Γ Δ} :: Proper (ass_eq Γ Δ ==> ∀ₕ _, eq ==> eq) t_sub ;
  t_var_sub {Γ τ} (t : term Γ τ) : v_var ⊛ₜ t = t ;
  t_sub_sub {Γ1 Γ2 Γ3 τ} (u : Γ2 =[val]> Γ3) (v : Γ1 =[val]> Γ2) (t : term Γ1 τ)
    : u ⊛ₜ (v ⊛ₜ t) = (u ⊛ v) ⊛ₜ t ;
} .

(* all the laws for a fill-monoid that can also be substituted *)
Class fill_monoid_subst_module2_coh {T} (val : Famₛ T) (ectx : Fam₂ T)
      {VM : subst_monoid val} {EFM : fill_monoid ectx} {ESM : subst_module2 val ectx} := {
  fsmon_fill_monoid_laws :: fill_monoid_laws ectx ;
  fsmon_subst_module2_laws :: subst_module2_laws val ectx ;
  e_sub_hole {Γ Δ τ} (u : Γ =[val]> Δ) : u ⊛ₑ ∙ = (∙ : ectx _ τ τ) ;
  e_sub_fill {Γ Δ τ1 τ2 τ3} (u : Γ =[val]> Δ) (E1 : ectx Γ τ1 τ2) (E2 : ectx  Γ τ2 τ3)
    : u ⊛ₑ (E2 @ₑ E1) = (u ⊛ₑ E2) @ₑ (u ⊛ₑ E1);
}.

(* all the laws for a fill-module that can also be substituted *)
Class fill_module_subst_module1_coh {T} (val : Famₛ T) (ectx : Fam₂ T) (term : Famₛ T)
      {VM : subst_monoid val} {EFM : fill_monoid ectx} {ESM : subst_module2 val ectx}
      {TVM : subst_module1 val term} {TFM : fill_module ectx term} := {
  fsmod_fill_module_laws :: fill_module_laws ectx term ;
  fsmod_subst_module1_laws :: subst_module1_laws val term ;
  t_sub_fill {Γ Δ τ1 τ2} (u : Γ =[val]> Δ) (E : ectx Γ τ1 τ2) (t : term  Γ τ1)
    : u ⊛ₜ (E @ₜ t) = (u ⊛ₑ E) @ₜ (u ⊛ₜ t) ;
}.

Section translation.
  Context {typ : Type} {val : Famₛ typ} {ectx : Fam₂ typ} {term : Famₛ typ}.
  Context {VM : subst_monoid val} {VML : subst_monoid_laws val}.
  Context {EFM : fill_monoid ectx} {ESM : subst_module2 val ectx}
          {EML : fill_monoid_subst_module2_coh val ectx}.
  Context {TFM : fill_module ectx term} {TSM : subst_module1 val term}
          {TML : fill_module_subst_module1_coh val ectx term}.

  Variant ityp := | VTy (t : typ) | CTy (t : typ).
  Derive NoConfusion for ityp.
  Notation "+ x" := (VTy x) (at level 5).
  Notation "¬ x" := (CTy x) (at level 5).

  (* petit renommage et notation pour la restriction de contexte *)
  Equations restrict : ctx ityp -> ctx typ :=
    restrict ∅ := ∅;
    restrict (Γ ▶ +τ) := (restrict Γ) ▶ τ;
    restrict (Γ ▶ ¬τ) := (restrict Γ).
  Notation "↓ Γ" := (restrict Γ) (at level 5).

  Variant ival : Famₛ ityp :=
  | IVal {Γ τ} (v : val ↓Γ τ) : ival Γ +τ
  | ICtx {Γ τ σ} (α : Γ ∋ ¬σ) (E : ectx ↓Γ τ σ) : ival Γ ¬τ.
  Derive NoConfusion for ival.

  (* des petits accesseurs pour ival *)
  Equations ival_v_get_val {Γ σ} (iv : ival Γ +σ) : val ↓Γ σ :=
    ival_v_get_val (IVal v) := v .

  Equations ival_e_get_ty {Γ σ} (iv : ival Γ ¬σ) : typ :=
    ival_e_get_ty (@ICtx Γ τ1 τ2 i E) := τ2 .

  Equations ival_e_get_var {Γ σ} (iv : ival Γ ¬σ) : Γ ∋ ¬(ival_e_get_ty iv) :=
    ival_e_get_var (@ICtx Γ τ1 τ2 i E) := i .

  Equations ival_e_get_ectx {Γ σ} (iv : ival Γ ¬σ) : ectx ↓Γ σ (ival_e_get_ty iv) :=
    ival_e_get_ectx (@ICtx Γ τ1 τ2 i E) := E .

  (* juste des petits noms plus cohérents avec le reste, aussi les champs c'est bien
     qu'ils aient des noms explicites vu que ça devient des accesseurs. *)
  Record iterm (Γ : ctx ityp) := ITerm {
    itm_ty : typ ;
    itm_var : Γ ∋ ¬itm_ty ;
    itm_tm : term ↓Γ itm_ty ;
  }.
  #[global] Arguments ITerm {Γ σ} i t : rename.
  #[global] Arguments itm_ty {Γ}.
  #[global] Arguments itm_var {Γ}.
  #[global] Arguments itm_tm {Γ}.

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
  | RestrictV (i : ↓Γ ∋ σ) : restrict_view (restrict_emb i)
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
  Equations restrict_get {Γ σ} (i : Γ ∋ +σ) : ↓Γ ∋ σ :=
    restrict_get i with view_restrict i := {
       | RestrictV j := j
    }.

  (* downgrade des assignations (j'ai renommé un changé l'implem pour
     utiliser les nouveaux outils) *)
  Definition restrict_ass {Γ Δ} (γ : Γ =[ival]> Δ) : ↓Γ =[val]> ↓Δ :=
    fun _ i => ival_v_get_val (γ _ (restrict_emb i)) .
  Notation "↓ₐ u" := (restrict_ass u) (at level 5).

  (* restreindre les assignations préserve l'égalité pointwise *)
  #[global] Instance restrict_ass_proper {Γ Δ}
            : Proper (ass_eq Γ Δ ==> ass_eq ↓Γ ↓Δ) restrict_ass .
  Proof.
    intros ?? H ? i.
    unfold restrict_ass; f_equal. 
    apply H.
  Qed.

  (* j'ai extrait les defs qui étaient en tactiques inline, pour utiliser equations *)
  Equations ival_var {Γ} σ : Γ ∋ σ -> ival Γ σ :=
    ival_var (+ σ) i := IVal (v_var _ (restrict_get i)) ;
    ival_var (¬ σ) i := ICtx i ∙ .

  Equations ival_sub {Γ Δ} (γ : Γ =[ival]> Δ) {σ} (v : ival Γ σ) : ival Δ σ :=
    ival_sub γ (IVal v)   := IVal (↓ₐ γ ⊛ᵥ v) ;
    ival_sub γ (ICtx i E) :=
      let i' := ival_e_get_var (γ _ i) in
      let E' := ival_e_get_ectx (γ _ i) in
      ICtx i' (E' @ₑ (↓ₐ γ ⊛ₑ E)) .

  Definition iterm_sub {Γ Δ} (γ : Γ =[ival]> Δ) (t : iterm Γ) : iterm Δ :=
    let i' := ival_e_get_var (γ _ t.(itm_var)) in
    let E' := ival_e_get_ectx (γ _ t.(itm_var)) in
    ITerm i' (E' @ₜ (↓ₐ γ ⊛ₜ t.(itm_tm))).

  #[global] Instance ival_monoid : subst_monoid ival :=
    {| v_var := @ival_var ; v_sub := @ival_sub |}.

  #[global] Instance iterm_module : subst_module ival iterm :=
    {| c_sub := @iterm_sub |}.

  (* je te fais les proper.. *)
  #[global] Instance ival_sub_proper {Γ Δ}
            : Proper (ass_eq Γ Δ ==> ∀ₕ _, eq ==> eq) ival_sub .
  Proof.
    intros ?? Hu ? v ? <-.
    dependent elimination v; cbn.
    - now rewrite Hu.
    - rewrite (Hu _ α); f_equal.
      now rewrite Hu.
  Qed.

  #[global] Instance iterm_sub_proper {Γ Δ}
            : Proper (ass_eq Γ Δ ==> eq ==> eq) iterm_sub .
  Proof.
    intros ?? Hu [ τ α t ] ? <-; unfold iterm_sub; cbn.
    rewrite (Hu _ α); f_equal.
    now rewrite Hu.
  Qed.

  (* .. et puis la première loi. L'idée c'est de faire des lemmes pour chacun des champs
     de `subst_monoid_laws ival` et `subst_module_laws ival iterm`. *)
  Lemma ival_sub_var {Γ1 Γ2} (p : Γ1 =[ival]> Γ2) : p ⊛ ival_var ≡ₐ p .
  Proof.
    intros a i.
    destruct a; cbn.
    - (* ici c'est tricky mais la manière dont j'ai fais les loi des subst_monoid fais
         que c'est un peu chiant de les appliquer, souvent il faut faire des `change`
         (remplace un terme par un autre qui est convertible). Là globalement on est
         en train de substituter une variable: `foo ⊛ᵥ v_var _ i`, sauf que la loi
         qu'on veut appliquer parle de `foo ⊛ v_var`. *)
      change (?u ⊛ᵥ v_var _ ?i) with ((u ⊛ v_var) _ i).
      rewrite v_sub_var.
      clear.
      (* là grosso modo fini la preuve, mais il reste à gérer les restrict..
         ici on veut montrer que inverser une variable de valeur puis aller
         chercher dans l'assignation restreinte, c'est la même chose qu'aller
         directement chercher dans l'assignation initiale. Grosso modo restrict_get
         c'est l'inversion de la variable, alors que la restriction d'assignation fait
         l'inverse (elle prend une variable simple et l'embed dans le contexte etendu
         pour recupérer la valeur). C'est maintenant que ça paye la view: on va unfold
         un peu pour faire apparaitre le moment où restrict_get pattern-match sur
         l'élément de la fibre donné par `view_restrict` et on va aussi pattern
         matcher dessus dans la preuve. Ce truc va pop souvent donc il faudrait
         l'extraire dans un lemme.
      *)
      unfold restrict_get.
      destruct (view_restrict i); cbn.
      (* et là c'est toujours pas fini, il y a le IVal qui embète: déjà on un unfold
         ce ↓ₐ pour y voir plus clair *)
      unfold restrict_ass.
      (* donc là c'est juste notre accesseur: on doit monter que
         `IVal (ival_v_get_val v) = v`. Encore une fois il faudrait l'extraire, ça va
         probablement réapparaitre. On commence par abstraire `v`, aka ici
         `p _ (restrict_emb i)` *)
      remember (p _ (restrict_emb i)) as v; clear.
      now dependent elimination v.
    - (* là on voit que la seule manière dont on utilise p et i c'est pour
         construire `p _ i`, donc dans le doute on abstrait *)
      remember (p _ i) as v; clear i Heqv.
      dependent elimination v; cbn.
      rewrite e_sub_hole. (* hop, une petite loi de cohérence qu'on avait oublié!! *)
      rewrite e_fill_hole.
      reflexivity.
  Qed.

  (* les lemmes qu'on a prouvé inline au-dessus, mais qui vont etre pratiques *)
  Lemma ival_v_get_id {Γ σ} (v : ival Γ +σ) : IVal (ival_v_get_val v) = v. 
  Admitted.

  (* bonus, j'imagine qu'on en aura besoin tout pareil *)
  Lemma ival_e_get_id {Γ σ} (v : ival Γ ¬σ)
        : ICtx (ival_e_get_var v) (ival_e_get_ectx v) = v. 
  Admitted.

  Lemma ass_restrict_get {Γ1 Γ2 σ} (u : Γ1 =[ival]> Γ2) (i : Γ1 ∋ +σ)
        : IVal (↓ₐ u _ (restrict_get i)) = u _ i .
  Admitted.
End translation.
