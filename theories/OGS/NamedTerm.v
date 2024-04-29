From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.
From OGS.Ctx Require Import All DirectSum Ctx.
From OGS.OGS Require Import Subst.

Open Scope ctx_scope.

(* hole and composition of contexts *)
Class fill_monoid `{CC : context T C} (ectx : Fam₂ T C) := {
  e_hole {Γ τ} : ectx Γ τ τ ;
  e_fill {Γ τ1 τ2 τ3} : ectx Γ τ2 τ3 -> ectx Γ τ1 τ2 -> ectx Γ τ1 τ3 ;
}.

#[global] Notation "∙" := e_hole.
#[global] Notation "E @ₑ F" := (e_fill E F) (at level 20).

Class fill_monoid_laws `{CC : context T C} (ectx : Fam₂ T C) {EM : fill_monoid ectx} := {
  e_hole_fill {Γ τ1 τ2} (e : ectx Γ τ1 τ2) : ∙ @ₑ e = e ;
  e_fill_hole {Γ τ1 τ2} (e : ectx Γ τ1 τ2) : e @ₑ ∙ = e ;
  e_fill_fill {Γ τ1 τ2 τ3 τ4}  (E1 : ectx Γ τ1 τ2) (E2 : ectx Γ τ2 τ3) (E3 : ectx Γ τ3 τ4)
    : E3 @ₑ (E2 @ₑ E1) = (E3 @ₑ E2) @ₑ E1 ;
}.

(* substitution of a Fam₂-shaped family by values *)
Class subst_module2 `{CC : context T C} (val : Fam₁ T C) (ectx : Fam₂ T C) := {
  e_sub : ectx ⇒₂ ⟦ val , ectx ⟧₂ ;
}.
#[global] Arguments e_sub {T C CC val ectx _} [Γ x y] E [Δ] a : rename. 
#[global] Notation "E ₑ⊛ a" := (e_sub E a%asgn) (at level 30).

Class subst_module2_laws `{CC : context T C} (val : Fam₁ T C) (ectx : Fam₂ T C)
      {VM : subst_monoid val} {ESM : subst_module2 val ectx} := {
  e_sub_proper :: Proper (∀ₕ Γ, ∀ₕ _, ∀ₕ _, eq ==> ∀ₕ Δ, asgn_eq Γ Δ ==> eq) e_sub ;
  e_sub_id {Γ τ1 τ2} (E : ectx Γ τ1 τ2) : E ₑ⊛ a_id = E;
  e_sub_comp {τ1 τ2 Γ1 Γ2 Γ3} (E : ectx Γ1 τ1 τ2) (u : Γ1 =[val]> Γ2) (v : Γ2 =[val]> Γ3)
    : E ₑ⊛ (u ⊛ v) = (E ₑ⊛ u) ₑ⊛ v ;
}.

(* filling a context with a term *)
Class fill_module `{CC : context T C} (ectx : Fam₂ T C) (term : Fam₁ T C) := {
  t_fill {Γ τ1 τ2} : ectx Γ τ1 τ2 -> term Γ τ1 -> term Γ τ2
}.
#[global] Notation "E @ₜ t" := (t_fill E t) (at level 20).

Class fill_module_laws `{CC : context T C} (ectx : Fam₂ T C) (term : Fam₁ T C)
      {EFM : fill_monoid ectx} {TFM : fill_module ectx term} := {
  t_fill_id {Γ τ1} (t : term Γ τ1) : ∙ @ₜ t = t ;
  t_fill_comp  {Γ τ1 τ2 τ3} (E1 : ectx Γ τ1 τ2) (E2 : ectx Γ τ2 τ3) (t : term Γ τ1)
    : E2 @ₜ (E1 @ₜ t) = (E2 @ₑ E1) @ₜ t ;
}.

(* substituting a Famₛ-shaped family *)
Class subst_module1 `{CC : context T C} (val term : Fam₁ T C) := {
  t_sub : term ⇒₁ ⟦ val , term ⟧₁ ;
}.
#[global] Arguments t_sub {T C CC val term _} [Γ x] t [Δ] a : rename. 
#[global] Notation "t ₜ⊛ a" := (t_sub t a%asgn) (at level 30).

Class subst_module1_laws `{CC : context T C} (val term : Fam₁ T C)
      {VM : subst_monoid val} {TSM : subst_module1 val term} := {
  t_sub_proper :: Proper (∀ₕ Γ, ∀ₕ _, eq ==> ∀ₕ Δ, asgn_eq Γ Δ ==> eq) t_sub ;
  t_sub_id {Γ τ} (t : term Γ τ) : t ₜ⊛ a_id = t ;
  t_sub_sub {Γ1 Γ2 Γ3 τ} (t : term Γ1 τ) (u : Γ1 =[val]> Γ2) (v : Γ2 =[val]> Γ3)
    : t ₜ⊛ (u ⊛ v) = (t ₜ⊛ u) ₜ⊛ v ;
} .

(* all the laws for a fill-monoid that can also be substituted *)
Class fill_monoid_subst_module2_coh `{CC : context T C} (val : Fam₁ T C) (ectx : Fam₂ T C)
      {VM : subst_monoid val} {EFM : fill_monoid ectx} {ESM : subst_module2 val ectx} := {
  fsmon_fill_monoid_laws :: fill_monoid_laws ectx ;
  fsmon_subst_module2_laws :: subst_module2_laws val ectx ;
  e_sub_hole {Γ Δ τ} (u : Γ =[val]> Δ) : ∙ ₑ⊛ u = (∙ : ectx _ τ τ) ;
  e_sub_fill {Γ Δ τ1 τ2 τ3} (E1 : ectx Γ τ1 τ2) (E2 : ectx Γ τ2 τ3) (u : Γ =[val]> Δ) 
    : (E2 @ₑ E1) ₑ⊛ u = (E2 ₑ⊛ u) @ₑ (E1 ₑ⊛ u);
}.

(* all the laws for a fill-module that can also be substituted *)
Class fill_module_subst_module1_coh `{CC : context T C}
      (val : Fam₁ T C) (ectx : Fam₂ T C) (term : Fam₁ T C)
      {VM : subst_monoid val} {EFM : fill_monoid ectx} {ESM : subst_module2 val ectx}
      {TVM : subst_module1 val term} {TFM : fill_module ectx term} := {
  fsmod_fill_module_laws :: fill_module_laws ectx term ;
  fsmod_subst_module1_laws :: subst_module1_laws val term ;
  t_sub_fill {Γ Δ τ1 τ2} (E : ectx Γ τ1 τ2) (t : term  Γ τ1) (u : Γ =[val]> Δ)
    : (E @ₜ t) ₜ⊛ u = (E ₑ⊛ u) @ₜ (t ₜ⊛ u) ;
}.

Section translation.
  Context `{CC : context T C} {val : Fam₁ T C} {ectx : Fam₂ T C} {term : Fam₁ T C}.
  Context {VM : subst_monoid val} {VML : subst_monoid_laws val}.
  Context {EFM : fill_monoid ectx} {ESM : subst_module2 val ectx}
          {EML : fill_monoid_subst_module2_coh val ectx}.
  Context {TFM : fill_module ectx term} {TSM : subst_module1 val term}
          {TML : fill_module_subst_module1_coh val ectx term}.

  Notation ictx := (dsum C C).
  Notation ityp := (T + T)%type.
  Notation "⌊ x ⌋" := (inl x) (at level 5).
  Notation "¬ x" := (inr x) (at level 5).

  Notation "ᵥ↓ Γ" := (fst Γ) (at level 5).
  Notation "ₖ↓ Γ" := (snd Γ) (at level 5).

  Record f_named (F : C -> T -> Type) (Γ : ictx) := Named {
    n_ty : T ;
    n_kvar : ₖ↓Γ ∋ n_ty ;
    n_elt : F ᵥ↓Γ n_ty ;
  }.
  #[global] Arguments Named {F Γ σ} i t : rename.
  #[global] Arguments n_ty {F Γ}.
  #[global] Arguments n_kvar {F Γ}.
  #[global] Arguments n_elt {F Γ}.
  Notation "⦅ i ⦆ x" := (Named i x) (at level 40).

  Equations ival : Fam₁ ityp ictx :=
    ival Γ ⌊τ⌋ := val ᵥ↓Γ τ ;
    ival Γ ¬τ  := f_named (fun Δ σ => ectx Δ τ σ) Γ .

  Equations ival_var {Γ} σ : Γ ∋ σ -> ival Γ σ :=
    ival_var ⌊σ⌋ i := v_var (i : ᵥ↓Γ ∋ _) ;
    ival_var ¬σ  i := ⦅i⦆ ∙ .

  Equations ival_sub {Γ Δ} (γ : Γ =[ival]> Δ) σ (v : ival Γ σ) : ival Δ σ :=
    ival_sub γ ⌊σ⌋ v       := (v : val _ _) ᵥ⊛ (γ ∘ inl) ;
    ival_sub γ ¬σ  (⦅i⦆ E) :=
      let (_ , j, E') := γ (¬ _) i in
      ⦅j⦆ (E' @ₑ (E ₑ⊛ (γ ∘ inl))) .

  Variant ival (Γ : ictx) : ityp -> Type :=
  | IVal {τ} (v : val ᵥ↓Γ τ) : ival Γ +τ
  | ICtx {τ σ} (α : ₖ↓Γ ∋ σ) (E : ectx ᵥ↓Γ τ σ) : ival Γ ¬τ.
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
