From Coinduction Require Import coinduction tactics.

From OGS Require Import Prelude.
From OGS.Utils Require Import Ctx Rel.
From OGS.Game Require Import HalfGame Event.
From OGS.ITree Require Import ITree Eq Delay Structure Properties Guarded.

Open Scope ctx_scope.

(*|
Operational signature
=====================
Specifies the interactions player and opponent communicate over.
- typ : a set of types (meta [t])
- msg : maps a typ to messages (meta [m])
- dom : maps messages to the context extension they entails --- think the free variables of the message
|*)
Class interaction_spec : Type := {
  typ : Type ;
  msg : typ -> Type ;
  dom : forall t, msg t -> ctx typ ;
}.
Arguments dom {_} [_].

Section withInteractionSpec.
  Context {S : interaction_spec}.

(*|
Lifting messages and domain to contexts.
|*)
  Notation context := (ctx typ).
  Definition msg' (Γ : context) : Type := { t : typ & Γ ∋ t * msg t }%type.

  Definition msg_ty' {Γ} (m : msg' Γ) : typ := projT1 m .
  Definition msg_var' {Γ} (m : msg' Γ) : Γ ∋ msg_ty' m := fst (projT2 m) .
  Definition msg_msg' {Γ} (m : msg' Γ) : msg (msg_ty' m) := snd (projT2 m) .
  Definition dom' {Γ} (m : msg' Γ) : context := dom (msg_msg' m) .

(*|
Operational machine
=====================
Specifies the operational semantics of the language.
- [conf Γ]: the configurations (meta [c]), or active states, with open variables in Γ
- [v :::= val Γ τ]: the values (meta [v]), or elementary passive states, with open variables in Γ and of type τ
- [eval c]: the evaluation function for configurations, evaluating down to a message and an assignment. This evaluation is partial, partiality which we embed in the delay monad.
- [emb m]: embeds messages into configurations
- [v_var]: well-scoped embedding of variables into values
- [v_sub]: performs over values the substitution associated to an assignment
- [c_sub]: performs over configurations the substitution associated to an assignment
|*)
  Class lang_monoid : Type := {
    val : context -> typ -> Type ;
    v_var {Γ} : Γ =[val]> Γ ; (* Γ ∋ x -> val Γ x *)
    v_sub {Γ Δ} : Γ =[val]> Δ -> val Γ ⇒ᵢ val Δ ;
  } .

  Notation "u ⊛ᵥ v" := (v_sub u _ v) (at level 30).
  Notation "Γ ⇒ᵥ Δ" := (Γ =[val]> Δ) (at level 30).

  Class lang_module (V : lang_monoid) : Type := {
    conf : context -> Type ;
    c_sub {Γ Δ} : Γ ⇒ᵥ Δ -> conf Γ -> conf Δ ;
  } .
  Notation "u ⊛ₜ c" := (c_sub u c) (at level 30).

(*|
Derived notion: composition of value assignments.
|*)
  Definition e_comp {_ : lang_monoid} {Γ1 Γ2 Γ3} : Γ2 ⇒ᵥ Γ3 -> Γ1 ⇒ᵥ Γ2 -> Γ1 ⇒ᵥ Γ3
    := fun u v => s_map (v_sub u) v.
  Infix "⊛" := e_comp (at level 14).

  Class lang_monoid_laws (V : lang_monoid) : Prop := {
    v_sub_proper {Γ Δ} :: Proper (ass_eq Γ Δ ==> forall_relation (fun i => eq ==> eq)) v_sub ;
    v_sub_var {Γ1 Γ2} (p : Γ1 ⇒ᵥ Γ2) : p ⊛ v_var ≡ₐ p ;
    v_var_sub {Γ1 Γ2} (p : Γ1 ⇒ᵥ Γ2) : v_var ⊛ p ≡ₐ p ;
    v_sub_sub {Γ1 Γ2 Γ3 Γ4} (p : Γ3 ⇒ᵥ Γ4) (q : Γ2 ⇒ᵥ Γ3) (r : Γ1 ⇒ᵥ Γ2)
      : p ⊛ (q ⊛ r) ≡ₐ (p ⊛ q) ⊛ r ;
  } .

  Class lang_module_laws {V : lang_monoid} (C : lang_module V) : Prop := {
    c_sub_proper {Γ Δ} :: Proper (ass_eq Γ Δ ==> eq ==> eq) c_sub ;
    c_var_sub {Γ} (c : conf Γ) : v_var ⊛ₜ c = c ;
    c_sub_sub {Γ1 Γ2 Γ3} (u : Γ2 ⇒ᵥ Γ3) (v : Γ1 ⇒ᵥ Γ2) {c}
      : u ⊛ₜ (v ⊛ₜ c) = (u ⊛ v) ⊛ₜ c ;
  } .

  Context {V : lang_monoid} {VL : lang_monoid_laws V} .
  Context {C : lang_module V} {CL : lang_module_laws C} .

(*|
Derived notions: renamings.
|*)
  Definition v_ren {Γ Δ} : Γ ⊆ Δ -> val Γ ⇒ᵢ val Δ :=
    fun u => v_sub (v_var ⊛ᵣ u) .
  Notation "r ᵣ⊛ᵥ v" := (v_ren r _ v) (at level 14).

  Definition e_ren {Γ1 Γ2 Γ3} : Γ2 ⊆ Γ3 -> Γ1 ⇒ᵥ Γ2 -> Γ1 ⇒ᵥ Γ3
    := fun u v => (v_var ⊛ᵣ u) ⊛ v.
  Infix "ᵣ⊛" := e_ren (at level 14).

  Definition c_ren {Γ1 Γ2} : Γ1 ⊆ Γ2 -> conf Γ1 -> conf Γ2
    := fun u c => (v_var ⊛ᵣ u) ⊛ₜ c .
  Infix "ᵣ⊛ₜ" := c_ren (at level 14).

(*|
Additional assumptions on how variables behave.
|*)
  Definition is_var {Γ x} (v : val Γ x) : Type := { i : Γ ∋ x & v = v_var x i } .
  Definition is_var_get {Γ x} {v : val Γ x} (p : is_var v) : Γ ∋ x := projT1 p .
  Definition is_var_get_eq {Γ x} {v : val Γ x} (p : is_var v) : v = v_var x (is_var_get p) := projT2 p .

  Class var_assumptions : Type := {
    v_var_inj {Γ x} (i j : Γ ∋ x) : v_var x i = v_var x j -> i = j ;
    is_var_dec {Γ x} (v : val Γ x) : is_var v + (is_var v -> False) ;
    is_var_ren {Γ1 Γ2 x} (v : val Γ1 x) (e : Γ1 ⊆ Γ2) : is_var (e ᵣ⊛ᵥ v) -> is_var v ;
  }.
  Context {VA : var_assumptions} .

  Definition nf (Γ : context) (t : typ) : Type := { m : msg t & dom m ⇒ᵥ Γ } .
  Definition nf' (Γ : context) : Type := { t : typ & Γ ∋ t * nf Γ t }%type .

  Definition nf_ty' {Γ} : nf' Γ -> typ := @projT1 _ _ .
  Definition nf_var' {Γ} (u : nf' Γ) : Γ ∋ (nf_ty' u) := fst (projT2 u) .
  Definition nf_nf' {Γ} (u : nf' Γ) : nf Γ (nf_ty' u) := snd (projT2 u) .
  Definition nf_msg' {Γ} (u : nf' Γ) : msg (nf_ty' u) := projT1 (snd (projT2 u)) .
  Definition nf_val' {Γ} (u : nf' Γ) : dom (nf_msg' u) ⇒ᵥ Γ := projT2 (snd (projT2 u)) .

  Definition nf_eq {Γ t} : relation (nf Γ t) :=
    fun a b => exists H : projT1 a = projT1 b,
        rew H in projT2 a ≡ₐ projT2 b .

  Definition nf_eq' {Γ} : relation (nf' Γ) :=
    fun a b => exists H : nf_ty' a = nf_ty' b,
        (rew H in nf_var' a = nf_var' b) /\ (nf_eq (rew H in nf_nf' a) (nf_nf' b)) .

  Definition comp_eq {Γ} : relation (delay (nf' Γ)) :=
    it_eq (fun _ : T1 => nf_eq') (i := T1_0) .
  Notation "u ≋ v" := (comp_eq u v) (at level 40) .

  Definition msg_of_nf' : nf' ⇒ᵢ msg' :=
    fun Γ u => (nf_ty' u ,' (nf_var' u , nf_msg' u)) .

  Definition nf_of_msg' {Γ} (m : msg' Γ) : nf' (Γ +▶ dom' m) :=
    (msg_ty' m ,' (r_concat_l _ (msg_var' m) , (msg_msg' m ,' v_var ⊛ᵣ r_concat_r))) .

  Class machine : Type := {
    eval {Γ} : conf Γ -> delay (nf' Γ) ;
    app {Γ x} (v : val Γ x) (m : msg x) (r : dom m ⇒ᵥ Γ) : conf Γ ;
  } .
  Context {M : machine}.

  Definition app' {Γ Δ} (u : Γ ⇒ᵥ Δ) (v : nf' Γ) : conf Δ :=
    app (u _ (nf_var' v)) (nf_msg' v) (u ⊛ nf_val' v) .

  Definition eval_to_msg {Γ} (t : conf Γ) : delay (msg' Γ) :=
    fmap_delay (msg_of_nf' Γ) (eval t) . 

  Variant head_inst_nostep (u : { x : typ & msg x }) : { x : typ & msg x } -> Prop :=
  | HeadInst {Γ y} (v : val Γ y) (m : msg y) (e : dom m ⇒ᵥ Γ) (p : is_var v -> False) (i : Γ ∋ projT1 u)
             : eval_to_msg (app v m e) ≊ ret_delay (projT1 u ,' (i , projT2 u)) -> head_inst_nostep u (y ,' m) .


  Class machine_laws : Prop := {
    app_proper {Γ x v m} :: Proper (ass_eq (dom m) Γ ==> eq) (@app _ Γ x v m) ;
    app_sub {Γ1 Γ2 x} (e : Γ1 ⇒ᵥ Γ2) (v : val Γ1 x) (m : msg x) (r : dom m ⇒ᵥ Γ1)
      : e ⊛ₜ app v m r = app (e ⊛ᵥ v) m (e ⊛ r) ;

    eval_sub {Γ Δ} (c : conf Γ) (e : Γ ⇒ᵥ Δ)
      : eval (e ⊛ₜ c)
      ≋ bind_delay (eval c) (fun u => eval (app (e _ (nf_var' u)) (nf_msg' u) (e ⊛ nf_val' u))) ;

    (*eval_nf_ret {Γ} (u : nf' Γ) :
      eval_to_msg (app (v_var _ (nf_var' u)) (nf_msg' u) (nf_val' u))
      ≊ ret_delay (msg_of_nf' _ u) ;*)

    eval_nf_ret {Γ} (u : nf' Γ) :
      eval (app (v_var _ (nf_var' u)) (nf_msg' u) (nf_val' u))
      ≋ ret_delay u ;

    eval_app_not_var : well_founded head_inst_nostep ;
  } .      

  Context {ML : machine_laws} .

  Lemma is_var_irr {Γ x} {v : val Γ x} (p q : is_var v) : p = q .
    destruct p as [i1 e1], q as [i2 e2].
    destruct (v_var_inj _ _ (eq_trans (eq_sym e1) e2)).
    f_equal; apply YesUIP.
  Qed.

  Definition ren_is_var {Γ1 Γ2 x} (v : val Γ1 x) (e : Γ1 ⊆ Γ2) : is_var v -> is_var (e ᵣ⊛ᵥ v) .
    intro p.
    refine (e _ (is_var_get p) ,' _).
    pose (i := is_var_get p); eassert (H : _) by exact (is_var_get_eq p); fold i in H |- *.
    rewrite H; change (e ᵣ⊛ᵥ v_var x i) with ((e ᵣ⊛ v_var) x i).
    unfold e_ren; rewrite v_sub_var; reflexivity.
  Defined.

  Lemma ren_is_var_get {Γ1 Γ2 x} (v : val Γ1 x) (e : Γ1 ⊆ Γ2) (p : is_var v) :
    is_var_get (ren_is_var v e p) = e _ (is_var_get p) .
    reflexivity.
  Qed.    

  Variant is_var_ren_view {Γ1 Γ2 x} (v : val Γ1 x) (e : Γ1 ⊆ Γ2) : is_var (e ᵣ⊛ᵥ v) -> Type :=
  | IsVarRen (p : is_var v) : is_var_ren_view v e (ren_is_var v e p)
  .
  Arguments IsVarRen {Γ1 Γ2 x v e}.

  Lemma view_is_var_ren {Γ1 Γ2 x} (v : val Γ1 x) (e : Γ1 ⊆ Γ2) (p : is_var (e ᵣ⊛ᵥ v)) : is_var_ren_view v e p .
    rewrite (is_var_irr p (ren_is_var v e (is_var_ren v e p))); econstructor.
  Qed.

(*|
A couple derived properties on the constructed operations.
|*)

  #[global]
  Instance e_comp_proper {Γ1 Γ2 Γ3} : Proper (ass_eq Γ2 Γ3 ==> ass_eq Γ1 Γ2 ==> ass_eq Γ1 Γ3) e_comp.
    intros ? ? H1 ? ? H2 ? i; unfold e_comp, s_map.
    now rewrite H1, H2.
  Qed.

  #[global]
  Instance e_ren_proper {Γ1 Γ2 Γ3} : Proper (ass_eq Γ2 Γ3 ==> ass_eq Γ1 Γ2 ==> ass_eq Γ1 Γ3) e_ren.
    intros ? ? H1 ? ? H2; unfold e_ren.
    apply e_comp_proper; eauto; now rewrite H1.
  Qed.

  Lemma e_comp_ren_r {Γ1 Γ2 Γ3 Γ4} (u : Γ3 ⇒ᵥ Γ4) (v : Γ2 ⇒ᵥ Γ3) (w : Γ1 ⊆ Γ2)
        : u ⊛ (v ⊛ᵣ w) ≡ₐ (u ⊛ v) ⊛ᵣ w .
    reflexivity.
  Qed.

  Lemma e_comp_ren_l {Γ1 Γ2 Γ3 Γ4} (u : Γ3 ⇒ᵥ Γ4) (v : Γ2 ⊆ Γ3) (w : Γ1 ⇒ᵥ Γ2)
        : (u ⊛ᵣ v) ⊛ w ≡ₐ u ⊛ (v ᵣ⊛ w) .
    unfold e_ren; now rewrite v_sub_sub, e_comp_ren_r, v_sub_var.
  Qed.

  Lemma v_sub_comp {Γ1 Γ2 Γ3} (u : Γ2 ⇒ᵥ Γ3) (v : Γ1 ⇒ᵥ Γ2) {x} (w : val Γ1 x) : u ⊛ᵥ (v ⊛ᵥ w) = (u ⊛ v) ⊛ᵥ w .
    pose (w' := s_append s_empty w : (∅ ▶ x) ⇒ᵥ Γ1).
    change w with (w' _ Ctx.top).
    do 2 change (?u ⊛ᵥ ?v _ Ctx.top) with ((u ⊛ v) _ Ctx.top).
    apply v_sub_sub.
  Qed.

  Lemma v_sub_id {Γ1 Γ2} (u : Γ1 ⇒ᵥ Γ2) {x} (i : Γ1 ∋ x) : u ⊛ᵥ (v_var x i) = u x i .
    apply v_sub_var.
  Qed.

(*|
Evaluate a configuration inside an environment (assignment), returning only the message part (the "positive" or "static" part).
|*)
  Definition eval_in_env {Γ Δ} (e : Γ ⇒ᵥ Δ) (t : conf Γ) : delay (msg' Δ) :=
    eval_to_msg (e ⊛ₜ t) .

  #[global] Instance eval_in_env_proper {Γ Δ} : Proper (ass_eq Γ Δ ==> eq ==> eq) (@eval_in_env Γ Δ).
    intros ? ? H1 ? ? H2; unfold eval_in_env; now rewrite H1, H2.
  Qed.

  Definition ciu {Γ} Δ (x y : conf Γ) : Prop
    := forall e : Γ ⇒ᵥ Δ, eval_in_env e x ≈ eval_in_env e y.

(*|
Section 3: game definition
↓+ ~ join_even
|*)
  Definition alt_ext : Type := ctx (context).
  Notation "↓⁺ a" := (join_even a) (at level 9).
  Notation "↓⁻ a" := (join_odd a) (at level 9).
  Notation "↓[ b ] a" := (join_even_odd_aux b a) (at level 9).

  Definition ogs_hg : half_game alt_ext alt_ext :=
    {| g_move := fun es => msg' ↓⁺es ;
       g_next := fun es m => (es ▶ dom' m) |} .

  Definition ogs_g : game alt_ext alt_ext :=
    {| g_client := ogs_hg ;
       g_server := ogs_hg  |} .

  Definition ogs_e : event alt_ext alt_ext := e_of_g ogs_g.

  Definition ogs_act (Δ : context) : psh alt_ext := itree ogs_e (fun _ => msg' Δ).
  Definition ogs_pas (Δ : context) : psh alt_ext := h_pasv ogs_hg (ogs_act Δ).

  Notation "Ⓟ" := true.
  Notation "Ⓞ" := false.

(*|
Env* (def 3.12)
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

  Notation εₑ := (ENil) .
  Notation "u ▶ₑ⁺" := (EConT u) (at level 40).
  Notation "u ▶ₑ⁻ e" := (EConF u e) (at level 40).

  (* flattens an alternating environment into an unstructured one *)
  Equations concat0 {Δ1 Δ2 b Φ} (u : alt_env Δ1 Δ2 b Φ) : ↓[negb b]Φ ⇒ᵥ ((if b then Δ2 else Δ1) +▶ ↓[b]Φ) :=
    concat0 (εₑ)     := s_empty ;
    concat0 (u ▶ₑ⁺)   := r_concat3_1 ᵣ⊛ concat0 u ;
    concat0 (u ▶ₑ⁻ e) := [ concat0 u , e ] .

(*|
SIDETRACK: an alternative implementation of concat0, working pointwise, with precise auxiliary getters

.. coq::

  Equations alt_env_prefix {Δ1 Δ2 b Φ} (u : alt_env Δ1 Δ2 b Φ) {x} (i : ↓[negb b]Φ ∋ x) : context by struct u :=
    alt_env_prefix (u ▶ₑ⁺)   i := alt_env_prefix u i ;
    alt_env_prefix (v ▶ₑ⁻ γ) i with cat_split i := {
      | CLeftV j  := alt_env_prefix v j ;
      | CRightV j := Δ1 +▶ ↓⁺ Φ1 } .

  Equations alt_env_prefix_ren {Δ1 Δ2 b Φ} (u : alt_env Δ1 Δ2 b Φ) {x} (i : ↓[negb b]Φ ∋ x)
            : alt_env_prefix u i ⊆ ((if b then Δ2 else Δ1) +▶ ↓[b]Φ) :=
    alt_env_prefix_ren (u ▶ₑ⁺)   i := r_concat3_1 ⊛ᵣ alt_env_prefix_ren u i ;
    alt_env_prefix_ren (v ▶ₑ⁻ γ) i with cat_split i := {
      | CLeftV j  := alt_env_prefix_ren v j ;
      | CRightV j := r_id } .

  Equations alt_env_get {Δ1 Δ2 b Φ} (u : alt_env Δ1 Δ2 b Φ) {x} (i : ↓[negb b]Φ ∋ x)
            : val (alt_env_prefix u i) x :=
    alt_env_get (u ▶ₑ⁺)   i := alt_env_get u i ;
    alt_env_get (v ▶ₑ⁻ γ) i with cat_split i := {
      | CLeftV j  := alt_env_get v j ;
      | CRightV j := γ _ j } .

  Definition concat0_alt {Δ1 Δ2 b Φ} (u : alt_env Δ1 Δ2 b Φ)
    : ↓[negb b]Φ ⇒ᵥ ((if b then Δ2 else Δ1) +▶ ↓[b]Φ) :=
    fun _ i => alt_env_prefix_ren u i ᵣ⊛ᵥ alt_env_get u i .

  Lemma concat0_alt_eq {Δ1 Δ2 b Φ} (u : alt_env Δ1 Δ2 b Φ) : concat0 u ≡ₐ concat0_alt u .
    intros ? i; unfold concat0_alt.
    revert Δ1 Δ2 b u i; induction Φ; intros Δ1 Δ2 b u i.
    - inversion i.
    - dependent elimination u; cbn.
      * unfold e_ren, e_comp, s_map, v_ren.
        rewrite (IHΦ _ _ _ a0 i); unfold v_ren.
        rewrite v_sub_comp, e_comp_ren_r, v_sub_var, s_ren_comp.
        reflexivity.
      * cbn in i; unfold s_cat, s_cover.
        pose (ii := cat_split i); change (cover_split _ i) with ii; change (cat_split i) with ii.
        destruct ii; cbn.
        + exact (IHΦ _ _ _ a1 i).
        + unfold v_ren; rewrite s_ren_id; symmetry; apply v_var_sub.
  Qed.
|*)

(*|
Flattens a pair of alternating environments for both player and opponent into a "closed" substitution.
|*)
  Equations concat1 {Δ} Φ {b} : alt_env Δ Δ b Φ -> alt_env Δ Δ (negb b) Φ -> ↓[b]Φ ⇒ᵥ Δ :=
    concat1 ∅       _       _         := s_empty ;
    concat1 (Φ ▶ _) (u ▶ₑ⁺)  (v ▶ₑ⁻ e) := [ concat1 Φ u v , [ v_var , concat1 Φ v u ] ⊛ e ] ;
    concat1 (Φ ▶ _) (u ▶ₑ⁻ e) (v ▶ₑ⁺)  := concat1 Φ u v .
  Arguments concat1 {Δ Φ b}.

(*|
lem 4.6
|*)
  Lemma concat_fixpoint {Δ Φ} (u : alt_env Δ Δ Ⓟ Φ) (v : alt_env Δ Δ Ⓞ Φ)
    :  [ v_var , concat1 u v ] ⊛ concat0 u ≡ₐ concat1 v u
     /\ [ v_var , concat1 v u ] ⊛ concat0 v ≡ₐ concat1 u v .
    induction Φ; dependent destruction u; dependent destruction v; cbn; split.
    - intros ? i; dependent elimination i.
    - intros ? i; dependent elimination i.
    - rewrite <- e_comp_ren_l.
      rewrite <- (proj2 (IHΦ v u)).
      apply e_comp_proper; [ | reflexivity ].
      symmetry; apply s_eq_cover_uniq.
      * unfold r_concat3_1.
        now rewrite <- s_ren_comp, 2 s_eq_cat_l.
      * unfold r_concat3_1.
        now rewrite <- s_ren_comp, s_eq_cat_r, s_ren_comp, s_eq_cat_r, s_eq_cat_l.
    - symmetry; apply s_eq_cover_uniq.
      * rewrite <- e_comp_ren_r, s_eq_cat_l.
        symmetry; apply IHΦ.
      * now rewrite <- e_comp_ren_r, s_eq_cat_r.
  Qed.

  Definition m_strat_act Δ : psh alt_ext := fun Φ => (conf (Δ +▶ ↓⁺Φ) * alt_env Δ Δ Ⓟ Φ)%type.
  Definition m_strat_pas Δ : psh alt_ext := fun Φ => alt_env Δ Δ Ⓞ Φ.

  Definition m_strat_wrap {Δ Φ} (x : alt_env Δ Δ Ⓟ Φ)
     : nf' (Δ +▶ ↓⁺ Φ) -> (msg' Δ + h_actv ogs_hg (m_strat_pas Δ) Φ) :=
      fun u =>
        match cat_split (fst (projT2 u)) with
        | CLeftV h => inl (_ ,' (h , nf_msg' u))
        | CRightV h => inr ((_ ,' (h , nf_msg' u)) ,' (x ▶ₑ⁻ nf_val' u))
        end .

  Definition m_strat_play {Δ Φ} (x : m_strat_act Δ Φ)
    : delay (msg' Δ + h_actv ogs_hg (m_strat_pas Δ) Φ)
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
          go (match r in (fiber _ b) return (itree' ogs_e (fun _ : alt_ext => msg' Δ) b) with
              | Fib (inl m) => RetF (m : (fun _ : alt_ext => msg' Δ) Φ)
              | Fib (inr (x ,' p)) => VisF (x : ogs_e.(e_qry) Φ)
                                          (fun r => _m_strat (g_next r) (m_strat_resp p r))
              end).

  Lemma unfold_mstrat {Δ a} (x : m_strat_act Δ a) :
    m_strat a x
    ≊ (emb_delay (m_strat_play x) >>=
        fun j (r : (_ @ a) j) =>
          match r in (fiber _ b) return (itree ogs_e (fun _ : alt_ext => msg' Δ) b)
          with
          | Fib (inl m) => Ret' (m : (fun _ : alt_ext => msg' Δ) a)
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

  Definition inj_init_act {Δ Γ} (c : conf Γ) : m_strat_act Δ (∅ ▶ Γ)
    := ((r_concat_r ⊛ᵣ r_concat_r) ᵣ⊛ₜ c , εₑ ▶ₑ⁺).

  Definition inj_init_pas {Δ Γ} (γ : Γ ⇒ᵥ Δ) : m_strat_pas Δ (∅ ▶ Γ)
    := εₑ ▶ₑ⁻ (r_concat_l ᵣ⊛ γ).

  Definition reduce_t (Δ : context) : Type :=
    ⦉ m_strat_act Δ ×ᵢ m_strat_pas Δ ⦊ᵢ .

  Equations reduce_t_mk {Δ Φ} b (u : alt_env Δ Δ b Φ) (v : alt_env Δ Δ (negb b) Φ)
                         {x} (j : ↓⁺Φ ∋ x) (m : msg x) (γ : dom m ⇒ᵥ (Δ +▶ ↓⁺Φ))
            : (m_strat_act Δ ×ᵢ m_strat_pas Δ) (Φ ▶ dom m) :=
    reduce_t_mk true  u v j m γ := (m_strat_resp v (x,' (j, m)), u ▶ₑ⁻ γ) ;
    reduce_t_mk false u v j m γ := (m_strat_resp u (x,' (j, m)), v ▶ₑ⁻ γ) .

  Equations compo_body {Δ}
    : reduce_t Δ -> delay (reduce_t Δ + msg' Δ) :=
    compo_body x :=
      m_strat_play (fst (projT2 x)) >>= fun _ r =>
          match r with
              | inl r => Ret' (inr r)
              | inr e => Ret' (inl (_ ,' (m_strat_resp (snd (projT2 x)) (projT1 e) , (projT2 e))))
              end.

  Definition split_sub_eval {Γ Δ} (c : conf (Δ +▶ Γ)) (e : Γ ⇒ᵥ Δ) : delay (nf' Δ) :=
    eval ([ v_var , e ] ⊛ₜ c) .

  Definition eval_split_sub {Γ Δ} (c : conf (Δ +▶ Γ)) (e : Γ ⇒ᵥ Δ) : delay (nf' Δ) :=
    eval c >>= fun 'T1_0 u =>
        match cat_split (nf_var' u) with
        | CLeftV h => Ret' (nf_ty' u ,' (h , (nf_msg' u ,' [ v_var,  e ] ⊛ nf_val' u)))
        | CRightV h => eval (app (e _ h) (nf_msg' u) ([v_var , e ] ⊛ nf_val' u))
        end .

  #[global] Instance nf_eq_rfl {Γ t} : Reflexive (@nf_eq Γ t) .
    intros a; exists eq_refl; auto.
  Qed.
  
  #[global] Instance nf_eq_sym {Γ t} : Symmetric (@nf_eq Γ t) .
    intros a b [ p q ].
    unshelve econstructor.
    - now symmetry.
    - intros ? i.
      destruct a as [ m a ] ; cbn in *.
      revert a q i; rewrite p; clear p; intros a q i.
      symmetry; apply q.
  Qed.
  
  #[global] Instance nf_eq_tra {Γ t} : Transitive (@nf_eq Γ t) .
    intros a b c [ p1 q1 ] [ p2 q2 ].
    unfold nf_eq.
    unshelve econstructor.
    - now transitivity (projT1 b).
    - transitivity (rew [fun m : msg t => dom m ⇒ᵥ Γ] p2 in projT2 b); auto.
      now rewrite <- p2.
  Qed.

  #[global] Instance nf_eq_rfl' {Γ} : Reflexiveᵢ (fun _ : T1 => @nf_eq' Γ) .
    intros _ [ x [ i n ] ].
    unshelve econstructor; auto.
  Qed.
  
  #[global] Instance nf_eq_sym' {Γ} : Symmetricᵢ (fun _ : T1 => @nf_eq' Γ) .
    intros _ [ x1 [ i1 n1 ] ] [ x2 [ i2 n2 ] ] [ p [ q1 q2 ] ].
    unshelve econstructor; [ | split ]; cbn in *.
    - now symmetry.
    - revert i1 q1; rewrite p; intros i1 q1; now symmetry.
    - revert n1 q2; rewrite p; intros n1 q2; now symmetry.
  Qed.

  #[global] Instance nf_eq_tra' {Γ} : Transitiveᵢ (fun _ : T1 => @nf_eq' Γ) .
    intros _ [ x1 [ i1 n1 ] ] [ x2 [ i2 n2 ] ] [ x3 [ i3 n3 ] ] [ p1 [ q1 r1 ] ] [ p2 [ q2 r2 ] ].
    unshelve econstructor; [ | split ]; cbn in *.
    - now transitivity x2.
    - transitivity (rew [has Γ] p2 in i2); auto.
      now rewrite <- p2.
    - transitivity (rew [nf Γ] p2 in n2); auto.
      now rewrite <- p2.
  Qed.

  Lemma eval_to_msg_eq {Γ} (a b : delay (nf' Γ)) (H : a ≋ b) :
    fmap_delay (@msg_of_nf' Γ) a ≊ fmap_delay (@msg_of_nf' Γ) b . 
    revert a b H; unfold it_eq; coinduction R CIH; intros a b H.
    unfold comp_eq in H; apply it_eq_step in H.
    cbn in *; unfold observe in H.
    destruct (_observe a), (_observe b); dependent elimination H; econstructor.
    - destruct r_rel as [ p [ q [ r _ ] ] ].
      destruct r1 as [ x1 [ i1 [ m1 a1 ] ] ], r2 as [ x2 [ i2 [ m2 a2 ] ] ].
      unfold msg_of_nf', nf_ty', nf_var', nf_msg' in *; cbn in *.
      revert i1 m1 a1 q r; rewrite p; intros i1 m1 a1 q r.
      now do 2 f_equal.
    - now apply CIH.
    - inversion q1.
  Qed.

  Lemma eval_split {Γ Δ} (c : conf (Δ +▶ Γ)) (e : Γ ⇒ᵥ Δ) : split_sub_eval c e ≋ eval_split_sub c e .
    unfold split_sub_eval, eval_split_sub.
    rewrite (eval_sub c ([ v_var , e ])).
    unfold bind_delay.
    remember (eval c) as t; clear c Heqt.
    revert t; unfold comp_eq,it_eq; coinduction R CIH; cbn; intro t.
    destruct (_observe t); [ | econstructor; apply CIH | inversion q ].
    destruct r as [ x [ i [ m γ ] ] ]; cbn in *.
    destruct (cat_split i).
    + change (?u x (r_cover_l cover_cat x i)) with ((u ⊛ᵣ r_concat_l) x i).
      rewrite s_eq_cat_l.
      eassert (H : _) by exact (eval_nf_ret (x ,' (i , (m ,' ([v_var, e]) ⊛ γ)))).
      unfold comp_eq in H.
      apply it_eq_step in H; cbn in *; unfold observe in H.
      destruct (_observe (eval (app (v_var x i) m (([v_var, e]) ⊛ γ)))); dependent elimination H; auto.
    + change (?u x (r_cover_r cover_cat x j)) with ((u ⊛ᵣ r_concat_r) x j).
      rewrite s_eq_cat_r.
      destruct (_observe (eval (app (e x j) m (([v_var, e]) ⊛ γ)))); econstructor; auto.
      now apply nf_eq_rfl'.
  Qed.


(*|
Interesting facts but not used in the current proof...

.. coq::

  Lemma app_simpl {Γ x} (v : val Γ x) (m : msg x) (e : S.(dom) m ⇒ᵥ Γ) :
    app v m e = [ v_var , e ] ⊛ₜ app (r_concat_l ᵣ⊛ᵥ v) m (v_var ⊛ᵣ r_concat_r) .    
    rewrite app_sub.
    assert (H : v = ([v_var, e] ⊛ᵥ r_concat_l ᵣ⊛ᵥ v)); [ | rewrite <- H; clear H ].
    unfold v_ren.
    pose (foo := s_append s_empty v).
    eassert (H : foo x Ctx.top = v) by reflexivity.
    rewrite <- H at 2.
    do 2 change (?u ⊛ᵥ ?v x Ctx.top)
      with ((u ⊛ v) x Ctx.top).
    etransitivity; cycle 1.
    apply e_comp_proper; [ reflexivity | ].
    symmetry; apply e_comp_ren_l.
    rewrite v_sub_sub.
    etransitivity; cycle 1.
    apply e_comp_proper; [ | reflexivity ].
    rewrite v_sub_var.
    reflexivity.
    rewrite <- e_comp_ren_l.
    etransitivity; cycle 1.
    apply e_comp_proper; [ | reflexivity ].
    rewrite s_eq_cat_l. reflexivity.
    rewrite v_var_sub. exact H.
    apply app_proper.
    rewrite e_comp_ren_r, v_sub_var, s_eq_cat_r; reflexivity.
  Qed.

  Lemma eval_app_simpl {Γ x} (v : val Γ x) (m : msg x) (e : S.(dom) m ⇒ᵥ Γ) :
    eval (app v m e) ≊ eval_sub (app (r_concat_l ᵣ⊛ᵥ v) m (v_var ⊛ᵣ r_concat_r)) e .
    rewrite app_simpl.
    apply eval_split.
  Qed.
|*)

  Equations var_depth (Ψ : alt_ext) b {x} (j : ↓[b] Ψ ∋ x) : nat by struct Ψ :=
    var_depth ∅%ctx        _     (!) ;
    var_depth (Ψ ▶ Γ)%ctx true  i := aux Γ i
      where aux (Γ1 : context) {x1} (i : (↓⁻ Ψ +▶ Γ1) ∋ x1) : nat by struct Γ1 := {
        aux ∅%ctx         i1           := Datatypes.S (var_depth Ψ _ i1) ;
        aux (Γ1 ▶ _)%ctx (Ctx.top)    := Datatypes.O ;
        aux (Γ1 ▶ _)%ctx (Ctx.pop i1) := aux Γ1 i1 
      } ;
    var_depth (Ψ ▶ Γ)%ctx false i := Datatypes.S (var_depth Ψ _ i) .
  Arguments var_depth {Ψ b x} j.

  Lemma var_depth_ext {Ψ Γ x} (j : ↓⁻ Ψ ∋ x)
        : @var_depth (Ψ ▶ Γ) true x (r_concat_l x j) = Datatypes.S (var_depth j) .
    cbn.
    pose (t' := r_concat_l (Δ:=Γ) x j); change (r_concat_l x j) with t' at 1.
    pose (x' := x); change x with x' at 1; change x with x' in t'.
    pose (Γ' := Γ); change Γ with Γ' at 1; change Γ with Γ' in t'.
    remember t' as t_; clear Heqt_ t'.
    remember x' as x_; clear Heqx_ x'.
    remember Γ' as Γ_; clear HeqΓ_ Γ'.
    revert x_ Γ_ t_; induction Γ; intros x_ Γ_ t_; cbn.
    now rewrite r_cover_l_nil.
    now apply IHΓ.
  Qed.

  Definition var_height {Ψ : alt_ext} {b x} (j : ↓[b] Ψ ∋ x) : nat :=
    Nat.sub (c_length Ψ) (var_depth j) .

  Lemma var_depth_le {Ψ : alt_ext} {b x} (j : ↓[b] Ψ ∋ x) : (var_depth j <= c_length Ψ)%nat.
    revert b j; induction Ψ; intros b j; [ inversion j | ].
    destruct b; cbn in *; [ | apply le_n_S, IHΨ ].
    induction x0; [ apply le_n_S, IHΨ | ].
    dependent elimination j; [ now apply le_0_n | now apply IHx0 ].
  Qed.

  Lemma depth_increases {Δ Ψ b} (v : alt_env Δ Δ b Ψ) {x} (j : ↓[negb b] Ψ ∋ x) (k : ↓[b] Ψ ∋ x)
    (H : concat0 v x j = v_var x (r_concat_r x k)) : var_depth j < var_depth k .
    revert b v x j k H; induction Ψ; intros b v t j k H; [ inversion j | ].
    destruct b; cbn in *.
    - pose (k' := k); change k with k' at 1.
      pose (x' := x); change x with x' at 1; change x with x' in k'.
      pose (t' := t); change t with t' at 2; change t with t' in k'.
      remember k' as k_; clear Heqk_ k'.
      remember x' as x_; clear Heqx_ x'.
      remember t' as t_; clear Heqt_ t'.
      revert x_ t_ k_; induction x; intros x_ t_ k_.
      * apply le_n_S.
        dependent elimination v.
        refine (IHΨ _ a _ j k _).
        assert (H2 : @r_concat3_1 typ Δ ↓⁻ Φ ∅ ≡ₐ r_id)
          by (apply s_eq_cover_uniq; [ reflexivity | cbn; now rewrite r_cover_l_nil ]).
        cbn in H; unfold e_ren in H.
        unshelve erewrite (e_comp_proper _ v_var _ _ (concat0 a)) in H;
          [ | now rewrite v_var_sub in H | reflexivity ].
        etransitivity; [ apply s_ren_proper | apply s_ren_id ]; auto.
      * dependent elimination v; dependent elimination k; cbn in *.
        + pose (H' := (_ ,' H) : is_var _).
          assert (Heq : is_var_get H' = Ctx.top) by reflexivity.
          remember H' as H1; clear H' H HeqH1.
          change ((?u ᵣ⊛ concat0 a) x1 j) with (u ᵣ⊛ᵥ concat0 a x1 j) in H1.
          destruct (view_is_var_ren (concat0 a x1 j) _ H1); cbn in Heq.
          destruct (cat_split (is_var_get p)).
          ++ change (?u x1 _) with ((u ⊛ᵣ r_concat_l) _ i) in Heq.
             unfold r_concat3_1 in Heq; rewrite s_eq_cat_l in Heq.
             cbn in Heq; unfold s_ren, s_map, s_pop in Heq; inversion Heq.
          ++ change (?u x1 _) with ((u ⊛ᵣ r_concat_r) _ j0) in Heq.
             unfold r_concat3_1 in Heq; rewrite s_eq_cat_r in Heq.
             cbn in Heq; unfold s_ren, s_map, s_pop in Heq; inversion Heq.
        + apply (IHx (a ▶ₑ⁺) h); cbn.
          pose (H' := (_ ,' H) : is_var _).
          assert (Heq : is_var_get H' = (s_pop ⊛ᵣ r_cover_r cover_cat) x2 h) by reflexivity.
          remember H' as H1; clear H' H HeqH1.
          change ((?u ᵣ⊛ concat0 a) x2 j) with (u ᵣ⊛ᵥ concat0 a x2 j) in H1.
          destruct (view_is_var_ren (concat0 a x2 j) _ H1).
          destruct p; cbn in *.
          unfold e_ren, e_comp, s_map; rewrite e, v_sub_id; unfold s_ren, s_map.
          destruct (cat_split x0).
          ++ change (r_concat3_1 x2 _) with ((@r_concat3_1 _ _ ↓⁻ Φ (x ▶ y) ⊛ᵣ r_concat_l) x2 i) in Heq.
             unfold r_concat3_1 in Heq; rewrite s_eq_cat_l in Heq.
             change (r_concat3_1 x2 _) with ((@r_concat3_1 _ _ ↓⁻ Φ x ⊛ᵣ r_concat_l) x2 i).
             unfold r_concat3_1; rewrite s_eq_cat_l; unfold r_concat_l.
             cbn in Heq; unfold s_pop, s_ren, s_map in Heq.
             remember (@r_cover_l _ _ _ (Δ +▶ (↓⁻ Φ +▶ x)) cover_cat x2 i).
             remember (@r_cover_r _ _ _ (Δ +▶ (↓⁻ Φ +▶ x)) cover_cat x2 h).
             clear -Heq; now dependent induction Heq.
          ++ change (r_concat3_1 x2 _) with ((@r_concat3_1 _ Δ _ (x ▶ y) ⊛ᵣ r_concat_r) x2 j0) in Heq.
             unfold r_concat3_1 in Heq; rewrite s_eq_cat_r in Heq.
             change (r_concat3_1 x2 _) with ((@r_concat3_1 _ Δ _ x ⊛ᵣ r_concat_r) x2 j0).
             unfold r_concat3_1; rewrite s_eq_cat_r; unfold r_concat_l.
             cbn in Heq; unfold s_pop, s_ren, s_map in Heq.
             unfold s_ren, s_map, r_concat_r.
             remember ((@r_cover_r _ _ _ (Δ +▶ (↓⁻ Φ +▶ x)) cover_cat x2 (r_concat_l x2 j0))).
             remember ((@r_cover_r _ _ _ (Δ +▶ (↓⁻ Φ +▶ x)) cover_cat x2 (@r_cover_l _ _ _ (↓⁻ Φ +▶ x) cover_cat x2 j0))).
             clear -Heq; now dependent induction Heq.
    - pose (j' := j); change j with j' at 1.
      pose (x' := x); change x with x' at 1; change x with x' in j'.
      pose (t' := t); change t with t' at 1; change t with t' in j'.
      remember j' as j_; clear Heqj_ j'.
      remember x' as x_; clear Heqx_ x'.
      remember t' as t_; clear Heqt_ t'.
      revert x_ t_ j_; induction x; intros x_ t_ j_.
      * apply le_n_S.
        dependent elimination v.
        refine (IHΨ _ a0 _ j k _).
        cbn in H; unfold s_cat, s_cover in H.
        destruct (cover_split cover_cat j); [ | inversion j ].
        cbn; rewrite r_cover_l_nil; exact H.
      * dependent elimination j; [ apply PeanoNat.Nat.lt_0_succ | ].
        dependent elimination v; cbn.
        eapply (IHx (a0 ▶ₑ⁻ (a1 ⊛ᵣ s_pop))); cbn in *.
        rewrite <- H.
        change (([ ?u , a1 ]) x2 (pop h)) with (([ u , a1 ] ⊛ᵣ s_pop) x2 h).
        apply s_eq_cover_uniq; rewrite <- s_ren_comp.
        + change (s_pop ⊛ᵣ r_cover_l cover_cat) with (@r_cover_l _ _ _ (↓⁻ Φ0 +▶ x ▶ y) cover_cat).
          now rewrite s_eq_cat_l.
        + change (s_pop ⊛ᵣ r_cover_r cover_cat) with (@r_cover_r _ _ _ (↓⁻ Φ0 +▶ x ▶ y) cover_cat ⊛ᵣ s_pop).
          now rewrite s_ren_comp, s_eq_cat_r.
  Qed.

  (*
lemme zig-zag

app v m ...

=eventually>

app w m ...  où not (is_var w)

 thm:
  
  - 1 coup lemme zig-zag
  on est dans le cas où w != var
  n: nf sur laquelle on bloque
  induction sur acc head_inst n  // induction sur la phase de n
  > par cas sur eval (app .. .. ..)
    - si tau -> fini
    - sinon on ret n'
      tour de boucle de "eventually"
      on redémarre sur un app z m' ...
      + lemme zig-zag
      on est dans le cas où z != var
      on est dans un cas où on a `head_inst current n`
*)


  Lemma compo_body_guarded_aux {Δ Ψ} (u : alt_env Δ Δ Ⓟ Ψ) (v : alt_env Δ Δ Ⓞ Ψ)
                                    {x} (m : msg x) (γ : dom m ⇒ᵥ (Δ +▶ ↓⁺ Ψ)) (j : ↓⁺ Ψ ∋ x)
    : ev_guarded (fun 'T1_0 => @compo_body Δ)
          (compo_body ((Ψ ▶ dom m),'
           (app (r_concat3_1 ᵣ⊛ᵥ concat0 v x j) m ((v_var ⊛ᵣ r_concat_r) ⊛ᵣ r_concat_r), v ▶ₑ⁺, u ▶ₑ⁻ γ))) .
    pose (m' := (x ,' m)).
    revert γ j.
    change x with (projT1 m').
    change m with (projT2 m').
    remember m' as m''; clear m' m x Heqm''; rename m'' into m.
    pose (wf := eval_app_not_var m).

    revert Ψ u v; induction wf; intros Ψ u v γ j.
    destruct x as [ x m ]; cbn [projT1 projT2] in *.

    pose (h := lt_wf (var_height j)); remember (var_height j) as n.
    revert Ψ u v γ j Heqn; induction h; intros Ψ u v γ j Heqn.
    
    unfold ev_guarded; cbn -[cat_split].

  pose (vv := @r_concat3_1 typ Δ ↓⁻ Ψ (@dom S x m) ᵣ⊛ᵥ concat0 v x j).
  change (r_concat3_1 ᵣ⊛ᵥ _) with vv; destruct (is_var_dec vv).

    - destruct i as [ i eq ].
      rewrite eq.
      eassert (H3 : _) by exact (eval_nf_ret (_ ,' (i , (m ,' ((v_var ⊛ᵣ r_concat_r) ⊛ᵣ r_concat_r))))).
      unfold comp_eq in H3.
      apply it_eq_step in H3; cbn in H3; unfold observe in H3.
    pose (ot := _observe (eval (app (v_var x i) m ((v_var ⊛ᵣ r_concat_r) ⊛ᵣ r_concat_r)))); fold ot in H3 |- *.
    destruct ot; dependent elimination H3.
    cbn in r1, r_rel |- * .
    destruct r1 as [ x' [ i' [ m' a' ] ] ].
    destruct r_rel as [ p [ q r ] ]; cbn in *.
    unfold m_strat_wrap; unfold dom' in a'; unfold msg_of_nf', nf_ty', nf_var', nf_msg' in *; cbn [ fst snd projT1 projT2] in *.
    revert i' m' a' q r; rewrite p; clear p x'; intros i' m' a' q [ r1 _ ]; cbn in q, r1.
    rewrite q; clear q i'.
    revert a'; rewrite r1; clear r1 m'; intros a'.
    pose (i' := (i ,' eq) : is_var vv).
    change i with (is_var_get i').
    remember i' as ii; clear i i' Heqii eq.
    unfold vv in ii; destruct (view_is_var_ren _ _ ii).
    destruct p; simpl is_var_get.
    destruct (cat_split x1).
    * unfold r_concat3_1; change (?u x (r_cover_l _ x i)) with ((u ⊛ᵣ r_concat_l) x i).
      rewrite s_eq_cat_l, cat_split_l.
      now do 2 econstructor.
    * unfold r_concat3_1; change (?u x (r_cover_r _ x j0)) with ((u ⊛ᵣ r_concat_r) x j0).
      rewrite s_eq_cat_r; unfold s_ren, s_map; rewrite cat_split_r.
      unfold dom', m_strat_resp; cbn [fst snd projT1 projT2].
      refine (GNext _); eapply H2; [ | reflexivity ].

      rewrite Heqn.
      unfold var_height; rewrite var_depth_ext.
      simpl c_length; rewrite PeanoNat.Nat.sub_succ.
      apply (Plus.plus_lt_reg_l_stt _ _ (var_depth j0 + var_depth j)).
      rewrite PeanoNat.Nat.add_shuffle0.
      rewrite Arith_prebase.le_plus_minus_r_stt; [ | exact (@var_depth_le _ false _ j0) ].
      rewrite <- PeanoNat.Nat.add_assoc.
      rewrite Arith_prebase.le_plus_minus_r_stt; [ | exact (@var_depth_le Ψ _ _ j) ].
      rewrite PeanoNat.Nat.add_comm.
      apply Plus.plus_lt_compat_r_stt.
      exact (depth_increases v j j0 e).

  - remember (eval (app vv m ((v_var ⊛ᵣ r_concat_r) ⊛ᵣ r_concat_r))) as t.
    remember (_observe t) as ot.
    destruct ot; try now do 2 econstructor.
    unfold m_strat_wrap.
    destruct r as [ x' [ j' [ m' a' ]]]. unfold nf_msg', nf_val' in *. cbn [ fst snd projT1 projT2 ].
    pose (uu := cat_split j'); change (cat_split j') with uu; destruct uu.
    now do 2 econstructor.
    refine (GNext _).
    unfold dom', msg_msg'; cbn [fst snd projT1 projT2].
    eapply (H0 (x' ,' m')).
    econstructor.
    exact f.
    apply it_eq_unstep; cbn.
    rewrite Heqt in Heqot.
    rewrite <- Heqot.
    econstructor; reflexivity.
    Qed.

  Lemma compo_body_guarded {Δ} : eqn_ev_guarded (fun 'T1_0 => @compo_body Δ).
    intros [] [ Γ [ [c u] v ] ]; unfold m_strat_pas in v.
    unfold ev_guarded; cbn -[cat_split].
    pose (ot := _observe (eval c)); change (_observe (eval c)) with ot.
    destruct ot; try now do 2 econstructor.
    remember r as r'; rewrite Heqr'.
    unfold m_strat_wrap; destruct r as [ ? [ i [ m γ ] ] ]; cbn in *.
    destruct (cat_split i); try now do 2 econstructor.
    refine (GNext _).
    unfold dom', msg_msg', msg_ty'; cbn [ fst snd projT1 projT2 ].
    apply compo_body_guarded_aux.
  Qed.

  Definition compo {Δ a} (u : m_strat_act Δ a) (v : m_strat_pas Δ a) : delay (msg' Δ)
    := iter_ev_guarded _ compo_body_guarded T1_0 (a ,' (u , v)).
  Notation "u ∥ v" := (compo u v) (at level 40).

  (* guilhem: rename? *)
  Definition barb {Γ} Δ (x y : conf Γ) : Prop
    := forall e : Γ ⇒ᵥ Δ, (inj_init_act x ∥ inj_init_pas e) ≈ (inj_init_act y ∥ inj_init_pas e).

  Equations reduce {Δ} : reduce_t Δ -> delay (msg' Δ) :=
    reduce u := eval_in_env
                       ([ v_var , concat1 (snd (fst (projT2 u))) (snd (projT2 u)) ])
                       (fst (fst (projT2 u))) .

  Definition reduce' {Δ} : forall i, reduce_t Δ -> itree ∅ₑ (fun _ : T1 => msg' Δ) i := fun 'T1_0 => reduce .

  Lemma quatre_trois_pre {Δ} (x : reduce_t Δ) :
    (compo_body x >>= fun _ r =>
         match r with
         | inl x' => reduce' _ x'
         | inr y => Ret' (y : (fun _ => msg' _) _)
         end)
    ≊
    (eval (fst (fst (projT2 x))) >>= fun _ u =>
         match cat_split (nf_var' u) with
         | CLeftV h => Ret' (_ ,' (h, nf_msg' u))
         | CRightV h => reduce' _ (_ ,' (m_strat_resp (snd (projT2 x)) (_ ,' (h, nf_msg' u)) ,
                                         snd (fst (projT2 x)) ▶ₑ⁻ nf_val' u))
         end).
    etransitivity; [ now apply bind_bind_com | ].
    etransitivity; [ now apply fmap_bind_com | ].
    unfold m_strat_play, m_strat_wrap.
    remember (eval (fst (fst (projT2 x)))) as t eqn:H; clear H; revert t.
    unfold it_eq; coinduction R CIH; intros t.
    cbn; destruct (t.(_observe)) as [ [ ? [ i [ ? ? ] ] ] | | [] ]; cbn.
    + destruct (cat_split i).
      * econstructor; reflexivity.
      * cbn -[eval_in_env] .
        change (it_eqF _ _ _ _ (_observe ?a) (_observe ?b))
          with (it_eq_map  ∅ₑ (eqᵢ _) (it_eq_t _ (eqᵢ _) R) T1_0 a b).
        reflexivity.
    + econstructor; apply CIH.
  Qed.

  Lemma quatre_trois {Δ a} (c : m_strat_act Δ a) (e : m_strat_pas Δ a)
    : reduce (_ ,' (c , e)) ≊ (c ∥ e) .
    refine (iter_evg_uniq (fun 'T1_0 u => compo_body u) (fun 'T1_0 u => reduce u) _ _ T1_0 _).
    clear a c e; intros [] [ ? [ u v ] ].
    etransitivity; [ | symmetry; apply quatre_trois_pre ].
    unfold reduce at 1.
    etransitivity; [ apply eval_to_msg_eq, eval_split | ].
    etransitivity; [ apply bind_fmap_com | ].
    unfold it_eq; cbn [fst snd projT2 projT1].
    apply (tt_t (it_eq_map ∅ₑ (eqᵢ _))).
    refine (it_eq_up2bind_t _ _ _ _ (eval (fst u) >>= _) (eval (fst u) >>= _) _); econstructor; eauto.
    intros [] [ t1 [ i1 [ m1 γ1 ] ]] [ t2 [ i2 [ m2 γ2 ] ]] [ p [ q r ] ].
    cbn in *.
    revert i1 m1 γ1 q r; rewrite p; clear p t1; intros i1 m1 γ1 q r; cbn in q,r.
    rewrite q; clear q i1.
    destruct r as [ p q ]; cbn in p,q.
    revert γ1 q; rewrite p; clear p m1; intros γ1 q; cbn in q.
    apply (bt_t (it_eq_map ∅ₑ (eqᵢ (fun _ : T1 => msg' Δ)))).
    pose (xx := cat_split i2); change (cat_split i2) with xx; destruct xx.
    - cbn; econstructor; reflexivity.
    - cbn -[it_eq_map fmap].
      change (it_eq_t ∅ₑ (eqᵢ (fun _ : T1 => msg' Δ)) bot) with (it_eq (E:=∅ₑ) (eqᵢ (fun _ : T1 => msg' Δ))).
      apply it_eq_step, fmap_eq.
      unfold m_strat_resp; cbn [fst snd projT1 projT2].
      rewrite app_sub, concat1_equation_2.

      pose (xx := [ v_var , [concat1 v (snd u), ([v_var, concat1 (snd u) v]) ⊛ γ2]] ⊛ᵥ r_concat3_1 ᵣ⊛ᵥ concat0 v t2 j).
      change ([ v_var , [ _ , _ ]] ⊛ᵥ _) with xx.
      assert (H : xx = concat1 (snd u) v t2 j); [ | rewrite H; clear H ].
      + unfold xx; clear xx.
        change (?a ⊛ᵥ ?b ᵣ⊛ᵥ (concat0 v _ j)) with ((a ⊛ (b ᵣ⊛ concat0 v)) _ j).
        unfold e_ren; rewrite v_sub_sub.
        etransitivity; [ | now apply (proj2 (concat_fixpoint (snd u) v)) ].
        eapply e_comp_proper; [ | reflexivity ].
        rewrite e_comp_ren_r, v_sub_var.
        unfold r_concat3_1.
        etransitivity; [ unfold s_ren at 1; apply s_eq_cover_map | ].
        change (s_map ?a ?b) with (s_ren a b); change (s_cover cover_cat ?a ?b) with ([ a , b ]).
        now rewrite s_eq_cat_l, s_ren_comp, s_eq_cat_r, s_eq_cat_l.
      + erewrite app_proper; [ reflexivity | ].
        now rewrite q, 2 e_comp_ren_r, v_sub_var, 2 s_eq_cat_r.
   Qed.

  Lemma quatre_trois_app {Γ Δ} (c : conf Γ) (e : Γ ⇒ᵥ Δ)
        : eval_in_env e c ≊ (inj_init_act c ∥ inj_init_pas e).
    rewrite <- quatre_trois.
    unfold reduce, inj_init_act, eval_in_env; cbn [fst snd projT1 projT2]; apply fmap_eq.
    unfold inj_init_pas; rewrite concat1_equation_2, 2 concat1_equation_1.
    unfold c_ren; rewrite c_sub_sub, c_sub_proper ; try reflexivity.
    rewrite s_eq_cover_empty_r.
    rewrite e_comp_ren_r, v_sub_var.
    rewrite s_ren_comp, 2 s_eq_cat_r.
    unfold e_ren, r_concat_l, cover_cat; cbn; rewrite r_cover_l_nil, s_ren_id.
    now rewrite 2 v_var_sub.
  Qed.

  Theorem barb_correction {Γ} Δ (x y : conf Γ) : barb Δ x y -> ciu Δ x y.
    intros H e.
    etransitivity; [ apply it_eq_wbisim, (quatre_trois_app x e) | ].
    etransitivity; [ apply (H e) | ].
    symmetry; apply it_eq_wbisim, (quatre_trois_app y e).
  Qed.

  (* Alternative definition of the composition easier to prove
  congruence (respecting weak bisimilarity). *)

  Definition compo_alt_t (Δ : context) : Type :=
    ⦉ ogs_act Δ ×ᵢ ogs_pas Δ ⦊ᵢ .

  Notation "'RetD' x" := (RetF (x : (fun _ : T1 => _) T1_0)) (at level 40).
  Notation "'TauD' t" := (TauF (t : itree ∅ₑ (fun _ : T1 => _) T1_0)) (at level 40).

  Equations compo_alt_body {Δ} : compo_alt_t Δ -> delay (compo_alt_t Δ + msg' Δ) :=
    compo_alt_body :=
      cofix _compo_body u :=
        go match (fst (projT2 u)).(_observe) with
            | RetF r => RetD (inr r)
            | TauF t => TauD (_compo_body (_ ,' (t , (snd (projT2 u)))))
            | VisF e k => RetD (inl (_ ,' (snd (projT2 u) e , k)))
            end .

  Definition compo0 {Δ a} (u : ogs_act Δ a) (v : ogs_pas Δ a) : delay (msg' Δ)
    := iter_delay compo_alt_body (a ,' (u , v)).

  Definition compo_t_eq (Δ : context) : relation (compo_alt_t Δ) :=
    fun x1 x2 =>
     exists p : projT1 x1 = projT1 x2,
       rew p in fst (projT2 x1) ≈ fst (projT2 x2)
       /\ h_pasvR ogs_hg (it_wbisim (eqᵢ _)) _ (rew p in snd (projT2 x1)) (snd (projT2 x2)). 

  Definition compo_t_eq_strong (Δ : context) : relation (compo_alt_t Δ) :=
    fun x1 x2 =>
     exists p : projT1 x1 = projT1 x2,
       rew p in fst (projT2 x1) ≊ fst (projT2 x2)
       /\ h_pasvR ogs_hg (it_eq (eqᵢ _)) _ (rew p in snd (projT2 x1)) (snd (projT2 x2)). 

  #[global] Instance compo_alt_proper {Δ a}
    : Proper (it_wbisim (eqᵢ _) a ==> h_pasvR ogs_hg (it_wbisim (eqᵢ _)) a ==> it_wbisim (eqᵢ _) T1_0)
        (@compo0 Δ a).
    intros x y H1 u v H2.
    unshelve eapply (iter_weq (RX := fun _ => compo_t_eq Δ)); [ | exact (ex_intro _ eq_refl (conj H1 H2)) ].
    clear a x y H1 u v H2; intros [] [ ? [ x u ]] [ ? [ y v ]] [ H1 H2 ].
    cbn in H1; destruct H1; cbn in H2; destruct H2 as [ H1 H2 ].
    unfold it_wbisim; revert x y H1; coinduction R CIH; intros x y H1.
    apply it_wbisim_step in H1; cbn in *; unfold observe in H1; destruct H1 as [ ? ? r1 r2 rr ].
    dependent destruction rr.
    - unshelve econstructor.
      * exact (RetF (inr r0)).
      * exact (RetF (inr r3)).
      * remember (_observe x) eqn:H; clear H.
        remember (@RetF alt_ext ogs_e (fun _ => msg' Δ) (ogs_act Δ) x0 r0) eqn:H.
        apply (fun u => rew <- [ fun v => it_eat _ _ v ] H in u) in r1.
        induction r1; [ now rewrite H | eauto ].
      * remember (_observe y) eqn:H; clear H.
        remember (@RetF alt_ext ogs_e (fun _ => msg' Δ) (ogs_act Δ) x0 r3) eqn:H.
        apply (fun u => rew <- [ fun v => it_eat _ _ v ] H in u) in r2.
        induction r2; [ now rewrite H | eauto ].
      * now repeat econstructor.
    - unshelve econstructor.
      * exact (TauD (compo_alt_body (_ ,' (t1 , u)))).
      * exact (TauD (compo_alt_body (_ ,' (t2 , v)))).
      * remember (_observe x) eqn:H; clear H.
        remember (TauF t1) eqn:H.
        induction r1; [ now rewrite H | auto ].
      * remember (_observe y) eqn:H; clear H.
        remember (TauF t2) eqn:H.
        induction r2; [ now rewrite H | auto ].
      * auto.
    - unshelve econstructor.
      * exact (RetF (inl (_ ,' (u q , k1)))).
      * exact (RetF (inl (_ ,' (v q , k2)))).
      * remember (_observe x) eqn:H; clear H.
        remember (VisF q k1) eqn:H.
        induction r1; [ now rewrite H | auto ].
      * remember (_observe y) eqn:H; clear H.
        remember (VisF q k2) eqn:H.
        induction r2; [ now rewrite H | auto ].
      * unshelve (do 3 econstructor); [ exact eq_refl | exact (conj (H2 q) k_rel) ].
   Qed.

  Definition reduce_t_inj {Δ : context} (x : reduce_t Δ) : compo_alt_t Δ
     := (_ ,' (m_strat _ (fst (projT2 x)) , m_stratp _ (snd (projT2 x)))) .
  
  Lemma compo_compo_alt {Δ} {x : reduce_t Δ}
        : iter_delay compo_alt_body (reduce_t_inj x) ≊ iter_delay compo_body x .

    apply (iter_cong_strong (RX := fun _ a b => compo_t_eq_strong _ a (reduce_t_inj b))); cycle 1.

    cbn; destruct (reduce_t_inj x) as [ ? [] ].
    exists eq_refl; split; cbn; [ | intro r ]; reflexivity.
    
    intros [] [? [u1 e1]] [? [u2 e2]] [A B].
    dependent elimination A; cbn in B; destruct B as [H1 H2].
    rewrite unfold_mstrat in H1.
    unfold compo_body; cbn [fst snd projT1 projT2].
    remember (m_strat_play u2) eqn:Hu; clear Hu.
    clear u2; unfold it_eq; revert u1 d H1; coinduction R CIH; intros u1 d H1.
    apply it_eq_step in H1; cbn in *; unfold observe in *.
    destruct (_observe d).
    + destruct r as [ | [] ]; destruct (_observe u1); dependent elimination H1;
        econstructor; econstructor; eauto.
      exists eq_refl; split; [ exact (H2 q0) | exact k_rel ].
    + destruct (_observe u1); dependent elimination H1; eauto.
    + destruct q.
  Qed.

  Theorem ogs_correction {Γ} Δ (x y : conf Γ)
    : inj_init_act (Δ:=Δ) x ≈ₐ inj_init_act y -> ciu Δ x y.
    intro H; apply barb_correction.
    intro e; unfold compo.
    rewrite 2 iter_evg_iter.
    change (iter _ T1_0 ?u) with (iter_delay compo_body u).
    rewrite <- 2 compo_compo_alt.
    apply compo_alt_proper; [ exact H | intro; reflexivity ].
  Qed.

End withInteractionSpec.
About ogs_correction.
Print Assumptions ogs_correction.
