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
Record interaction_spec : Type := {
  typ : Type ;
  msg : typ -> Type ;
  dom : forall t, msg t -> ctx typ ;
}.
Arguments dom _ [_].

Section withInteractionSpec.

  Context (S : interaction_spec).

  Notation typ := (S.(typ)).
  Notation msg := (S.(msg)).
(*|
Contexts of types (meta [Γ])
|*)
  Notation context := (ctx typ).

(*|
Lifting the notion of message to context:
given a context Γ, a [msg'] is a message over a [typ] contained in Γ.
|*)
  Definition msg' (Γ : context) : Type :=
    { t : typ & Γ ∋ t * msg t }%type.

(*|
Lifting the notion of domain to context:
Given a context Γ, the domain of a message over Γ is the domain of its typ-level message component.
|*)
  Definition dom' {Γ} (m : msg' Γ) : context :=
    S.(dom) (snd (projT2 m)).

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
  Class machine : Type := {
    conf : context -> Type ;
    val : context -> typ -> Type ;
    eval {Γ} : conf Γ -> delay { m : msg' Γ & dom' m =[val]> Γ } ;
    app {Γ x} (v : val Γ x) (m : msg x) (r : S.(dom) m =[val]> Γ): conf Γ ;
    v_var {Γ} : Γ =[val]> Γ ; (*  Γ ∋ x -> val Γ x   *)
    v_sub {Γ Δ} : Γ =[val]> Δ -> val Γ ⇒ᵢ val Δ ;
    c_sub {Γ Δ} : Γ =[val]> Δ -> conf Γ -> conf Δ ;
    }.

  Notation "u ⊛ᵥ v" := (v_sub u _ v) (at level 30).
  Notation "u ⊛ₜ c" := (c_sub u c) (at level 30).
  Notation "Γ ⇒ᵥ Δ" := (Γ =[val]> Δ) (at level 30).

  Context {M : machine}.

  Definition emb {Γ} (m : msg' Γ) : conf (Γ +▶ dom' m) :=
    app (v_var _ (r_concat_l _ (fst (projT2 m)))) (snd (projT2 m)) (v_var ⊛ᵣ r_concat_r).

  (*
  Definition app' {Γ Δ} (e : Γ ⇒ᵥ Δ) (m : msg' Γ) : conf (Δ +▶ dom' m) :=
    app (e (projT1 m) (fst (projT2 m))) (snd (projT2 m)) .
  *)



(*|
Renaming in values, a particular case of value substitution.
|*)
  Definition v_ren {Γ Δ} : Γ ⊆ Δ -> val Γ ⇒ᵢ val Δ :=
    fun u => v_sub (v_var ⊛ᵣ u) .
  Notation "r ᵣ⊛ᵥ v" := (v_ren r _ v) (at level 14).

(*|
Composition of value assignments.
|*)
  Definition e_comp {Γ1 Γ2 Γ3} : Γ2 ⇒ᵥ Γ3 -> Γ1 ⇒ᵥ Γ2 -> Γ1 ⇒ᵥ Γ3
    := fun u v => s_map (v_sub u) v.
  Infix "⊛" := e_comp (at level 14).

(*|
Renaming in environments
|*)
  Definition e_ren {Γ1 Γ2 Γ3} : Γ2 ⊆ Γ3 -> Γ1 ⇒ᵥ Γ2 -> Γ1 ⇒ᵥ Γ3
    := fun u v => (v_var ⊛ᵣ u) ⊛ v.
  Infix "ᵣ⊛" := e_ren (at level 14).

(*|
Renaming in configurations
|*)
  Definition c_ren {Γ1 Γ2} : Γ1 ⊆ Γ2 -> conf Γ1 -> conf Γ2
    := fun u c => (v_var ⊛ᵣ u) ⊛ₜ c .
  Infix "ᵣ⊛ₜ" := c_ren (at level 14).

  Definition is_var {Γ x} (v : val Γ x) : Type := { i : Γ ∋ x & v = v_var x i } .

  Definition is_var_get {Γ x} {v : val Γ x} (p : is_var v) : Γ ∋ x := projT1 p .
  Definition is_var_get_eq {Γ x} {v : val Γ x} (p : is_var v) : v = v_var x (is_var_get p) := projT2 p .

(*|
Operational machine: axiomatization
====================================
The machine comes with a battery of expected laws:
- value substitution respects the equivalence of assignments ([sub_eq])
- configuration substitution respects the equivalence of assignments ([sub_eq])
- the embedding of variables is the unit for composition of assignments
- the composition of value assignments is associative
- the embedding of variables is the unit substitution on terms
- the composition o substitution on terms commutes with the composition of assignments
|*)
  Class machine_law_ty : Type := {
    is_var_dec {Γ x} (v : val Γ x) : is_var v + (is_var v -> False) ;
    is_var_ren {Γ1 Γ2 x} (v : val Γ1 x) (e : Γ1 ⊆ Γ2) : is_var (e ᵣ⊛ᵥ v) -> is_var v ;
  }.
  Context {MHT : machine_law_ty}.
                                    
  Class machine_law : Prop := {
    v_sub_proper {Γ Δ} :: Proper (ass_eq Γ Δ ==> forall_relation (fun i => eq ==> eq)) v_sub ;
    c_sub_proper {Γ Δ} :: Proper (ass_eq Γ Δ ==> eq ==> eq) c_sub ;
    v_sub_var {Γ1 Γ2} (p : Γ1 ⇒ᵥ Γ2) : p ⊛ v_var ≡ₐ p ;
    v_var_sub {Γ1 Γ2} (p : Γ1 ⇒ᵥ Γ2) : v_var ⊛ p ≡ₐ p ;
    v_sub_sub {Γ1 Γ2 Γ3 Γ4} (p : Γ3 ⇒ᵥ Γ4) (q : Γ2 ⇒ᵥ Γ3) (r : Γ1 ⇒ᵥ Γ2)
      : p ⊛ (q ⊛ r) ≡ₐ (p ⊛ q) ⊛ r ;
    c_var_sub {Γ} (c : conf Γ) : v_var ⊛ₜ c = c ;
    c_sub_sub {Γ1 Γ2 Γ3} (u : Γ2 ⇒ᵥ Γ3) (v : Γ1 ⇒ᵥ Γ2) {c}
      : u ⊛ₜ (v ⊛ₜ c) = (u ⊛ v) ⊛ₜ c ;
    app_proper {Γ x v m} :: Proper (ass_eq (S.(dom) m) Γ ==> eq) (@app _ Γ x v m) ;
    app_ren {Γ1 Γ2 x} (e : Γ1 ⇒ᵥ Γ2) (v : val Γ1 x) (m : msg x) (r : dom _ m ⇒ᵥ Γ1)
      : e ⊛ₜ app v m r = app (e ⊛ᵥ v) m (e ⊛ r) ;
    v_var_inj {Γ x} (i j : Γ ∋ x) : v_var x i = v_var x j -> i = j ;
  }.
  Context {MH : machine_law}.

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

(*|
Evaluate a configuration inside an environment (assignment), returning only the message part (the "positive" or "static" part).
|*)
  Definition eval_in_env {Γ Δ} (e : Γ ⇒ᵥ Δ) (t : conf Γ) : delay (msg' Δ)
    := fmap (fun _ => @projT1 _ _) _ (eval (e ⊛ₜ t)).

  #[global] Instance eval_in_env_proper {Γ Δ} : Proper (ass_eq Γ Δ ==> eq ==> eq) (@eval_in_env Γ Δ).
    intros ? ? H1 ? ? H2; unfold eval_in_env.
    now rewrite H1, H2.
  Qed.

  Definition ciu {Γ} Δ (x y : conf Γ) : Prop
    := forall e : Γ ⇒ᵥ Δ, eval_in_env e x ≈ eval_in_env e y.

  (* Section 3: game definition
     ↓+ ~ join_even
   *)
  Definition alt_ext : Type := ctx (context).
  Notation "↓⁺ a" := (join_even a) (at level 9).
  Notation "↓⁻ a" := (join_odd a) (at level 9).
  Notation "↓[ b ] a" := (join_even_odd_aux b a) (at level 9).

  Definition ogs_hg : half_game alt_ext alt_ext :=
    {|
      g_move := fun es => msg' ↓⁺es ;
      g_next := fun es m => (es ▶ dom' m) ;
    |}.

  Definition ogs_g : game alt_ext alt_ext :=
    {|
      g_client := ogs_hg ;
      g_server := ogs_hg ;
    |}.

  Definition ogs_e : event alt_ext alt_ext := e_of_g ogs_g.

  Definition ogs_act (Δ : context) : psh alt_ext := itree ogs_e (fun _ => msg' Δ).
  Definition ogs_pas (Δ : context) : psh alt_ext := h_pasv ogs_hg (ogs_act Δ).

  Notation "Ⓟ" := true.
  Notation "Ⓞ" := false.

  (* Env* (def 3.12)
     Env M Δ player es : environment part of the player (aka active at es) configuration at (Δ + es)
     Env M Δ opponent es : environment part of the opponent (aka passive at es) configuration at (Δ + es)
   *)
  Inductive alt_env (Δ : context) : bool -> alt_ext -> Type :=
  | ENil {b} : alt_env Δ b ∅
  | EConT {Φ Γ} : alt_env Δ Ⓞ Φ -> alt_env Δ Ⓟ (Φ ▶ Γ)
  | EConF {Φ Γ} : alt_env Δ Ⓟ Φ -> Γ ⇒ᵥ (Δ +▶ ↓⁺Φ) -> alt_env Δ Ⓞ (Φ ▶ Γ)
  .
  Arguments ENil {Δ b}.
  Arguments EConT {Δ Φ Γ}.
  Arguments EConF {Δ Φ Γ}.

  Notation εₑ := (ENil) .
  Notation "u ▶ₑ⁺" := (EConT u) (at level 40).
  Notation "u ▶ₑ⁻ e" := (EConF u e) (at level 40).

  (* flattens an alternating environment into an unstructured one *)
  Equations concat0 {Δ b Φ} : alt_env Δ b Φ -> ↓[negb b]Φ ⇒ᵥ (Δ +▶ ↓[b]Φ) :=
    concat0 (εₑ)     := s_empty ;
    concat0 (u ▶ₑ⁺)   := r_concat3_1 ᵣ⊛ concat0 u ;
    concat0 (u ▶ₑ⁻ e) := [ concat0 u , e ] .

  (* Flattens a pair of alternating environments for resp. player and opponent into a "closed" substitution *)
  Equations concat1 {Δ} Φ {b} : alt_env Δ b Φ -> alt_env Δ (negb b) Φ -> ↓[b]Φ ⇒ᵥ Δ :=
    concat1 ∅       _       _         := s_empty ;
    concat1 (Φ ▶ _) (u ▶ₑ⁺)  (v ▶ₑ⁻ e) := [ concat1 Φ u v , [ v_var , concat1 Φ v u ] ⊛ e ] ;
    concat1 (Φ ▶ _) (u ▶ₑ⁻ e) (v ▶ₑ⁺)  := concat1 Φ u v .
  Arguments concat1 {Δ Φ b}.

  (* lem 4.6 *)
  Lemma concat_fixpoint {Δ Φ} (u : alt_env Δ Ⓟ Φ) (v : alt_env Δ Ⓞ Φ)
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

  Definition m_strat_act Δ : psh alt_ext :=
    fun Φ => (conf (Δ +▶ ↓⁺Φ) * alt_env Δ Ⓟ Φ)%type.

  Definition m_strat_pas Δ : psh alt_ext :=
    fun Φ => alt_env Δ Ⓞ Φ.

  Definition m_strat_wrap {Δ Φ} (x : alt_env Δ Ⓟ Φ)
     : {m : msg' (Δ +▶ ↓⁺ Φ) & dom' m ⇒ᵥ (Δ +▶ ↓⁺ Φ)} -> (msg' Δ + h_actv ogs_hg (m_strat_pas Δ) Φ) :=
      fun u =>
        match cat_split (fst (projT2 (projT1 u))) with
        | CLeftV h => inl (_ ,' (h , snd (projT2 (projT1 u))))
        | CRightV h => inr ((_ ,' (h , snd (projT2 (projT1 u))))
                            ,' (x ▶ₑ⁻ projT2 u))
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
          go (match r
              in (fiber _ b) return (itree' ogs_e (fun _ : alt_ext => msg' Δ) b)
              with
              | Fib (inl m) => RetF (m : (fun _ : alt_ext => msg' Δ) a)
              | Fib (inr (x ,' p)) => VisF (x : ogs_e.(e_qry) _)
                                          (fun r => m_strat (g_next r) (m_strat_resp p r))
              end)).
    apply it_eq_unstep.
    cbn -[m_strat_play].
    destruct (_observe (m_strat_play x)) as [ [ | [] ] | | [] ]; eauto.
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

  (*
  Definition reduce_t_mk {Δ Φ} b (u : alt_env Δ b Φ) (v : alt_env Δ (negb b) Φ)
                         {x} (j : ↓[b]Φ ∋ x) (m : msg x) (γ : dom S m ⇒ᵥ (Δ +▶ ↓[b]Φ))
        : (m_strat_act Δ ×ᵢ m_strat_pas Δ) (Φ ▶ dom S m) .
    destruct b.
    - refine (m_strat_resp v (x,' (j, m)), u ▶ₑ⁻ γ).
    - refine (m_strat_resp u (x,' (_, m)), v ▶ₑ⁻ γ).
    - refine ((_ , u) , v).
    exact 
  Defined.
*)

  (*
  Lemma reduce_t_mk_conf {Δ Φ} b (c : conf (Δ +▶ ↓⁺Φ)) (u : alt_env Δ b Φ) (v : alt_env Δ (negb b) Φ)
                             : fst (fst (reduce_t_mk b c u v)) = c .
    now destruct b.
  Qed.
*)

  Equations compo_body {Δ}
    : reduce_t Δ -> delay (reduce_t Δ + msg' Δ) :=
    compo_body x :=
      m_strat_play (fst (projT2 x)) >>= fun _ r =>
          match r with
              | inl r => Ret' (inr r)
              | inr e => Ret' (inl (_ ,' (m_strat_resp (snd (projT2 x)) (projT1 e) , (projT2 e))))
              end.

  (* Now we prove guardedness of this equation. *)

  Definition sub_eval {Γ Δ} (c : conf (Δ +▶ Γ)) (e : Γ ⇒ᵥ Δ)
             : delay { m : msg' Δ & dom' m ⇒ᵥ Δ } :=
        eval ([ v_var , e ] ⊛ₜ c) .

  Definition eval_sub {Γ Δ} (c : conf (Δ +▶ Γ)) (e : Γ ⇒ᵥ Δ)
    : delay { m : msg' Δ & dom' m ⇒ᵥ Δ }.
    refine (eval c >>= fun 'T1_0 x =>
                match cat_split (fst (projT2 (projT1 x))) with
                | CLeftV h => Ret'
                               ((_ ,' (h , snd (projT2 (projT1 x)))) ,' [ v_var,  e ] ⊛ (projT2 x))
                | CRightV h => _
                end) .
    refine (eval ([ e , ([v_var , e ] ⊛ projT2 x) ] ⊛ₜ (emb (_ ,' (h , (snd (projT2 (projT1 x)))))))).
  Defined.

  Hypothesis eval_hyp : forall {Γ Δ}
                          (c : conf (Δ +▶ Γ))
                          (e : Γ ⇒ᵥ Δ),
                          sub_eval c e ≊ eval_sub c e .

  Hypothesis eval_app_var : forall Γ x (v : val Γ x) (m : msg x) (e : S.(dom) m ⇒ᵥ Γ)
                              (p : is_var v),
      eval (app v m e) ≊ Ret' ((x ,' (is_var_get p , m)) ,' e).

  Lemma app_simpl {Γ x} (v : val Γ x) (m : msg x) (e : S.(dom) m ⇒ᵥ Γ) :
    app v m e = [ v_var , e ] ⊛ₜ app (r_concat_l ᵣ⊛ᵥ v) m (v_var ⊛ᵣ r_concat_r) .    
    rewrite app_ren.
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
    apply eval_hyp.
  Qed.

  (*
  Lemma m_strat_play_app_simpl {Γ x} (v : val Γ x) (m : msg x) (e : S.(dom) m ⇒ᵥ Γ) :
    eval (app v m e) ≊ eval_sub (app (r_concat_l ᵣ⊛ᵥ v) m (v_var ⊛ᵣ r_concat_r)) e .

*)
  

  Variant is_tau' {I} {E : event I I} {X i} : itree' E X i -> Prop :=
    | IsTau {t : itree E X i} : is_tau' (TauF t) .

  Definition is_tau {I} {E : event I I} {X i} (t : itree E X i) : Prop := is_tau' t.(_observe).

  Hypothesis eval_app_not_var : forall Γ x (v : val Γ x) (m : msg x) (e : S.(dom) m ⇒ᵥ Γ)
                                  (p : is_var v -> False), is_tau (eval (app v m e)) .

  Lemma cat_split_l {X} {Γ1 Γ2} {x : X} (i : Γ1 ∋ x) : cat_split (r_concat_l (Δ:=Γ2) _ i) = CLeftV i .
    pose (uu := cat_split (r_concat_l (Δ:=Γ2) x i)); fold uu.
    dependent induction uu.
    - apply r_cover_l_inj in x1; rewrite x1 in x.
      dependent destruction x; simpl_depind; reflexivity.
    - symmetry in x1; apply r_cover_disj in x1; destruct x1.
  Qed.

  Lemma cat_split_r {X} {Γ1 Γ2} {x : X} (i : Γ2 ∋ x) : cat_split (r_concat_r (Γ:=Γ1) _ i) = CRightV i .
    pose (uu := cat_split (r_concat_r (Γ:=Γ1) x i)); fold uu.
    dependent induction uu.
    - apply r_cover_disj in x1; destruct x1.
    - apply r_cover_r_inj in x1; rewrite x1 in x.
      dependent destruction x; simpl_depind; reflexivity.
  Qed.

  Definition compo_body_guarded {Δ} : eqn_ev_guarded (fun 'T1_0 => @compo_body Δ).
  intros [] [ Γ [ [c u] v ] ]; unfold m_strat_pas in v.
  
  unfold ev_guarded; cbn -[cat_split].
  (*rewrite reduce_t_mk_conf.*)
  pose (ot := _observe (eval c)); change (_observe (eval c)) with ot.
  destruct ot; clear c; try now do 2 econstructor.
  unfold m_strat_wrap; pose (h := cat_split (fst (projT2 (projT1 r)))); change (cat_split _) with h.
  destruct r as [ [ ? [ i m ] ] γ]; unfold dom' in *; cbn in *.
  destruct h; try now do 2 econstructor.
  cbn in *.

  (*
  pose (p := Ⓟ); change Ⓟ with p in u; change Ⓞ with (negb p) in v.
  change (↓⁺ Γ) with (↓[p] Γ) in γ,j.
  remember p as b.
*)
  
  refine (GNext _).
  
  revert u v x m γ j; induction Γ; intros u v ? m γ j; [ dependent elimination j | ].
  change (ev_guarded' ?e (_observe ?u)) with (ev_guarded e u) in IHΓ.

  unfold m_strat_resp; cbn [fst snd projT1 projT2].

  cbn -[cat_split].
  pose (vv := @r_concat3_1 typ Δ ↓⁻ (Γ ▶ x) (@dom S x0 m) ᵣ⊛ᵥ concat0 v x0 j).
  change (r_concat3_1 ᵣ⊛ᵥ _) with vv.
  destruct (is_var_dec vv); cycle 1.

  * eassert (H : _) by exact (eval_app_not_var _ _ _ m (v_var ⊛ᵣ (@r_concat_r _ Δ _ ⊛ᵣ @r_concat_r _ ↓⁺ Γ (@dom S x0 m))) f).
    unfold is_tau in H.
    pose (ot0 := _observe (eval (app vv m (v_var ⊛ᵣ (@r_concat_r _ Δ _ ⊛ᵣ @r_concat_r _ ↓⁺ Γ (@dom S x0 m)))))).
    change (_observe (eval _)) with ot0 in H |- *.
    remember ot0 as ot; clear Heqot.
    dependent elimination H.
    repeat econstructor.
  * eassert (H : _) by exact (eval_app_var _ _ _ m (v_var ⊛ᵣ (@r_concat_r _ Δ _ ⊛ᵣ @r_concat_r _ ↓⁺ Γ (@dom S x0 m))) i).
    apply it_eq_step in H; cbn in H; unfold observe in H.
    pose (ot0 := _observe (eval (app vv m (v_var ⊛ᵣ (@r_concat_r _ Δ _ ⊛ᵣ @r_concat_r _ ↓⁺ Γ (@dom S x0 m)))))).
    change (_observe (eval _)) with ot0 in H |- *.
    unfold m_strat_wrap, dom'.
    dependent elimination H; cbn -[cat_split]; rewrite r_rel; clear r1 r_rel.
    cbn [fst snd projT1 projT2].

    eassert (i1 : _) by exact (is_var_ren _ _ i).
    rewrite (is_var_irr i (ren_is_var _ _ i1)); clear i.

    pose (xx := is_var_get (ren_is_var (@concat0 Δ Ⓞ (Γ ▶ x) v x0 j) (@r_concat3_1 typ Δ ↓⁻ (Γ ▶ x) (@dom S x0 m)) i1)).
    change (is_var_get _) with xx.
    eassert (H : _) by exact (ren_is_var_get (@concat0 Δ Ⓞ (Γ ▶ x) v x0 j) (@r_concat3_1 typ Δ ↓⁻ (Γ ▶ x) (@dom S x0 m)) i1).
    change (is_var_get _) with xx in H at 1.
    rewrite H. dependent elimination i1; cbn in *. clear xx H vv e j.

    remember (r_concat3_1 x0 x1).
    destruct (cat_split x1).
    ** change (r_concat3_1 x0 (r_cover_l cover_cat x0 i))
         with ((@r_concat3_1 typ Δ ↓⁺ Γ (@dom S x0 m) ⊛ᵣ r_concat_l) x0 i) in Heqh.
       rewrite (eq_trans Heqh (s_eq_cat_l _ _ _ _)).
       rewrite cat_split_l.
       do 2 econstructor.
    ** change (r_concat3_1 x0 (r_cover_l cover_cat x0 j))
         with ((@r_concat3_1 typ Δ ↓⁺ Γ (@dom S x0 m) ⊛ᵣ r_concat_l) x0 j) in Heqh.
       rewrite (eq_trans Heqh (s_eq_cat_r _ _ _ _)); clear h Heqh.
       unfold s_ren at 1, s_map; rewrite cat_split_r.
       unfold m_strat_resp, dom'; cbn.
       

       (*
       rewrite app_ren.
  
       unshelve erewrite (app_proper _ _ _); [ shelve | | ].
       rewrite e_comp_ren_r, v_sub_var, s_eq_cat_r.
       reflexivity.

       eassert (H : ([r_concat3_1 ᵣ⊛ ([concat0 u, γ]), v_var ⊛ᵣ (r_concat_r ⊛ᵣ r_concat_r)]
               ⊛ᵥ v_var x0 (r_concat_l x0 (r_concat_l x0 j))) = _); [ | rewrite H; clear H ].

       change (?u ⊛ᵥ v_var x0 (r_concat_l x0 (r_concat_l x0 j)))
         with ((u ⊛ (v_var ⊛ᵣ r_concat_l ⊛ᵣ r_concat_l)) x0 j).
       rewrite e_comp_ren_r.

       etransitivity; [ apply s_ren_proper; [ | reflexivity ] | ].
       rewrite e_comp_ren_r.
       rewrite v_sub_var.
       apply s_eq_cat_l.

       unfold e_ren.
       rewrite <- e_comp_ren_r.
       etransitivity; [ apply e_comp_proper; [ reflexivity | apply s_eq_cat_l ] | ].
       rewrite e_comp_ren_l, v_var_sub.
       reflexivity.
*)

       dependent elimination u; dependent elimination v; simp concat0; cbn in *.

       eassert (H : r_concat3_1 ᵣ⊛ᵥ ([r_concat3_1 ᵣ⊛ concat0 a, γ]) x0 (r_concat_l x0 j) = _); [ | rewrite H; clear H ].
       change (?a ᵣ⊛ᵥ ?b x0 (r_concat_l x0 j))
         with ((a ᵣ⊛ (b ⊛ᵣ r_concat_l)) x0 j).
       unfold e_ren.
       etransitivity; [ apply e_comp_proper; [ reflexivity | apply s_eq_cat_l ] | ].
       rewrite v_sub_sub.
       etransitivity; [ apply e_comp_proper; [ | reflexivity ] | ].
       rewrite e_comp_ren_r, v_sub_var; reflexivity.
       reflexivity.

       (*
       unfold r_concat3_1 at 2.
       transitivity (v_var ⊛ᵣ ([ @r_concat3_1 typ Δ (↓⁻ Φ1 +▶ Γ1) (@dom S x0 m) ⊛ᵣ r_concat_l, @r_concat3_1 typ Δ (↓⁻ Φ1 +▶ Γ1) (@dom S x0 m) ⊛ᵣ (r_concat_r ⊛ᵣ r_concat_l)])).
       apply s_ren_proper; auto.
       symmetry; apply s_eq_cover_uniq.    
       change (r_cover_l cover_cat) with (@r_concat_l typ Δ ↓⁻ Φ1).
       rewrite <- s_ren_comp, s_eq_cat_l; reflexivity.
       change (r_cover_r cover_cat) with (@r_concat_r typ Δ ↓⁻ Φ1).
       rewrite <- s_ren_comp, s_eq_cat_r; reflexivity.

       unfold r_concat3_1.
       rewrite s_eq_cat_l.
       rewrite s_ren_comp.
       rewrite s_eq_cat_r. *)

       refine (GNext _).
       specialize (IHΓ a1 a x0 m ([ v_var ⊛ᵣ r_concat_l , [ concat0 a1 , a2 ] ] ⊛ γ) j).
       unfold m_strat_resp in IHΓ; cbn [fst snd projT1 projT2] in IHΓ.
       rewrite app_simpl in IHΓ.
       Check (app ((((v_var ⊛ᵣ r_concat3_1) ⊛ᵣ r_concat3_1) ⊛ concat0 a) x0 j) m
              ((v_var ⊛ᵣ r_concat_r) ⊛ᵣ r_concat_r)).
       
       Check (concat0 a x0 j).
       rewrite app_simpl.
       Check (app (concat0 a x0 j) m).
       Check (concat0 a x0 j).
       rewrite app_simpl.
       
       rewrite app_ren in IHΓ.
       unshelve erewrite (app_proper _ _ _) in IHΓ.
       rewrite e_comp_ren_r, v_sub_var, s_eq_cat_r; reflexivity.
       unshelve eassert (H : [r_concat3_1 ᵣ⊛ concat0 a, v_var ⊛ᵣ (r_concat_r ⊛ᵣ r_concat_r)] ⊛ᵥ v_var x0 (r_concat_l x0 j) = _); [ shelve | shelve | | rewrite H in IHΓ; clear H ].
       change (?u ⊛ᵥ v_var x0 (r_concat_l x0 j))
         with ((u ⊛ (v_var ⊛ᵣ r_concat_l)) x0 j).
       rewrite e_comp_ren_r.
       etransitivity; [ apply s_ren_proper; [ apply v_sub_var | reflexivity ] | ].
       rewrite s_eq_cat_l.
       reflexivity.

       unshelve eapply (ev_guarded_cong _ _ IHΓ).

       unfold compo_body.
       cbn [fst snd projT1 projT2].
       unfold m_strat_play.
       cbn [fst snd projT1 projT2].
       
       eassert (H2 : _) by exact (eval_app_simpl ((r_concat3_1 ᵣ⊛ concat0 a) x0 j) m (v_var ⊛ᵣ (r_concat_r ⊛ᵣ r_concat_r))).
       etransitivity.
       unshelve eapply (@subst_eq _ _ _ _ (eqᵢ _) (eqᵢ _)).
       refine (fun (i : T1) (r : msg' Δ + h_actv ogs_hg (m_strat_pas Δ) (Φ1 ▶ dom S m)) =>
     match r with
     | inl r0 => _
     | inr e => _
     end).
       shelve. shelve. shelve.
       all: cycle 1.

       eapply (@fmap_eq _ _ _ (eqᵢ _) _ (eqᵢ _)); cycle 1.
       exact H2.
       intros [] ? ? ->; reflexivity.
       all: cycle 1.
       intros [] ? ? ->. destruct y. reflexivity. reflexivity.
       
       intros ? ? ? ->.
       apply it_eq
       setoid_rewrite H2.
       apply it_eq_step in H2; cbn -[eval_sub] in H2; unfold observe in H2.
       pose (ot1 := _observe (eval (app ((r_concat3_1 ᵣ⊛ concat0 a) x0 j) m (v_var ⊛ᵣ (r_concat_r ⊛ᵣ r_concat_r))))); change (_observe (eval (app _ _ _))) with ot1 in H2 |- *.
       pose (ot2 :=
         (_observe
            (eval_sub (app (r_concat_l ᵣ⊛ᵥ (r_concat3_1 ᵣ⊛ concat0 a) x0 j) m (v_var ⊛ᵣ r_concat_r))
               (v_var ⊛ᵣ (r_concat_r ⊛ᵣ r_concat_r))))).
       change (_observe (eval_sub _ _)) with ot2 in H2.
       dependent elimination H2.

       dependent elimination ot; cbn.
       
       destruct H
       dependent elimination H2.
       pose ()

       apply it_eq_unstep; cbn -[cat_split].
       cbn.

       rewrite v_sub_var.


       ; [ shelve | shelve | ].

       rewrite 
       
       Check ((app (concat0 a x0 j) m ([ v_var ⊛ᵣ r_concat_l , [ v_var ⊛ᵣ r_concat_r , [ v_var ⊛ᵣ r_concat_l , concat0 a ] ⊛ a2 ] ] ⊛ γ))).
       Check (concat0 a).

↓⁺ Φ1 ⇒ᵥ (Δ +▶ ↓⁻ Φ1)
       Check (@r_concat3_1 _ Δ (↓⁻ Φ1) Γ1).
(Δ +▶ (↓⁻ Φ1 +▶ Γ1)) ⊆ (Δ +▶ ↓⁻ Φ1)

       Check (IHΓ ())

              (v_var ⊛ᵣ (r_concat_r ⊛ᵣ r_concat_r)), ((a ▶ₑ⁺) ▶ₑ⁻ γ) ▶ₑ⁺,

       
       Print r_concat3_2.

       

       reflexivity
       Check r_concat3_1.
       reflexivity
       unfold s_ren at 2, s_map.
       reflexivity.
       p
       rewrite e_comp_ren_l.
       Check e_comp_ren_l.
       rewrite (e_comp_ren_r (v_var ⊛ᵣ r_concat3_1)).
       rewrite <- e_comp_ren_l.


       Check (app ((r_concat3_1 ᵣ⊛ concat0 u) x0 j) m (v_var ⊛ᵣ (r_concat_r ⊛ᵣ r_concat_r))).

       

       rewrite s_eq_cat_l.



       rewrite s_eq_cat_l.
  rewrite s_eq_cat_l.
  reflexivity.

  change ((r_concat3_1 ᵣ⊛ concat0 v) x0 j) with (@r_concat3_1 typ Δ ↓⁻ (Γ ▶ x) (@dom S x0 m) ᵣ⊛ᵥ concat0 v x0 j).

       apply (G)
       
    ** change (r_concat3_1 x (r_cover_r cover_cat x j0))
         with ((@r_concat3_1 typ Δ ↓⁺ Φ1 (@dom S x m) ⊛ᵣ r_concat_r) x j0) in u.
       remember u as u'; unfold u in Hequ'; clear u.
       rewrite (eq_trans Hequ' (s_eq_cat_r _ _ _ _)).
       unfold s_ren at 1, s_map.
       rewrite cat_split_r.

       unfold m_strat_resp, emb, dom'; cbn [fst snd projT1 projT2]; simp concat0.
       rewrite app_ren.
Set Printing Implicit.
       
       unfold m_strat_resp, emb.
    ** 

    Set Printing Implicit.
    dependent elimination i1; cbn in *.
    ewrite r_rel.
  refine (GNext _).

    


  
  cbn -[cat_split].

  - dependent elimination j.
  - 
  destru

  
  revert c u v; induction Γ; intros c u v.
  - unfold ev_guarded; cbn -[cat_split].
    pose (ev := _observe (eval c)); change (_observe (eval c)) with ev.
    destruct ev; try now repeat econstructor.
    destruct r as [ [ ? [ i m ] ] γ].
    cbn [fst snd projT1 projT2].
    unfold cat_split. cbn [cover_cat].
    pose (s := cover_split cover_nil_r i).
    change (cover_split cover_nil_r i) with s.
    destruct s ; [ | inversion j ].
    repeat econstructor.
  - (* advance one step of composition *)
    unfold ev_guarded.
    cbn -[cat_split].
    pose (ot := _observe (eval c)); change (_observe (eval c)) with ot.
    destruct ot; try now repeat econstructor. (* some work done, hence guarded *)
    pose (s := cat_split (fst (projT2 (projT1 r)))).
    change (cat_split _) with s.
    destruct s; try now repeat econstructor. (* final channel, hence guarded *)

    refine (GNext _). (* we're not guarded here, but after one more step *)

    dependent elimination u; dependent elimination v.
    destruct r as [ [ x [ i m ] ] γ ].
    unfold m_strat_resp, emb, dom' in *; cbn [fst snd projT1 projT2] in *; simp concat0.

    (* start: cleanup *)

    rewrite app_ren.

    unshelve erewrite (app_proper _ _ _); [ shelve | | ].
    rewrite e_comp_ren_r.
    rewrite v_sub_var.
    rewrite s_eq_cat_r.
    reflexivity.

    eassert (H : ([r_concat3_1 ᵣ⊛ ([concat0 a1, a2]), v_var ⊛ᵣ (r_concat_r ⊛ᵣ r_concat_r)]
               ⊛ᵥ v_var x (r_concat_l x j)) = _); [ | rewrite H; clear H ].
    change (?u ⊛ᵥ v_var x (r_concat_l x j)) with ((u ⊛ (v_var ⊛ᵣ r_concat_l)) x j).
    rewrite e_comp_ren_r.
    etransitivity.
    apply s_ren_proper; [ apply v_sub_var | auto ].
    rewrite s_eq_cat_l.
    reflexivity.

    change ((r_concat3_1 (ϒ:=?a) ᵣ⊛ ([concat0 a1, a2])) x j)
      with (r_concat3_1 (ϒ:=a) ᵣ⊛ᵥ ([concat0 a1, a2]) x j).

    (* end: cleanup *)

    (* wip here *)

    cbn -[cat_split].

    pose (u := @r_concat3_1 typ Δ ↓⁺ Φ1 (@dom S x m) ᵣ⊛ᵥ ([@concat0 Δ Ⓟ Φ1 a1, a2]) x j).
    change (r_concat3_1 ᵣ⊛ᵥ _) with u.
    destruct (is_var_dec u); cycle 1.

    * eassert (H : _) by exact (eval_app_not_var _ _ _ m (v_var ⊛ᵣ (r_concat_r ⊛ᵣ r_concat_r)) f).
      unfold is_tau in H.
      remember (_observe (eval (app u m (v_var ⊛ᵣ (r_concat_r ⊛ᵣ r_concat_r))))) as ot; clear Heqot.
      dependent elimination H.
      repeat econstructor.

    * eassert (H : _) by exact (eval_app_var _ _ _ m (v_var ⊛ᵣ (r_concat_r ⊛ᵣ r_concat_r)) i0).
      apply it_eq_step in H; cbn in H; unfold observe in H.
      remember (_observe (eval (app u m (v_var ⊛ᵣ (r_concat_r ⊛ᵣ r_concat_r))))) as ot.
      dependent elimination H.
      rewrite r_rel; clear r1 Heqot r_rel; cbn.

      eassert (i1 : _) by exact (is_var_ren _ _ i0).
      rewrite (is_var_irr i0 (ren_is_var _ _ i1)); clear i0.

      pose (uu := is_var_get (ren_is_var (([concat0 a1, a2]) x j) (@r_concat3_1 typ Δ ↓⁺ Φ1 (@dom S x m)) i1)).
      change (is_var_get _) with uu.
      eassert (H : _) by exact (ren_is_var_get (([concat0 a1, a2]) x j) (@r_concat3_1 typ Δ ↓⁺ Φ1 (@dom S x m)) i1).
      change (is_var_get _) with uu in H at 1.
      rewrite H; clear uu H u.
      dependent elimination i1; cbn in *.

      pose (u := (@r_concat3_1 typ Δ ↓⁺ Φ1 (@dom S x m) x x0)).
      change (r_concat3_1 x x0) with u.
      

      destruct (cat_split x0).
      ** change (r_concat3_1 x (r_cover_l cover_cat x i0))
           with ((@r_concat3_1 typ Δ ↓⁺ Φ1 (@dom S x m) ⊛ᵣ r_concat_l) x i0) in u.
         remember u as u'. unfold u in Hequ'; clear u.
         apply (fun p => eq_trans p (s_eq_cat_l _ _ _ _)) in Hequ'.
         rewrite Hequ'.
         rewrite cat_split_l.
         repeat econstructor. (* final channel *)
      ** change (r_concat3_1 x (r_cover_r cover_cat x j0))
           with ((@r_concat3_1 typ Δ ↓⁺ Φ1 (@dom S x m) ⊛ᵣ r_concat_r) x j0) in u.
         remember u as u'; unfold u in Hequ'; clear u.
         rewrite (eq_trans Hequ' (s_eq_cat_r _ _ _ _)).
         unfold s_ren at 1, s_map.
         rewrite cat_split_r.

         unfold m_strat_resp, emb, dom'; cbn [fst snd projT1 projT2]; simp concat0.
         rewrite app_ren.
         
         unfold m_strat_resp, emb.

         refine (GNext _).
         fold ev_guarded.
         cbn -[cat_split].
         cbn.

         repeat econstructor
      ** 

         rewrite s_eq_cat_l in Hequ'.
            


      
      unfold r_concat3_1.

      destruct (cat_split x0).
      ** 


      unfold 
      change

      rewrite (ren_is_var_get (([concat0 a1, a2]) x j) (@r_concat3_1 typ Δ ↓⁺ Φ1 (@dom S x m)) i1).
      About ren_is_var_get.
      apply (ren_is_var _ r_concat3_1) in i1.


    rewrite 

    destruct (is_var_dec ((r_concat3_1 ᵣ⊛ ([concat0 a1, a2])) x j)).
    
    assert (H :
       compo_body
          (Φ1,'
           (app (([concat0 a1, a2]) x j) m (([v_var ⊛ᵣ r_concat_l, [concat0 a1, a2]]) ⊛ γ),
             a1,
             a))
     ≊ compo_body
          ((Φ1 ▶ Γ1 ▶ dom S m),'
           (app ((r_concat3_1 ᵣ⊛ ([concat0 a1, a2])) x j) m (v_var ⊛ᵣ (r_concat_r ⊛ᵣ r_concat_r)),
             (a1 ▶ₑ⁻ a2) ▶ₑ⁺,
             (a ▶ₑ⁺) ▶ₑ⁻ γ))
    ); [ | apply (ev_guarded_cong _ H); apply IHΓ ] .

    (* does this hold? *)

  Admitted.

  Definition compo {Δ a} (u : m_strat_act Δ a) (v : m_strat_pas Δ a)
    : delay (msg' Δ) :=
    iter_ev_guarded _ compo_body_guarded T1_0 (a ,' (u , v)).
  Notation "u ∥ v" := (compo u v) (at level 40).

  (* guilhem: rename? *)
  Definition barb {Γ} Δ (x y : conf Γ) : Prop :=
    forall e : Γ ⇒ᵥ Δ, (inj_init_act x ∥ inj_init_pas e) ≈ (inj_init_act y ∥ inj_init_pas e).

  Equations reduce {Δ} : (fun (_ : T1) => reduce_t Δ) ⇒ᵢ itree ∅ₑ (fun _ => msg' Δ) :=
    reduce T1_0 u := eval_in_env
                       ([ v_var , concat1 (snd (fst (projT2 u))) (snd (projT2 u)) ])
                       (fst (fst (projT2 u))) .

  Lemma quatre_trois_pre {Δ} (x : reduce_t Δ)
    :
        (compo_body x >>= fun _ r => match r with
                                     | inl x' => reduce _ x'
                                     | inr y => Ret' (y : (fun _ => msg' _) _)
                                     end)
        ≊
      (eval (fst (fst (projT2 x))) >>=
                      fun _ u =>
                        match cat_split (fst (projT2 (projT1 u))) with
                            | CLeftV h => Ret' (_ ,' (h, snd (projT2 (projT1 u))))
                            | CRightV h => reduce _ (_ ,'
                                                    (m_strat_resp (snd (projT2 x)) (_ ,' (h, snd (projT2 (projT1 u)))), EConF (snd (fst (projT2 x))) (projT2 u)))
                            end).
    etransitivity.
    unfold compo_body; apply bind_bind_com.
    etransitivity.
    unfold m_strat_play. apply fmap_bind_com.
    remember (eval (fst (fst (projT2 x)))) as t eqn:H; clear H; revert t.
    unfold it_eq; coinduction R CIH; intros t.
    cbn; destruct (t.(_observe)).
    + destruct r as [[? [i m]] γ]; cbn.
      destruct (cat_split i).
      econstructor; reflexivity.
      cbn -[eval_in_env] .
      change (it_eqF _ _ _ _ (_observe ?a) (_observe ?b))
        with (it_eq_map  ∅ₑ (eqᵢ _) (it_eq_t _ (eqᵢ _) R) T1_0 a b).
      reflexivity.
    + econstructor; apply CIH.
    + destruct q.
  Qed.

  Lemma quatre_trois {Δ a} (c : m_strat_act Δ a) (e : m_strat_pas Δ a)
    : reduce _ (_ ,' (c , e)) ≊ (c ∥ e) .
    apply iter_evg_uniq.
    clear a c e; intros [] [ ? [ u v ] ].
    etransitivity; cycle 1.
    symmetry.
    apply quatre_trois_pre.
    unfold reduce at 1.
    etransitivity.
    apply fmap_eq, eval_hyp.
    etransitivity.
    apply bind_fmap_com.
    unfold it_eq; cbn [fst snd projT2 projT1].
    apply (tt_t (it_eq_map ∅ₑ (eqᵢ _))).
    refine (@it_eq_up2bind_t _ ∅ₑ (fun _ => {m : msg' (Δ +▶ join_even x) & dom' m ⇒ᵥ (Δ +▶ _)}) _ _ _ (eqᵢ _) _ _ _ (eval (fst u) >>= _) (eval (fst u) >>= _) _).
    econstructor; eauto.
    intros [] [m γ] ? <-.
    apply (bt_t (it_eq_map ∅ₑ (eqᵢ (fun _ : T1 => msg' Δ)))).
    cbn [fst snd projT2 projT1].
    destruct (cat_split (fst (projT2 m))).
    - cbn; econstructor. reflexivity.
    - cbn -[it_eq_map fmap].
      change (it_eq_t ∅ₑ (eqᵢ (fun _ : T1 => msg' Δ)) bot) with (it_eq (E:=∅ₑ) (eqᵢ (fun _ : T1 => msg' Δ))).
      apply it_eq_step.
      apply fmap_eq.
      rewrite c_sub_sub.
      unshelve rewrite c_sub_proper; try reflexivity.
      apply s_eq_cover_uniq.
      * rewrite <- (proj2 (concat_fixpoint (snd u) v)).
        rewrite <- e_comp_ren_r.
        rewrite s_eq_cat_l.
        rewrite <- e_comp_ren_l.
        apply e_comp_proper; try reflexivity.
        apply s_eq_cover_uniq.
        + unfold r_concat3_1.
          now rewrite <- s_ren_comp, 2 s_eq_cat_l.
        + unfold r_concat3_1.
          rewrite <- s_ren_comp, s_eq_cat_r.
          cbn; now rewrite s_ren_comp, s_eq_cat_r, s_eq_cat_l.
      * rewrite <- e_comp_ren_r.
        rewrite s_eq_cat_r, e_comp_ren_r, v_sub_var.
        now rewrite s_ren_comp, 2 s_eq_cat_r .
   Qed.

  Lemma quatre_trois_app {Γ Δ}
    (c : conf Γ) (e : Γ ⇒ᵥ Δ)
    : eval_in_env e c ≊ (inj_init_act c ∥ inj_init_pas e).
    rewrite <- quatre_trois.
    unfold reduce, inj_init_act, eval_in_env; cbn [fst snd projT1 projT2]; apply fmap_eq.
    cbv [inj_init_pas]; rewrite concat1_equation_2, 2 concat1_equation_1.
    unfold c_ren; rewrite c_sub_sub, c_sub_proper ; try reflexivity.
    rewrite s_eq_cover_empty_r.
    rewrite e_comp_ren_r, v_sub_var.
    rewrite s_ren_comp, 2 s_eq_cat_r.
    unfold e_ren, r_concat_l, cover_cat; cbn; rewrite r_cover_l_nil, s_ren_id.
    now rewrite 2 v_var_sub.
  Qed.

  Theorem barb_correction {Γ} Δ (x y : conf Γ)
          : barb Δ x y -> ciu Δ x y.
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
        induction r2; [ now rewrite H | auto ].
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

  Definition reduce_t_inj {Δ : context} (x : reduce_t Δ) : compo_alt_t Δ :=
     (_ ,' (m_strat _ (fst (projT2 x)) , m_stratp _ (snd (projT2 x)))) .
  
  Lemma compo_compo_alt {Δ} {x : reduce_t Δ} :
    iter_delay compo_alt_body (reduce_t_inj x) ≊ iter_delay compo_body x .
    unshelve eapply (iter_cong_strong).
    - refine (fun _ a b => compo_t_eq_strong _ a (reduce_t_inj b)).
    - intros [] [? [u1 e1]] [? [u2 e2]] [A B].
      dependent elimination A; cbn in B; destruct B as [H1 H2].
      rewrite unfold_mstrat in H1.
      unfold compo_body.
      cbn [fst snd projT1 projT2].
      remember (m_strat_play u2) eqn:Hu; clear Hu.
      clear u2.
      unfold it_eq.
      revert u1 d H1.
      coinduction R CIH.
      intros u1 d H1.
      apply it_eq_step in H1.
      cbn in *; unfold observe in *.
      destruct (_observe d).
      + destruct r as [|[]]; destruct (_observe u1); dependent elimination H1;
          econstructor; econstructor; eauto.
        exists eq_refl; split; [ exact (H2 q0) | exact k_rel ].
      + destruct (_observe u1); dependent elimination H1; eauto.
      + destruct q.
    - cbn; destruct (reduce_t_inj x) as [ ? [] ].
      exists eq_refl; split; cbn. reflexivity. intro r. reflexivity.
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

Print Assumptions ogs_correction.
