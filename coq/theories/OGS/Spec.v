From Coinduction Require Import coinduction tactics.

From OGS Require Import Prelude.
From OGS.Utils Require Import Ctx Rel.
From OGS.Game Require Import HalfGame Event.
From OGS.ITree Require Import ITree Eq Delay Structure Properties Guarded.

Set Equations Transparent.

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
    emb {Γ} (m : msg' Γ) : conf (Γ +▶ dom' m) ;
    v_var {Γ} : Γ =[val]> Γ ; (*  Γ ∋ x -> val Γ x   *)
    v_sub {Γ Δ} : Γ =[val]> Δ -> val Γ ⇒ᵢ val Δ ;
    c_sub {Γ Δ} : Γ =[val]> Δ -> conf Γ -> conf Δ ;
    }.

  Notation "u ⊛ᵥ v" := (v_sub u _ v) (at level 30).
  Notation "u ⊛ₜ c" := (c_sub u c) (at level 30).
  Notation "Γ ⇒ᵥ Δ" := (Γ =[val]> Δ) (at level 30).

  Context {M : machine}.

(*|
Renaming in values, a particular case of value substitution.
|*)
  Definition v_ren {Γ Δ} : Γ ⊆ Δ -> val Γ ⇒ᵢ val Δ :=
    fun u => v_sub (v_var ⊛ᵣ u) .

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

  Require Import Coq.Logic.Decidable.

  Variant is_var {Γ x} : val Γ x -> Type :=
    | IsVar (i : Γ ∋ x) : is_var (v_var x i)
  .  
  
  Hypothesis check_var : forall Γ x (v : val Γ x), is_var v + (is_var v -> False).


  (* m = (i , p)
     case e i
       
   *)
  Hypothesis eval_emb_tau : forall Γ Δ (m : msg' Γ) (e : Γ ⇒ᵥ Δ),
       eval ([ r_concat_l ᵣ⊛ e , v_var ⊛ᵣ r_concat_r ] ⊛ₜ emb m)
     ≊ go match check_var Δ (projT1 m) (e (projT1 m) (fst (projT2 m))) with
          | inl a =>
              let '(IsVar i) := a in
              RetF ((_ ,' (r_concat_l _ i , snd (projT2 m))) ,' v_var ⊛ᵣ r_concat_r )
          | inr _ =>
              TauF (eat_one_tau (eval ([r_concat_l ᵣ⊛ e, v_var ⊛ᵣ r_concat_r] ⊛ₜ emb m)))
          end.

(*|
Renaming in configurations
|*)
  Definition c_ren {Γ1 Γ2} : Γ1 ⊆ Γ2 -> conf Γ1 -> conf Γ2
    := fun u c => (v_var ⊛ᵣ u) ⊛ₜ c .
  Infix "ᵣ⊛ₜ" := c_ren (at level 14).

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
  }.

  Context {MH : machine_law}.

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
  Proof.
    intros ? ? H1 ? ? H2; unfold e_ren.
    apply e_comp_proper; eauto; now rewrite H1.
  Qed.

  Lemma e_comp_ren_r {Γ1 Γ2 Γ3 Γ4} (u : Γ3 ⇒ᵥ Γ4) (v : Γ2 ⇒ᵥ Γ3) (w : Γ1 ⊆ Γ2)
        : u ⊛ (v ⊛ᵣ w) ≡ₐ (u ⊛ v) ⊛ᵣ w .
  Proof. reflexivity. Qed.

  Lemma e_comp_ren_l {Γ1 Γ2 Γ3 Γ4} (u : Γ3 ⇒ᵥ Γ4) (v : Γ2 ⊆ Γ3) (w : Γ1 ⇒ᵥ Γ2)
        : (u ⊛ᵣ v) ⊛ w ≡ₐ u ⊛ (v ᵣ⊛ w) .
  Proof. unfold e_ren; now rewrite v_sub_sub, e_comp_ren_r, v_sub_var. Qed.

(*|
Evaluate a configuration inside an environment (assignment), returning only the message part (the "positive" or "static" part).
|*)
  Definition eval_in_env {Γ Δ} (e : Γ ⇒ᵥ Δ) (t : conf Γ) : delay (msg' Δ)
    := fmap (fun _ => @projT1 _ _) _ (eval (e ⊛ₜ t)).

  #[global]
  Instance eval_in_env_proper {Γ Δ}
             : Proper (ass_eq Γ Δ ==> eq ==> eq) (@eval_in_env Γ Δ).
  Proof.
    intros ? ? H1 ? ? H2.
    unfold eval_in_env.
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
  Proof.
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

  Definition m_strat_play {Δ Φ} (x : m_strat_act Δ Φ)
    : delay (msg' Δ + h_actv ogs_hg (m_strat_pas Δ) Φ)%type :=
    eval (fst x) >>=
      fun _ u =>
        match cat_split (fst (projT2 (projT1 u))) with
        | CLeftV h => Ret' (inl (_ ,' (h , snd (projT2 (projT1 u)))))
        | CRightV h => Ret' (inr ((_ ,' (h , snd (projT2 (projT1 u))))
                            ,' (snd x ▶ₑ⁻ projT2 u)))
        end .
  Print r_concat3_1.

  Definition m_strat_resp {Δ Φ} (x : m_strat_pas Δ Φ)
    : h_pasv ogs_hg (m_strat_act Δ) Φ
    := fun m =>
         ([ (r_concat3_1 ᵣ⊛ concat0 x) , v_var ⊛ᵣ (r_concat_r ⊛ᵣ r_concat_r) ] ⊛ₜ emb m ,
          x ▶ₑ⁺).

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
  Proof.
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

  Definition compo_t (Δ : context) : Type :=
    ⦉ ogs_act Δ ×ᵢ ogs_pas Δ ⦊ᵢ .

  Definition compo_t_eq (Δ : context) : relation (compo_t Δ) .
    intros [a1 [u1 u2]] [a2 [v1 v2]].
    refine (exists (p : a1 = a2), _).
    rewrite p in *.
    refine (u1 ≈ v1 /\ h_pasvR ogs_hg (it_wbisim (eqᵢ _)) _ u2 v2).
  Defined.

  Definition compo_t_eq_strong (Δ : context) : relation (compo_t Δ) .
    intros [a1 [u1 u2]] [a2 [v1 v2]].
    refine (exists (p : a1 = a2), _).
    rewrite p in *.
    refine (u1 ≊ v1 /\ h_pasvR ogs_hg (it_eq (eqᵢ _)) _ u2 v2).
  Defined.

  Equations compo0_body {Δ}
            : (fun (_ : T1) => compo_t Δ) ⇒ᵢ itree ∅ₑ (fun _ => compo_t Δ + msg' Δ)%type :=
    compo0_body :=
      cofix _compo_body T1_0 u :=
        go (match (fst (projT2 u)).(_observe) with
            | RetF r => RetF (inr r)
            | TauF t => TauF (_compo_body T1_0 (_ ,' (t , (snd (projT2 u)))))
            | VisF e k => RetF (inl (_ ,' (snd (projT2 u) e , k)))
            end) .

  Definition compo0 {Δ a} (u : ogs_act Δ a) (v : ogs_pas Δ a) : delay (msg' Δ)
    := iter compo0_body T1_0 (a ,' (u , v)).

  #[global] Instance compo0_proper {Δ a}
    : Proper
        (it_wbisim (eqᵢ _) a ==> h_pasvR ogs_hg (it_wbisim (eqᵢ _)) a ==> it_wbisim (eqᵢ _) T1_0)%signature
        (@compo0 Δ a).
  Proof.
    intros ? ? H1 ? ? H2. unfold compo0.
    unshelve eapply (@iter_weq _ _ _ _ (fun _ => compo_t_eq Δ) (eqᵢ _) compo0_body compo0_body _ T1_0 (a ,' (x , x0)) (a ,' (y , y0)) (ex_intro _ eq_refl (conj H1 H2))).
    clear a x y H1 x0 y0 H2.
    unfold dpointwise_relation, respectful.
    intros [] [? []] [? []] []; destruct x1; cbn in H; destruct H.
    unfold it_wbisim.
    revert o o1 H.
    coinduction R CIH.
    intros o o1 H.
    cbn.
    apply it_wbisim_step in H.
    cbn in H; unfold observe in H.
    destruct H.
    dependent destruction rr.
    - unshelve econstructor.
      * exact (RetF (inr r0)).
      * exact (RetF (inr r3)).
      * remember (_observe o) eqn:H; clear H.
        remember (@RetF alt_ext ogs_e (fun _ => msg' Δ) (ogs_act Δ) x r0).
        apply (fun u => rew <- [ fun v => it_eat _ _ v ] Heqi0 in u) in r1.
        induction r1; [ now rewrite Heqi0 | eauto ].
      * remember (_observe o1) eqn:H; clear H.
        remember (@RetF alt_ext ogs_e (fun _ => msg' Δ) (ogs_act Δ) x r3).
        apply (fun u => rew <- [ fun v => it_eat _ _ v ] Heqi0 in u) in r2.
        induction r2; [ now rewrite Heqi0 | eauto ].
      * now repeat econstructor.
    - unshelve econstructor.
      * exact (TauF (compo0_body T1_0 (x ,' (t1 , o0)))).
      * exact (TauF (compo0_body T1_0 (x ,' (t2 , o2)))).
      * remember (_observe o) eqn:H; clear H.
        remember (TauF t1) eqn:H.
        induction r1; [ now rewrite H | eauto ].
      * remember (_observe o1) eqn:H; clear H.
        remember (TauF t2) eqn:H.
        induction r2; [ now rewrite H | eauto ].
      * eauto.
    - unshelve econstructor.
      * exact (RetF (inl (_ ,' (o0 q , k1)))).
      * exact (RetF (inl (_ ,' (o2 q , k2)))).
      * remember (_observe o) eqn:H; clear H.
        remember (VisF q k1) eqn:H.
        induction r1; [ now rewrite H | eauto ].
      * remember (_observe o1) eqn:H; clear H.
        remember (VisF q k2) eqn:H.
        induction r2; [ now rewrite H | eauto ].
      * econstructor. econstructor. unshelve econstructor. reflexivity.
        econstructor.
        exact (H0 q).
        exact k_rel.
   Qed.

  Definition reduce_t (Δ : context) : Type :=
    ⦉ m_strat_act Δ ×ᵢ m_strat_pas Δ ⦊ᵢ .

  Definition reduce_t_inj {Δ : context} : reduce_t Δ -> compo_t Δ.
  intros [ ? [ a b ]]. refine (x ,' (m_strat _ a , m_stratp _ b)).
  Defined.

  Equations compo_body {Δ}
    : (fun (_ : T1) => reduce_t Δ) ⇒ᵢ itree ∅ₑ (fun _ => reduce_t Δ + msg' Δ)%type :=
  compo_body T1_0 x := m_strat_play (fst (projT2 x)) >>= fun _ r =>
          go (match r with
              | inl r => RetF (inr r)
              | inr e => RetF (inl (_ ,' (m_strat_resp (snd (projT2 x)) (projT1 e) , (projT2 e))))
              end).

  Definition compo_body_guarded {Δ} : eqn_ev_guarded (@compo_body Δ).
  intros [] [ Γ [ u v ] ].
  induction Γ.
  - unfold ev_guarded; cbn -[cat_split].
    pose (ev := _observe (eval (fst u))); change (_observe (eval (fst u))) with ev.
    destruct ev; try now repeat econstructor.
    destruct r as [ [ ? [ i m ] ] γ].
    cbn [fst snd projT1 projT2].
    unfold cat_split. cbn [cover_cat].
    pose (s := cover_split cover_nil_r i).
    change (cover_split cover_nil_r i) with s.
    destruct s ; [ | inversion j ].
    repeat econstructor.
  - unfold ev_guarded; cbn -[cat_split].
    pose (ev := _observe (eval (fst u))); change (_observe (eval (fst u))) with ev.
    destruct ev; try now repeat econstructor.
    destruct r as [ [ ? [ i m ] ] γ].
    unfold dom' in γ; cbn [fst snd projT1 projT2] in *.
    pose (s := cat_split i); change (cat_split i) with s.
    destruct s; cbn; [ repeat econstructor | ].
  Admitted.

  Definition compo {Δ a} (u : m_strat_act Δ a) (v : m_strat_pas Δ a) : delay (msg' Δ)
    := iter compo_body T1_0 (a ,' (u , v)).
  Notation "u ∥ v" := (compo u v) (at level 40).

  Lemma compo_compo0 {Δ} {x : reduce_t Δ} : iter compo0_body T1_0 (reduce_t_inj x) ≊ iter compo_body T1_0 x .
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
      (*
      unfold m_strat in H1.
      rewrite iter_unfold in H1.
      fold (@m_strat Δ) in H1.
      unfold m_strat_body in H1.
      apply it_eq_step in H1.
      unfold compo_body.
      cbn -[bind] in H1; unfold observe in H1.
      cbn [fst snd projT1 projT2].
      unfold m_strat in H1.
*)
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
  (* guilhem: rename? *)
  Definition barb {Γ} Δ (x y : conf Γ) : Prop :=
    forall e : Γ ⇒ᵥ Δ, (inj_init_act x ∥ inj_init_pas e) ≈ (inj_init_act y ∥ inj_init_pas e).

  (*
  Definition reduce_t_eq (Δ : context) : relation (reduce_t Δ) :=
    fun u v => compo_t_eq Δ (reduce_t_inj _ u) (reduce_t_inj _ v).
*)

  Equations reduce {Δ} : (fun (_ : T1) => reduce_t Δ) ⇒ᵢ itree ∅ₑ (fun _ => msg' Δ) :=
    reduce T1_0 u := eval_in_env
                       ([ v_var , concat1 (snd (fst (projT2 u))) (snd (projT2 u)) ])
                       (fst (fst (projT2 u))) .

  Lemma quatre_trois_pre {Δ} (x : reduce_t Δ)
    :
        (compo_body T1_0 x >>= fun _ r => go (match r with
                                     | inl x' => TauF (reduce _ x')
                                     | inr y => RetF (y : (fun _ => msg' _) _)
                                     end))
        ≊
      (eval (fst (fst (projT2 x))) >>=
                      fun _ u =>
                        go (match cat_split (fst (projT2 (projT1 u))) with
                            | CLeftV h => RetF (_ ,' (h, snd (projT2 (projT1 u))))
                            | CRightV h => TauF (reduce _ (_ ,'
                                                    (m_strat_resp (snd (projT2 x)) (_ ,' (h, snd (projT2 (projT1 u)))), EConF (snd (fst (projT2 x))) (projT2 u))))
                            end)).
  Proof.
    etransitivity.
    unfold compo_body; apply bind_bind_com.
    etransitivity.
    unfold m_strat_play; apply bind_bind_com.
    remember (eval (fst (fst (projT2 x)))) as t eqn:H; clear H; revert t.
    unfold it_eq; coinduction R CIH; intros t.
    cbn; destruct (t.(_observe)).
    + destruct r as [[? [i m]] γ]; cbn.
      destruct (cat_split i).
      econstructor; reflexivity.
      econstructor; reflexivity.
    + econstructor. apply CIH.
    + destruct q.
  Qed.

  Definition eval_sub_1 {Γ Δ} (c : conf (Δ +▶ Γ)) (e : Γ ⇒ᵥ Δ)
             : delay { m : msg' Δ & dom' m ⇒ᵥ Δ } :=
        eval ([ v_var , e ] ⊛ₜ c) .

  Definition eval_sub_2 {Γ Δ} (c : conf (Δ +▶ Γ)) (e : Γ ⇒ᵥ Δ)
             : delay { m : msg' Δ & dom' m ⇒ᵥ Δ }.
    refine (eval c >>= fun 'T1_0 x =>
               go (match cat_split (fst (projT2 (projT1 x))) with
                   | CLeftV h => RetF ((_ ,' (h , snd (projT2 (projT1 x)))) ,'
                                   [ v_var,  e ] ⊛ (projT2 x))
                   | CRightV h => TauF _
                   end)) .
    refine (eval ([ e , ([v_var , e ] ⊛ projT2 x) ] ⊛ₜ (emb (_ ,' (h , (snd (projT2 (projT1 x)))))))).
  Defined.

  Hypothesis eval_hyp : forall {Γ Δ}
                          (c : conf (Δ +▶ Γ))
                          (e : Γ ⇒ᵥ Δ),
                          eval_sub_1 c e ≊ eval_sub_2 c e .

  Lemma quatre_trois {Δ a} (c : m_strat_act Δ a) (e : m_strat_pas Δ a)
    : reduce _ (_ ,' (c , e)) ≊ (c ∥ e) .
    refine (iter_uniq compo_body reduce _ _ (_ ,' (c , e))).
    clear a c e; intros [] [ ? [ u v ] ].
    etransitivity; cycle 1.
    symmetry; apply quatre_trois_pre.
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
    - cbn; econstructor.
      unfold reduce.
      fold (@fmap _ ∅ₑ _ _ (fun _ : T1 => projT1 (P:=fun m0 : msg' Δ => dom' m0 ⇒ᵥ Δ)) T1_0).
      change (it_eq_t ∅ₑ (eqᵢ (fun _ : T1 => msg' Δ)) bot T1_0 ?a ?b) with (it_eq (eqᵢ _) a b).
      apply fmap_eq.
      unfold m_strat_resp.
      cbn [fst snd projT1 projT2].
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
  Proof.
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
  Proof.
    intros H e.
    etransitivity; [ apply it_eq_wbisim, (quatre_trois_app x e) | ].
    etransitivity; [ apply (H e) | ].
    symmetry; apply it_eq_wbisim, (quatre_trois_app y e).
  Qed.

  Theorem ogs_correction {Γ} Δ (x y : conf Γ)
    : inj_init_act (Δ:=Δ) x ≈ₐ inj_init_act y -> ciu Δ x y.
    intro H.
    apply barb_correction.
    intro e.
    unfold compo; rewrite <- 2 compo_compo0.
    apply compo0_proper. exact H. intro r; eauto.
  Qed.

End withInteractionSpec.
