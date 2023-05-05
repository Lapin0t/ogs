Require Import Program.Equality.
Import EqNotations.

From Coinduction Require Import coinduction tactics.

From OGS Require Import Utils.
From OGS.Utils Require Import Ctx Rel.
From OGS.Game Require Import HalfGame Event.
From OGS.ITree Require Import ITree Monad Eq Delay.

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
    v_var {Γ} : has Γ ⇒ᵢ val Γ ; (*  Γ ∋ x -> val Γ x   *)
    v_sub {Γ Δ} : Γ =[val]> Δ -> val Γ ⇒ᵢ val Δ ;
    c_sub {Γ Δ} : Γ =[val]> Δ -> conf Γ -> conf Δ ;
    }.

  Notation "u @ᵥ v" := (v_sub u _ v) (at level 30).
  Notation "u @ₜ c" := (c_sub u c) (at level 30).
  Notation "Γ ⇒ᵥ Δ" := (Γ =[val]> Δ) (at level 30).

  Context {M: machine}.

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

(*|
Renaming in configurations
|*)
  Definition c_ren {Γ1 Γ2} : Γ1 ⊆ Γ2 -> conf Γ1 -> conf Γ2
    := fun u c => (v_var ⊛ᵣ u) @ₜ c .

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
    v_sub_proper {Γ Δ}
      :> Proper
          (ass_eq Γ Δ ==> forall_relation (fun i => eq ==> eq))
          v_sub ;
    c_sub_proper {Γ Δ}
      :> Proper
          (ass_eq Γ Δ ==> eq ==> eq)
          c_sub ;
    v_sub_var {Γ1 Γ2} (p : Γ1 ⇒ᵥ Γ2) : p ⊛ v_var ≡ₐ p ;
    v_var_sub {Γ1 Γ2} (p : Γ1 ⇒ᵥ Γ2) : v_var ⊛ p ≡ₐ p ;
    v_sub_sub {Γ1 Γ2 Γ3 Γ4} (p : Γ3 ⇒ᵥ Γ4) (q : Γ2 ⇒ᵥ Γ3) (r : Γ1 ⇒ᵥ Γ2)
      : p ⊛ (q ⊛ r) ≡ₐ (p ⊛ q) ⊛ r ;
    c_var_sub {Γ} (c : conf Γ) : v_var @ₜ c = c ;
    c_sub_sub {Γ1 Γ2 Γ3} (u : Γ2 ⇒ᵥ Γ3) (v : Γ1 ⇒ᵥ Γ2) {c}
      : u @ₜ (v @ₜ c) = (u ⊛ v) @ₜ c ;
  }.

  Context {MH : machine_law}.

  #[global] Instance e_comp_proper {Γ1 Γ2 Γ3}
             : Proper (ass_eq Γ2 Γ3 ==> ass_eq Γ1 Γ2 ==> ass_eq Γ1 Γ3) e_comp.
    intros ? ? H1 ? ? H2 ? i.
    unfold e_comp, s_map.
    now rewrite H1, H2.
  Qed.

  #[global] Instance e_ren_proper {Γ1 Γ2 Γ3}
             : Proper (ass_eq Γ2 Γ3 ==> ass_eq Γ1 Γ2 ==> ass_eq Γ1 Γ3) e_ren.
  intros ? ? H1 ? ? H2.
  unfold e_ren. apply e_comp_proper; eauto. now rewrite H1.
  Qed.

  Lemma e_comp_ren_r {Γ1 Γ2 Γ3 Γ4} (u : Γ3 ⇒ᵥ Γ4) (v : Γ2 ⇒ᵥ Γ3) (w : Γ1 ⊆ Γ2)
        : u ⊛ (v ⊛ᵣ w) ≡ₐ (u ⊛ v) ⊛ᵣ w .
    reflexivity.
  Qed.

  Lemma e_comp_ren_l {Γ1 Γ2 Γ3 Γ4} (u : Γ3 ⇒ᵥ Γ4) (v : Γ2 ⊆ Γ3) (w : Γ1 ⇒ᵥ Γ2)
        : (u ⊛ᵣ v) ⊛ w ≡ₐ u ⊛ (v ᵣ⊛ w) .
    unfold e_ren.
    now rewrite v_sub_sub, e_comp_ren_r, v_sub_var.
  Qed.

  Program Definition sub_eval_msg {Γ Δ} (e : Γ ⇒ᵥ Δ) (t : conf Γ)
             : delay (msg' Δ)
    := fmap (fun _ => @projT1 _ _) _ (eval (e @ₜ t)).

  #[global] Instance sub_eval_msg_proper {Γ Δ}
             : Proper (ass_eq Γ Δ ==> pointwise_relation _ eq) (@sub_eval_msg Γ Δ).
  Proof.
    intros ? ? H1 e.
    unfold sub_eval_msg.
    now rewrite H1.
  Qed.

  Definition ciu {Γ} Δ (x y : conf Γ) : Prop :=
    forall e : Γ ⇒ᵥ Δ, sub_eval_msg e x ≈ sub_eval_msg e y.

  (* Section 3: game definition
     ↓+ ~ join_even
   *)
  Definition alt_ext : Type := ctx (context).
  Notation "↓⁺ a" := (join_even a) (at level 9).
  Notation "↓⁻ a" := (join_odd a) (at level 9).
  Notation "↓[ b ] a" := (join_even_odd_aux b a) (at level 9).


  Definition ogs_hg : half_game alt_ext alt_ext := {|
    g_move := fun es => msg' ↓⁺es ;
    g_next := fun es m => (es ▶ dom' m) ;
  |}.

  Definition ogs_g : game alt_ext alt_ext :=
    {| g_client := ogs_hg ;
       g_server := ogs_hg |}.

  Definition ogs_e : event alt_ext alt_ext := e_of_g ogs_g.

  Definition ogs_act (Δ : context) : psh alt_ext := itree ogs_e (fun _ => msg' Δ).
  Definition ogs_pas (Δ : context) : psh alt_ext := h_pasv ogs_hg (ogs_act Δ).

  Notation player   := true.
  Notation opponent := false.
  (* Env* (def 3.12)
     Env M Δ player es : environment part of the player (aka active at es) configuration at (Δ + es)
     Env M Δ opponent es : environment part of the opponent (aka passive at es) configuration at (Δ + es)
   *)
  Inductive alt_env (Δ : context)
    : bool -> alt_ext -> Type :=
  | ENil {b} : alt_env Δ b ∅
  | EConT {a Γ} : alt_env Δ opponent a
                  -> alt_env Δ player (a ▶ Γ)
  | EConF {a Γ} : alt_env Δ player a
                  -> Γ ⇒ᵥ (Δ +▶ ↓⁺a)
                  -> alt_env Δ opponent (a ▶ Γ)
  .
  Arguments ENil {Δ b}.
  Arguments EConT {Δ a Γ}.
  Arguments EConF {Δ a Γ}.

  (* flattens an alternating environment into an unstructured one *)
  Equations concat0 {Δ b a} : alt_env Δ b a -> ↓[negb b] a ⇒ᵥ (Δ +▶ ↓[b] a) :=
    concat0 (ENil) := s_empty ;
    concat0 (EConT u) := r_concat3_1 ᵣ⊛ concat0 u ;
    concat0 (EConF u e) := [ concat0 u , e ] .

  (* Flattens a pair of alternating environments for resp. player and opponent into a "closed" substitution *)
  Equations concat1 {Δ} a b : alt_env Δ b a -> alt_env Δ (negb b) a -> ↓[b] a ⇒ᵥ Δ :=
    concat1 ∅      b _ _ :=
      s_empty ;
    concat1 (a ▶ _) b (EConT u) (EConF v e) :=
      [ concat1 a _ u v , [ v_var , concat1 a _ v u ] ⊛ e ] ;
    concat1 (a ▶ _) b (EConF u e) (EConT v) := concat1 a _ u v .
  Arguments concat1 {Δ a b}.

  Lemma quatre_six {Δ a} (u : alt_env Δ player a) (v : alt_env Δ opponent a)
    :  [ v_var , concat1 u v ] ⊛ concat0 u ≡ₐ concat1 v u
    /\ [ v_var , concat1 v u ] ⊛ concat0 v ≡ₐ concat1 u v .
  Proof.
    induction a; dependent destruction u; dependent destruction v; cbn; split.
    - intros ? i; dependent elimination i.
    - intros ? i; dependent elimination i.
    - rewrite <- e_comp_ren_l.
      rewrite <- (proj2 (IHa v u)).
      apply e_comp_proper; [ | reflexivity ].
      symmetry.
      apply s_eq_cover_uniq.
      * unfold r_concat3_1.
        now rewrite <- s_ren_comp, 2 s_eq_cat_l.
      * unfold r_concat3_1.
        now rewrite <- s_ren_comp, s_eq_cat_r, s_ren_comp, s_eq_cat_r, s_eq_cat_l.
    - symmetry; apply s_eq_cover_uniq.
      * rewrite <- e_comp_ren_r, s_eq_cat_l.
        symmetry; apply IHa.
      * now rewrite <- e_comp_ren_r, s_eq_cat_r.
  Qed.

  Definition m_strat_act Δ : alt_ext -> Type :=
    fun a => (conf (Δ +▶ join_even a) * alt_env Δ player a)%type.

  Definition m_strat_pas Δ : alt_ext -> Type :=
    fun a => alt_env Δ opponent a.

  Definition m_strat_play {Δ a} (x : m_strat_act Δ a)
    : delay (msg' Δ + h_actv ogs_hg (m_strat_pas Δ) a)%type :=
    (eval (fst x)) >>=
      fun _ u =>
        match cover_split cover_cat _ (fst (projT2 (projT1 u))) with
        | inl h => Ret' (inl (_ ,' (h , snd (projT2 (projT1 u)))))
        | inr h => Ret' (inr ((_ ,' (h , snd (projT2 (projT1 u)))) ,' EConF (snd x) (projT2 u)))
        end .

  Definition m_strat_resp {Δ a} (x : m_strat_pas Δ a)
    : h_pasv ogs_hg (m_strat_act Δ) a
    := fun m =>
         ([ (r_concat3_1 ᵣ⊛ concat0 x) , (r_concat_r ⊛ᵣ r_concat_r) ᵣ⊛ v_var ] @ₜ emb m ,
          EConT x).

  Definition m_strat_body {Δ}
    : m_strat_act Δ ⇒ᵢ itree ogs_e (m_strat_act Δ +ᵢ (fun _ => msg' Δ))
    := fun i e =>
         emb_delay (m_strat_play e) >>=
           fun _ '(Fib x) =>
             match x with
             | inl m => Ret' (inr m)
             | inr (m,'c) => Vis' (m : ogs_e.(e_qry) i) (fun r => Ret' (inl (m_strat_resp c r)))
             end.

  Definition m_strat {Δ} : m_strat_act Δ ⇒ᵢ ogs_act Δ :=
    iter m_strat_body.

  Definition m_stratp {Δ} : m_strat_pas Δ ⇒ᵢ ogs_pas Δ :=
    fun _ x m => m_strat _ (m_strat_resp x m).

  Definition m_strat_act_eqv {Δ} : relᵢ (m_strat_act Δ) (m_strat_act Δ) :=
    fun i x y => m_strat i x ≈ m_strat i y.
  Notation "x ≈ₐ y" := (m_strat_act_eqv _ x y) (at level 50).

  Definition m_strat_pas_eqv {Δ} : relᵢ (m_strat_pas Δ) (m_strat_pas Δ) :=
    fun i x y => forall m, m_strat_resp x m ≈ₐ m_strat_resp y m .
  Notation "x ≈ₚ y" := (m_strat_pas_eqv _ x y) (at level 50).

  Definition inj_init_act {Δ Γ} (c : conf Γ) : m_strat_act Δ (∅ ▶ Γ)
    := (c_ren (r_concat_r ⊛ᵣ r_concat_r) c , EConT ENil).

  Definition inj_init_pas {Δ Γ} (γ : Γ ⇒ᵥ Δ) : m_strat_pas Δ (∅ ▶ Γ)
    := EConF ENil (e_ren r_concat_l γ).

  Definition compo_t (Δ : context) : Type :=
    ⦉ ogs_act Δ ×ᵢ ogs_pas Δ ⦊ᵢ .

  Definition compo_t_eq (Δ : context) : relation (compo_t Δ) .
    intros [a1 [u1 u2]] [a2 [v1 v2]].
    refine (exists (p : a1 = a2), _).
    rewrite p in *.
    refine (u1 ≈ v1 /\ h_pasvR ogs_hg (it_wbisim (eqᵢ _)) _ u2 v2).
  Defined.

  Equations compo_body {Δ}
            : (fun (_ : T1) => compo_t Δ) ⇒ᵢ itree ∅ₑ (fun _ => compo_t Δ + msg' Δ)%type :=
    compo_body :=
      cofix _compo_body T1_0 u :=
        go (match (fst (projT2 u)).(_observe) with
            | RetF r => RetF (inr r)
            | TauF t => TauF (_compo_body T1_0 (_ ,' (t , (snd (projT2 u)))))
            | VisF e k => RetF (inl (_ ,' (snd (projT2 u) e , k)))
            end) .

  Definition compo {Δ a} (u : ogs_act Δ a) (v : ogs_pas Δ a) : delay (msg' Δ)
    := iter compo_body T1_0 (a ,' (u , v)).
  Notation "u ∥ v" := (compo u v) (at level 40).

  #[global] Instance compo_proper {Δ a}
    : Proper
        (it_wbisim (eqᵢ _) a ==> h_pasvR ogs_hg (it_wbisim (eqᵢ _)) a ==> it_wbisim (eqᵢ _) T1_0)%signature
        (@compo Δ a).
  Proof.
    intros ? ? H1 ? ? H2. unfold compo.
    unshelve eapply (@iter_weq _ _ _ _ (fun _ => compo_t_eq Δ) (eqᵢ _) compo_body compo_body _ T1_0 (a ,' (x , x0)) (a ,' (y , y0)) (ex_intro _ eq_refl (conj H1 H2))).
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
      * exact (TauF (compo_body T1_0 (x ,' (t1 , o0)))).
      * exact (TauF (compo_body T1_0 (x ,' (t2 , o2)))).
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

  (* guilhem: rename? *)
  Definition barb {Γ} Δ (x y : conf Γ) : Prop :=
    forall e : Γ ⇒ᵥ Δ, (m_strat _ (inj_init_act x) ∥ m_stratp _ (inj_init_pas e)) ≈ (m_strat _ (inj_init_act y) ∥ m_stratp _ (inj_init_pas e)).

  Definition reduce_t (Δ : context) : Type :=
    ⦉ m_strat_act Δ ×ᵢ m_strat_pas Δ ⦊ᵢ .

  Definition reduce_t_inj (Δ : context) : reduce_t Δ -> compo_t Δ.
  intros [ ? [ a b ]]. refine (x ,' (m_strat _ a , m_stratp _ b)).
  Defined.

  Definition reduce_t_eq (Δ : context) : relation (reduce_t Δ) :=
    fun u v => compo_t_eq Δ (reduce_t_inj _ u) (reduce_t_inj _ v).

  Equations reduce {Δ} : (fun (_ : T1) => reduce_t Δ) ⇒ᵢ itree ∅ₑ (fun _ => msg' Δ) :=
    reduce T1_0 u := sub_eval_msg
                       ([ v_var , concat1 (snd (fst (projT2 u))) (snd (projT2 u)) ])
                       (fst (fst (projT2 u))) .

  Lemma quatre_trois_pre {Δ} (x : reduce_t Δ)
    :
        (compo_body T1_0 (reduce_t_inj _ x) >>= fun _ r => go (match r with
                                     | inl x' => TauF (reduce _ x')
                                     | inr y => RetF (y : (fun _ => msg' _) _)
                                     end))
        ≊
      (eval (fst (fst (projT2 x))) >>=
                      fun _ u =>
                        go (match cover_split cover_cat _ (fst (projT2 (projT1 u))) with
                            | inl h => RetF (_ ,' (h, snd (projT2 (projT1 u))))
                            | inr h => TauF (reduce _ (_ ,'
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
      destruct (cover_split cover_cat _ i).
      econstructor; reflexivity.
      econstructor; reflexivity.
    + econstructor. apply CIH.
    + destruct q.
  Qed.

  Definition eval_sub_1 {Γ Δ} (c : conf (Δ +▶ Γ)) (e : Γ ⇒ᵥ Δ)
             : delay { m : msg' Δ & dom' m ⇒ᵥ Δ } :=
        eval ([ v_var , e ] @ₜ c) .

  Definition eval_sub_2 {Γ Δ} (c : conf (Δ +▶ Γ)) (e : Γ ⇒ᵥ Δ)
             : delay { m : msg' Δ & dom' m ⇒ᵥ Δ }.
    refine (eval c >>= fun 'T1_0 x =>
               go (match cover_split cover_cat _ (fst (projT2 (projT1 x))) with
                   | inl h => RetF ((_ ,' (h , snd (projT2 (projT1 x)))) ,'
                                   [ v_var,  e ] ⊛ (projT2 x))
                   | inr h => TauF _
                   end)) .
    refine (eval ([ e , ([v_var , e ] ⊛ projT2 x) ] @ₜ (emb (_ ,' (h , (snd (projT2 (projT1 x)))))))).
  Defined.

  Hypothesis eval_hyp : forall {Γ Δ}
                          (c : conf (Δ +▶ Γ))
                          (e : Γ ⇒ᵥ Δ),
                          eval_sub_1 c e ≊ eval_sub_2 c e .

  Lemma quatre_trois {Δ a} (c : m_strat_act Δ a) (e : m_strat_pas Δ a)
    : reduce _ (_ ,' (c , e)) ≊ (c ∥ e) .
    refine (iter_lem compo_body reduce _ _ (_ ,' (c , e))).
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
    refine (@it_eq_up2bind_t _ ∅ₑ (fun _ => {m : msg' (Δ +▶ join_even x) & dom' m ⇒ᵥ (Δ +▶ _)}) _ (eqᵢ _) _ _ _ (eval (fst u) >>= _) (eval (fst u) >>= _) _).
    econstructor; eauto.
    intros [] [m γ] ? <-.
    apply (bt_t (it_eq_map ∅ₑ (eqᵢ (fun _ : T1 => msg' Δ)))).
    cbn [fst snd projT2 projT1].
    destruct (cover_split cover_cat _ (fst (projT2 m))).
    - econstructor. reflexivity.
    - econstructor.
      unfold reduce.
      fold (@fmap _ ∅ₑ _ _ (fun _ : T1 => projT1 (P:=fun m0 : msg' Δ => dom' m0 ⇒ᵥ Δ)) T1_0).
      change (it_eq_t ∅ₑ (eqᵢ (fun _ : T1 => msg' Δ)) bot T1_0 ?a ?b) with (it_eq (eqᵢ _) a b).
      apply fmap_eq.
      unfold m_strat_resp.
      cbn [fst snd projT1 projT2].
      rewrite c_sub_sub.
      unshelve rewrite c_sub_proper; try reflexivity.
      apply s_eq_cover_uniq.
      * rewrite <- (proj2 (quatre_six (snd u) v)).
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
          rewrite s_eq_cat_r, <- e_comp_ren_l, v_sub_var.
          cbn; now rewrite s_ren_comp, 2 s_eq_cat_r .
   Qed.

  Lemma quatre_trois_app {Γ Δ}
    (c : conf Γ) (e : Γ ⇒ᵥ Δ)
    : sub_eval_msg e c ≊ (inj_init_act c ∥ inj_init_pas e).
  Proof.
    rewrite <- quatre_trois.
    unfold reduce, inj_init_act, sub_eval_msg; cbn [fst snd projT1 projT2]; apply fmap_eq.
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
    apply compo_proper. exact H. unfold m_strat_pas_eqv, m_strat_act_eqv; eauto.
  Qed.

End withInteractionSpec.
