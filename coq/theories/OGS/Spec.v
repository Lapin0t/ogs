Require Import Program.Equality.
Import EqNotations.

From Coinduction Require Import coinduction tactics.

From OGS Require Import Utils.
From OGS.Utils Require Import Ctx.
From OGS.Game Require Import HalfGame Event.
From OGS.ITree Require Import ITree Monad Eq Delay.

Set Equations Transparent.

Open Scope ctx_scope.

(*
  Mapping with pdf: operational signature

typ : set of types
msg : to each typ a message
dom : for each message the context extension it entails (a.k.a. free variables of the message)
 *)
Record interaction_spec : Type := {
  typ : Type ;
  msg : typ -> Type ;
  dom : forall t, msg t -> ctx typ ;
}.
Arguments dom _ [_].

Section a.

  Context (S : interaction_spec).

  (* pdf: msg* *)
  Definition msg' (Γ : ctx S.(typ)) : Type :=
    { t : S.(typ) & Γ ∋ t * S.(msg) t }%type.

  (* pdf: dom* *)
  Definition dom' {Γ} (m : msg' Γ) : ctx S.(typ) :=
    S.(dom) (snd (projT2 m)).

  (* (Axiomatization of the) Operational machine:

Question GJ: should msg' be renamed into move?

TODO: concretize env

     1-5 : current status of the pdf
     6-10: administration
   *)
  Class machine : Type := {
    (* configurations (used to be called "terms" far in the past)
       roughly: active states *)
    conf : ctx S.(typ) -> Type ;
    (* roughly: elementary passive states *)
    val : ctx S.(typ) -> S.(typ) -> Type ;
    (* evaluation function for configurations *)
    eval {Γ} : conf Γ -> delay { m : msg' Γ & dom' m =[val]> Γ } ;
    emb {Γ} (m : msg' Γ) : conf (Γ +▶ dom' m) ;
    (* value variables *)
    v_var {Γ} : has Γ ⇒ᵢ val Γ ; (*  Γ ∋ x -> val Γ x   *)
    (* value substitution *)
    v_sub {Γ Δ} : Γ =[val]> Δ -> val Γ ⇒ᵢ val Δ ;
    (* configuration substitution *)
    c_sub {Γ Δ} : Γ =[val]> Δ -> conf Γ -> conf Δ ;
    }.

  Notation "u @ᵥ v" := (v_sub u _ v) (at level 30).
  Notation "u @ₜ c" := (c_sub u c) (at level 30).

 
  Notation "Γ ⇒ᵥ Δ" := (Γ =[val]> Δ) (at level 30).

  Definition v_ren {M : machine} {Γ Δ} : Γ ⊆ Δ -> val Γ ⇒ᵢ val Δ :=
    fun u => v_sub (v_var ⊛ᵣ u) .
      
  Definition e_comp {M : machine} {Γ1 Γ2 Γ3} : Γ2 ⇒ᵥ Γ3 -> Γ1 ⇒ᵥ Γ2 -> Γ1 ⇒ᵥ Γ3
    := fun u v => s_map (v_sub u) v.
  Infix "⊛" := e_comp (at level 14).

  Definition e_ren {M : machine} {Γ1 Γ2 Γ3} : Γ2 ⊆ Γ3 -> Γ1 ⇒ᵥ Γ2 -> Γ1 ⇒ᵥ Γ3
    := fun u v => (v_var ⊛ᵣ u) ⊛ v.
  Infix "ᵣ⊛" := e_ren (at level 14).

  Definition c_ren {M : machine} {Γ1 Γ2} : Γ1 ⊆ Γ2 -> conf Γ1 -> conf Γ2
    := fun u c => (u ᵣ⊛ v_var) @ₜ c.

  Class machine_law (M : machine) : Prop := {
    v_sub_proper {Γ Δ}
      :> Proper
          (sub_eq Γ Δ ==> forall_relation (fun i => eq ==> eq))
          v_sub ;
    c_sub_proper {Γ Δ}
      :> Proper
          (sub_eq Γ Δ ==> eq ==> eq)
          c_sub ;
    v_sub_var {Γ1 Γ2} (p : Γ1 ⇒ᵥ Γ2) : p ⊛ v_var ≡ₛ p ;
    v_var_sub {Γ1 Γ2} (p : Γ1 ⇒ᵥ Γ2) : v_var ⊛ p ≡ₛ p ;
    v_sub_sub {Γ1 Γ2 Γ3 Γ4} (p : Γ3 ⇒ᵥ Γ4) (q : Γ2 ⇒ᵥ Γ3) (r : Γ1 ⇒ᵥ Γ2)
      : p ⊛ (q ⊛ r) ≡ₛ (p ⊛ q) ⊛ r ;
    c_var_sub {Γ} (c : conf Γ) : v_var @ₜ c = c ;
    c_sub_sub {Γ1 Γ2 Γ3} (u : Γ2 ⇒ᵥ Γ3) (v : Γ1 ⇒ᵥ Γ2) {c}
      : u @ₜ (v @ₜ c) = (u ⊛ v) @ₜ c ;
  }.

  Context {M : machine} {MH : machine_law M}.

  #[global] Instance e_comp_proper {Γ1 Γ2 Γ3}
             : Proper (sub_eq Γ2 Γ3 ==> sub_eq Γ1 Γ2 ==> sub_eq Γ1 Γ3) e_comp.
    intros ? ? H1 ? ? H2 ? i.
    unfold e_comp, s_map.
    now rewrite H1, H2.
  Qed.

  #[global] Instance e_ren_proper {Γ1 Γ2 Γ3}
             : Proper (sub_eq Γ2 Γ3 ==> sub_eq Γ1 Γ2 ==> sub_eq Γ1 Γ3) e_ren.
  intros ? ? H1 ? ? H2.
  unfold e_ren. apply e_comp_proper; eauto. now rewrite H1.
  Qed.

  Lemma e_comp_ren_r {Γ1 Γ2 Γ3 Γ4} (u : Γ3 ⇒ᵥ Γ4) (v : Γ2 ⇒ᵥ Γ3) (w : Γ1 ⊆ Γ2)
        : u ⊛ (v ⊛ᵣ w) ≡ₛ (u ⊛ v) ⊛ᵣ w .
    reflexivity.
  Qed.

  Lemma e_comp_ren_l {Γ1 Γ2 Γ3 Γ4} (u : Γ3 ⇒ᵥ Γ4) (v : Γ2 ⊆ Γ3) (w : Γ1 ⇒ᵥ Γ2)
        : (u ⊛ᵣ v) ⊛ w ≡ₛ u ⊛ (v ᵣ⊛ w) .
    unfold e_ren.
    now rewrite v_sub_sub, e_comp_ren_r, v_sub_var.
  Qed.

  Program Definition sub_eval_msg {Γ Δ} (e : Γ ⇒ᵥ Δ) (t : conf Γ)
             : delay (msg' Δ)
    := fmap (fun _ => @projT1 _ _) _ (eval (e @ₜ t)).

  #[global] Instance sub_eval_msg_proper {Γ Δ}
             : Proper (sub_eq Γ Δ ==> pointwise_relation _ eq) (@sub_eval_msg Γ Δ).
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
  Definition alt_ext : Type := ctx (ctx S.(typ)).
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

  Notation player   := true.
  Notation opponent := false.
  (* Env* (def 3.12)
     Env M Δ player es : environment part of the player (aka active at es) configuration at (Δ + es)
     Env M Δ opponent es : environment part of the opponent (aka passive at es) configuration at (Δ + es)
   *)
  Inductive alt_env (Δ : ctx S.(typ))
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
    :  [ v_var , concat1 u v ] ⊛ concat0 u ≡ₛ concat1 v u
    /\ [ v_var , concat1 v u ] ⊛ concat0 v ≡ₛ concat1 u v .
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
        rewrite <- s_ren_comp.
        change (?a ∘⊆ ?b) with (a ⊛ᵣ b).
        now rewrite 2 s_eq_cat_l.
      * unfold r_concat3_1.
        rewrite <- s_ren_comp.
        change (?a ∘⊆ ?b) with (a ⊛ᵣ b).
        rewrite s_eq_cat_r.
        change (?a ⊛ᵣ ?b) with (a ∘⊆ b) at 2.
        now rewrite s_ren_comp, s_eq_cat_r, s_eq_cat_l.
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
         ([ (r_concat3_1 ᵣ⊛ concat0 x) , (r_concat_r ∘⊆ r_concat_r) ᵣ⊛ v_var ] @ₜ emb m ,
          EConT x).

  Definition m_strat {Δ} : m_strat_act Δ ⇒ᵢ itree ogs_e (fun _ => msg' Δ) :=
    iter
      (fun i e =>
         emb_delay (m_strat_play e) >>=
           fun _ '(Fib x) =>
             match x with
             | inl m => Ret' (inr m)
             | inr (m,'c) => Vis' (m : ogs_e.(e_qry) i) (fun r => Ret' (inl (m_strat_resp c r)))
             end).

  Definition m_stratp {Δ} : m_strat_pas Δ ⇒ᵢ h_pasv ogs_hg (itree ogs_e (fun _ => msg' Δ)) :=
    fun _ x m => m_strat _ (m_strat_resp x m).

  Definition inj_init_act {Δ Γ} (c : conf Γ) : m_strat_act Δ (∅ ▶ Γ)
    := (c_ren (r_concat_r ∘⊆ r_concat_r) c , EConT ENil).

  Definition inj_init_pas {Δ Γ} (γ : Γ ⇒ᵥ Δ) : m_strat_pas Δ (∅ ▶ Γ)
    := EConF ENil (e_ren r_concat_l γ).

  Definition compo_t (Δ : ctx S.(typ)) : Type := ⦉ m_strat_act Δ ×ᵢ m_strat_pas Δ ⦊ᵢ .

  Equations compo_body {Δ}
            : (fun (_ : T1) => compo_t Δ) ⇒ᵢ itree ∅ₑ (fun _ => compo_t Δ + msg' Δ)%type :=
    compo_body T1_0 x :=
      m_strat_play (fst (projT2 x)) >>= fun _ r =>
          go (match r with
              | inl r => RetF (inr r)
              | inr e => RetF (inl (_ ,' (m_strat_resp (snd (projT2 x)) (projT1 e) , (projT2 e))))
              end).  

  Definition compo {Δ a} (u : m_strat_act Δ a) (v : m_strat_pas Δ a) : delay (msg' Δ)
    := iter compo_body T1_0 (a ,' (u , v)).

  Notation "u ∥ v" := (compo u v) (at level 40).

  (* guilhem: rename? *)
  Definition barb {Γ} Δ (x y : conf Γ) : Prop :=
    forall e : Γ ⇒ᵥ Δ, (inj_init_act x ∥ inj_init_pas e) ≈ (inj_init_act y ∥ inj_init_pas e).

  Equations reduce {Δ} : (fun (_ : T1) => compo_t Δ) ⇒ᵢ itree ∅ₑ (fun _ => msg' Δ) :=
    reduce T1_0 u := sub_eval_msg
                       ([ v_var , concat1 (snd (fst (projT2 u))) (snd (projT2 u)) ])
                       (fst (fst (projT2 u))) .

  Lemma quatre_trois_pre {Δ} (x : compo_t Δ)
    : 
        (compo_body T1_0 x >>= fun _ r => go (match r with
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
    apply (tt_t (it_eq_map ∅ₑ (fun _ : T1 => msg' Δ))).
    refine (@it_eq_up2bind_t _ ∅ₑ (fun _ => {m : msg' (Δ +▶ join_even x) & dom' m ⇒ᵥ (Δ +▶ _)}) _ _ _ (eval (fst u) >>= _) (eval (fst u) >>= _) _).
    econstructor; eauto.
    intros [] [m γ].
    apply (bt_t (it_eq_map ∅ₑ (fun _ : T1 => msg' Δ))).
    cbn [fst snd projT2 projT1].
    destruct (cover_split cover_cat _ (fst (projT2 m))).
    - econstructor.
    - econstructor.
      unfold reduce.
      fold (@fmap _ ∅ₑ _ _ (fun _ : T1 => projT1 (P:=fun m0 : msg' Δ => dom' m0 ⇒ᵥ Δ)) T1_0).
      change (it_eq_t ∅ₑ (fun _ : T1 => msg' Δ) bot T1_0 ?a ?b) with (it_eq a b).
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
          rewrite <- s_ren_comp.
          change (?a ∘⊆ ?b) with (a ⊛ᵣ b).
          now rewrite 2 s_eq_cat_l.
        + unfold r_concat3_1.
          rewrite <- s_ren_comp.
          change (?a ∘⊆ ?b) with (a ⊛ᵣ b).
          rewrite s_eq_cat_r.
          change (?a ⊛ᵣ ?b) with (a ∘⊆ b) at 2.
          cbn; now rewrite s_ren_comp, s_eq_cat_r, s_eq_cat_l.
      * rewrite <- e_comp_ren_r.
          rewrite s_eq_cat_r.
          change (?a ∘⊆ ?b) with (a ⊛ᵣ b).
          rewrite <- e_comp_ren_l, v_sub_var.
          change (?a ⊛ᵣ ?b) with (a ∘⊆ b) at 2.
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
    unfold e_ren; rewrite v_sub_sub, v_sub_var.
    rewrite s_eq_cover_empty_r.
    rewrite 2 e_comp_ren_r.
    rewrite 2 v_sub_var.
    rewrite s_ren_comp.
    rewrite 2 s_eq_cat_r.
    unfold r_concat_l, cover_cat; cbn.
    rewrite r_cover_l_nil.
    now rewrite s_ren_id, v_var_sub. 
  Qed.

  Theorem ogs_correction {Γ} Δ (x y : conf Γ)
          : barb Δ x y -> ciu Δ x y.
  Proof.
    intros H e.
    etransitivity; [ apply it_eq_wbisim, (quatre_trois_app x e) | ].
    etransitivity; [ apply (H e) | ].
    symmetry; apply it_eq_wbisim, (quatre_trois_app y e).
  Qed.

End a.
