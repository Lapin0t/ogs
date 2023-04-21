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
  Record machine : Type := {
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

  Definition v_ren {M Γ Δ} : Γ ⊆ Δ -> M.(val) Γ ⇒ᵢ M.(val) Δ :=
    fun u => M.(v_sub) (fun _ i => M.(v_var) _ (u _ i)) .
      
  Definition e_comp {M Γ1 Γ2 Γ3} (u : Γ2 =[M.(val)]> Γ3) (v : Γ1 =[M.(val)]> Γ2)
             : Γ1 =[M.(val)]> Γ3
    := s_map (M.(v_sub) u) v.

  Definition e_ren {M Γ1 Γ2 Γ3} (u : Γ2 ⊆ Γ3) (v : Γ1 =[M.(val)]> Γ2)
             : Γ1 =[M.(val)]> Γ3
    := s_map (v_ren u) v.

  Definition c_ren {M Γ1 Γ2} (u : Γ1 ⊆ Γ2) (c : M.(conf) Γ1) : M.(conf) Γ2
    := M.(c_sub) (fun _ i => v_ren u _ (M.(v_var) _ i)) c.

  Record machine_law (M : machine) : Type := {
    v_sub_proper {Γ Δ}
      : Proper
          (sub_eq Γ Δ ==> (dpointwise_relation (fun i => eq ==> eq)))
          M.(v_sub) ;
    c_sub_proper {Γ Δ}
      : Proper
          (sub_eq Γ Δ ==> eq ==> eq)
          M.(c_sub) ;
    v_sub_var {Γ1 Γ2} (p : Γ1 =[M.(val)]> Γ2) {t} i
      : M.(v_sub) p t (M.(v_var) t i)
      = p t i ;
    v_var_sub {Γ} {t} (v : M.(val) Γ t)
      : M.(v_sub) M.(v_var) t v
      = v ;
    v_sub_sub {Γ1 Γ2 Γ3} p q {t} v
      : M.(v_sub) p t (M.(v_sub) q t v)
      = M.(v_sub) (@e_comp M Γ1 Γ2 Γ3 p q) t v ;
    c_var_sub {Γ} (c : M.(conf) Γ)
      : M.(c_sub) M.(v_var) c
      = c ;
    c_sub_sub {Γ1 Γ2 Γ3} u v x
      : M.(c_sub) u (M.(c_sub) v x)
      = M.(c_sub) (@e_comp M Γ1 Γ2 Γ3 u v) x ;
  }. 
  Arguments c_sub_proper {M}.
  Arguments v_sub_proper {M}.
  Arguments v_sub_var {M}.
  Arguments v_var_sub {M}.
  Arguments v_sub_sub {M}.
  Arguments c_var_sub {M}.
  Arguments c_sub_sub {M}.

  Program Definition sub_eval_msg {Γ Δ} (M : machine) (e : Γ =[M.(val)]> Δ) (t : M.(conf) Γ)
             : delay (msg' Δ)
    := fmap (fun _ => @projT1 _ _) _ (M.(eval) (M.(c_sub) e t)).

  Definition ciu (M : machine) {Γ} Δ (x y : M.(conf) Γ) : Prop :=
    forall (e : Γ =[M.(val)]> Δ), it_wbisim (sub_eval_msg M e x) (sub_eval_msg M e y).

  (* Section 3: game definition
     ↓+ ~ join_even
   *)
  Definition alt_ext : Type := ctx (ctx S.(typ)).

  Definition ogs_hg : half_game alt_ext alt_ext := {|
    g_move := fun es => msg' (join_even es) ;
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
  Inductive alt_env (M : machine) (Δ : ctx S.(typ))
    : bool -> alt_ext -> Type :=
  | ENil {b} : alt_env M Δ b ∅
  | EConT {a Γ} : alt_env M Δ opponent a
                  -> alt_env M Δ player (a ▶ Γ)
  | EConF {a Γ} : alt_env M Δ player a
                  -> Γ =[M.(val)]> (Δ +▶ join_even a)
                  -> alt_env M Δ opponent (a ▶ Γ)
  .
  Arguments ENil {M Δ b}.
  Arguments EConT {M Δ a Γ}.
  Arguments EConF {M Δ a Γ}.

  (* flattens an alternating environment into an unstructured one *)
  Equations concat0 {M Δ b a} : alt_env M Δ b a
             -> (join_even_odd_aux (negb b) a) =[M.(val)]> (Δ +▶ join_even_odd_aux b a) :=
    concat0 (ENil) := s_empty ;
    concat0 (EConT u) := s_map (v_ren r_concat3_1) (concat0 u) ;
    concat0 (EConF u e) := s_cat (concat0 u) e .

  (* Flattens a pair of alternating environments for resp. player and opponent into a "closed" substitution *)
  Equations concat1 {M Δ} a b :
    alt_env M Δ b a ->
    alt_env M Δ (negb b) a ->
    (join_even_odd_aux b a) =[M.(val)]> Δ :=
    concat1 ∅      b _ _ :=
      s_empty ;
    concat1 (a ▶ _) b (EConT u) (EConF v e) :=
      s_cat
        (concat1 a _ u v)
        (e_comp (s_cat M.(v_var) (concat1 a _ v u)) e) ;
    concat1 (a ▶ _) b (EConF u e) (EConT v) := concat1 a _ u v .
  Arguments concat1 {M Δ a}.

  Lemma quatre_six {M Δ a} b
    (u : alt_env M Δ b a) (v : alt_env M Δ (negb b) a)
    {x i} :
    e_comp
        (s_cat M.(v_var) (concat1 b u v))
        (concat0 u) x i
    = concat1 (negb b)
        v
        (rew [fun x => alt_env _ _ x _] (Bool.negb_involutive_reverse b) in u)
        x i.
  Admitted.

  Definition m_strat_act (M : machine) Δ : alt_ext -> Type :=
    fun a => (M.(conf) (Δ +▶ join_even a) * alt_env M Δ player a)%type.

  Definition m_strat_pas (M : machine) Δ : alt_ext -> Type :=
    fun a => alt_env M Δ opponent a.

  Definition m_strat_play {M Δ a} (x : m_strat_act M Δ a)
    : delay (msg' Δ + h_actv ogs_hg (m_strat_pas M Δ) a)%type :=
    (M.(eval) (fst x)) >>=
      fun _ u =>
        match cover_split cover_cat (fst (projT2 (projT1 u))) with
        | inl h => Ret' (inl (_ ,' (h , snd (projT2 (projT1 u)))))
        | inr h => Ret' (inr ((_ ,' (h , snd (projT2 (projT1 u)))) ,' EConF (snd x) (projT2 u)))
        end .

  Definition m_strat_resp {M Δ a} (x : m_strat_pas M Δ a)
    : h_pasv ogs_hg (m_strat_act M Δ) a
    := fun m => (M.(c_sub)
                  (s_cat (e_ren r_concat3_1 (concat0 x))
                         (e_ren (r_concat_r ∘⊆ r_concat_r) M.(v_var)))
              (M.(emb) m) ,
          EConT x).

  Definition m_strat {M Δ} : m_strat_act M Δ ⇒ᵢ itree ogs_e (fun _ => msg' Δ) :=
    iter
      (fun i e =>
         emb_delay (m_strat_play e) >>=
           fun _ '(Fib x) =>
             match x with
             | inl m => Ret' (inr m)
             | inr (m,'c) => Vis' (m : ogs_e.(e_qry) i) (fun r => Ret' (inl (m_strat_resp c r)))
             end).

  Definition m_stratp {M Δ} : m_strat_pas M Δ ⇒ᵢ h_pasv ogs_hg (itree ogs_e (fun _ => msg' Δ)) :=
    fun _ x m => m_strat _ (m_strat_resp x m).

  Definition inj_init_act {M : machine} {Δ Γ} (c : M.(conf) Γ)
             : m_strat_act M Δ (∅ ▶ Γ)
    := (c_ren (r_concat_r ∘⊆ r_concat_r) c , EConT ENil).

  Definition inj_init_pas {M : machine} {Δ Γ} (γ : Γ =[M.(val)]> Δ)
             : m_strat_pas M Δ (∅ ▶ Γ)
    := EConF ENil (e_ren r_concat_l γ).

  Definition compo_t M (Δ : ctx S.(typ)) : Type := ⦉ m_strat_act M Δ ×ᵢ m_strat_pas M Δ ⦊ᵢ .

  Equations compo_body {M Δ} : (fun (_ : T1) => compo_t M Δ)
                             ⇒ᵢ itree ∅ₑ (fun _ => compo_t M Δ + msg' Δ)%type :=
    compo_body T1_0 x :=
      m_strat_play (fst (projT2 x)) >>= fun _ r =>
          go (match r with
              | inl r => RetF (inr r)
              | inr e => RetF (inl (_ ,' (m_strat_resp (snd (projT2 x)) (projT1 e) , (projT2 e))))
              end).  

  Definition compo {M Δ} a
    (u : m_strat_act M Δ a)
    (v : m_strat_pas M Δ a)
    : delay (msg' Δ)
    := iter compo_body T1_0 (a ,' (u , v)).

  (* guilhem: rename? *)
  Definition barb (M : machine) {Γ} Δ (x y : M.(conf) Γ) : Prop :=
    forall e : Γ =[M.(val)]> Δ,
    it_wbisim (compo _ (inj_init_act x) (inj_init_pas e))
              (compo _ (inj_init_act y) (inj_init_pas e)).

  Equations reduce {M : machine} {Δ} : (fun (_ : T1) => compo_t M Δ) ⇒ᵢ itree ∅ₑ (fun _ => msg' Δ) :=
    reduce T1_0 u := sub_eval_msg M (s_cat (M.(v_var)) (concat1 _ (snd (fst (projT2 u))) (snd (projT2 u)))) (fst (fst (projT2 u))) .

  Lemma quatre_trois_pre {M : machine} {Δ} (x : compo_t M Δ)
    : it_eq
        (compo_body T1_0 x >>= fun _ r => go (match r with
                                     | inl x' => TauF (reduce _ x')
                                     | inr y => RetF (y : (fun _ => msg' _) _)
                                     end))
      (M.(eval) (fst (fst (projT2 x))) >>=
                      fun _ u =>
                        go (match cover_split cover_cat (fst (projT2 (projT1 u))) with
                            | inl h => RetF (_ ,' (h, snd (projT2 (projT1 u))))
                            | inr h => TauF (reduce _ (_ ,'
                                                    (m_strat_resp (snd (projT2 x)) (_ ,' (h, snd (projT2 (projT1 u)))), EConF (snd (fst (projT2 x))) (projT2 u))))
                            end)).
  Proof.
    etransitivity.
    unfold compo_body; apply bind_bind_com.
    etransitivity.
    unfold m_strat_play; apply bind_bind_com.
    remember (M.(eval) (fst (fst (projT2 x)))) as t eqn:H; clear H; revert t.
    unfold it_eq; coinduction R CIH; intros t.
    cbn; destruct (t.(_observe)).
    + destruct r as [[? [i m]] γ]; cbn.
      destruct (cover_split cover_cat i).
      econstructor; reflexivity.
      econstructor; reflexivity.
    + econstructor. apply CIH.
    + destruct q.
  Qed.
    
  Definition eval_sub_1 {M : machine} {Γ Δ} (c : M.(conf) (Δ +▶ Γ)) (e : Γ =[M.(val)]> Δ)
             : delay { m : msg' Δ & dom' m =[M.(val)]> Δ } :=
        M.(eval) (M.(c_sub) (s_cat M.(v_var) e) c) .

  Definition eval_sub_2 {M : machine} {Γ Δ} (c : M.(conf) (Δ +▶ Γ)) (e : Γ =[M.(val)]> Δ)
             : delay { m : msg' Δ & dom' m =[M.(val)]> Δ }.
    refine (M.(eval) c >>= fun 'T1_0 x =>
               go (match cover_split cover_cat (fst (projT2 (projT1 x))) with
                   | inl h => RetF ((_ ,' (h , snd (projT2 (projT1 x)))) ,'
                                   e_comp (s_cat M.(v_var) e) (projT2 x))
                   | inr h => TauF _
                   end)) .
    refine (M.(eval) (M.(c_sub) (s_cat e (e_comp (s_cat M.(v_var) e) (projT2 x))) (M.(emb) (_ ,' (h , (snd (projT2 (projT1 x)))))))).
  Defined.

  Hypothesis eval_hyp : forall {M : machine} {Γ Δ}
                          (c : M.(conf) (Δ +▶ Γ))
                          (e : Γ =[M.(val)]> Δ),
                          it_eq (eval_sub_1 c e) (eval_sub_2 c e) .

  Lemma quatre_trois {M : machine} {MH : machine_law M} {Δ a}
    (c : m_strat_act M Δ a)
    (e : m_strat_pas M Δ a)
    : it_eq (reduce _ (_ ,' (c , e))) (compo _ c e) .
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
    refine (@it_eq_up2bind_t _ ∅ₑ (fun _ => {m : msg' (Δ +▶ join_even x) & dom' m =[ val M ]> (Δ +▶ join_even x)}) _ _ _ (M.(eval) (fst u) >>= _) (M.(eval) (fst u) >>= _) _).
    econstructor; eauto.
    intros [] [m γ].
    apply (bt_t (it_eq_map ∅ₑ (fun _ : T1 => msg' Δ))).
    cbn [fst snd projT2 projT1].
    destruct (cover_split cover_cat (fst (projT2 m))).
    - econstructor.
    - econstructor.
      unfold reduce.
      fold (@fmap _ ∅ₑ _ _ (fun _ : T1 => projT1 (P:=fun m0 : msg' Δ => dom' m0 =[ val M ]> Δ)) T1_0).
      change (it_eq_t ∅ₑ (fun _ : T1 => msg' Δ) bot T1_0 ?a ?b) with (it_eq a b).
      apply fmap_eq.
      unfold m_strat_resp.
      cbn [fst snd projT1 projT2].
      rewrite MH.(c_sub_sub).
      unshelve rewrite MH.(c_sub_proper); try reflexivity.
      intros ? ? ? ->.
      destruct m as [? [i m]]; unfold dom' in *; cbn [dom' fst snd projT1 projT2] in *.
  Admitted.

  Lemma quatre_trois_app {M : machine} {MH : machine_law M} {Γ Δ}
    (c : M.(conf) Γ) (e : Γ =[M.(val)]> Δ)
    : it_eq (sub_eval_msg M e c) (compo _ (inj_init_act c) (inj_init_pas e)).
    etransitivity.
    2: apply (@quatre_trois M MH).
    cbn [reduce fst snd projT1 projT2].
    unfold inj_init_act, sub_eval_msg.
    cbn [reduce fst snd projT1 projT2].
    apply fmap_eq.
    unfold c_ren.
    rewrite MH.(c_sub_sub), MH.(c_sub_proper); try reflexivity.

    intros ? i ? <-. unfold e_comp.
    unfold s_map.
    unfold v_ren.
    rewrite MH.(v_sub_sub).
    rewrite MH.(v_sub_var).
    unfold e_comp, s_map.
    rewrite MH.(v_sub_var).
    unfold r_comp.
    unfold inj_init_pas.
    cbn [join_even].
    rewrite concat1_equation_2, 2 concat1_equation_1.
    unfold s_ren.
    change (s_cat M.(v_var) ?u1 a (r_concat_r a ?u2)) with (s_ren (s_cat M.(v_var) u1) r_concat_r a u2).
    rewrite (s_eq_cat_r _ _ _ _ _ eq_refl).
    change (s_cat s_empty ?u1 a (r_concat_r a i)) with (s_ren (s_cat s_empty u1) r_concat_r a i).
    rewrite (s_eq_cat_r _ _ _ _ _ eq_refl).
    unfold e_comp, s_map.
    etransitivity.
    all: cycle 1.
    apply MH.(v_sub_proper).
    cbn [join_even].
    symmetry.
    exact (s_eq_cover_empty_r M.(v_var)).
    2: symmetry; apply MH.(v_var_sub).
    unfold e_ren, s_map, v_ren.
    etransitivity.
    symmetry; apply MH.(v_var_sub).
    apply MH.(v_sub_proper); try reflexivity.
    intros ? ? ? <-.
    f_equal.
    unfold r_concat_l, cover_cat.
    symmetry.
    exact (r_cover_l_nil _ _ x eq_refl).
    Qed.

  Theorem ogs_correction (M : machine) (MH : machine_law M) {Γ} Δ (x y : M.(conf) Γ)
          : barb M Δ x y -> ciu M Δ x y.
  Proof.
    intros H e.
    unfold barb in H.
    etransitivity.
    apply it_eq_wbisim, (@quatre_trois_app M MH _ _ x e).
    etransitivity.
    apply (H e).
    symmetry; apply it_eq_wbisim, (@quatre_trois_app M MH _ _ y e).
  Qed.

End a.
