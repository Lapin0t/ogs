Set Equations Transparent.
Require Import Program.Equality.
Import EqNotations.

From OGS Require Import Utils.
From OGS.Utils Require Import Ctx.
From OGS.Game Require Import HalfGame Event.
From OGS.ITree Require Import ITree Monad Eq Delay.

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
    (* value renaming *)
    v_ren {Γ Δ} : Γ ⊆ Δ -> val Γ ⇒ᵢ val Δ ;
    (* value substitution *)
    v_sub {Γ Δ} : Γ =[val]> Δ -> val Γ ⇒ᵢ val Δ ;
    (* configuration substitution *)
    c_sub {Γ Δ} : Γ =[val]> Δ -> conf Γ -> conf Δ ;
  }.

  Definition e_comp {M Γ1 Γ2 Γ3} (u : Γ2 =[M.(val)]> Γ3) (v : Γ1 =[M.(val)]> Γ2)
             : Γ1 =[M.(val)]> Γ3
    := s_map (M.(v_sub) u) v.

  Definition e_ren {M Γ1 Γ2 Γ3} (u : Γ2 ⊆ Γ3) (v : Γ1 =[M.(val)]> Γ2)
             : Γ1 =[M.(val)]> Γ3
    := s_map (M.(v_ren) u) v.

  Definition c_ren {M Γ1 Γ2} (u : Γ1 ⊆ Γ2) (c : M.(conf) Γ1) : M.(conf) Γ2
    := M.(c_sub) (fun _ i => M.(v_ren) u _ (M.(v_var) _ i)) c.

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
    concat0 (EConT u) := s_map (M.(v_ren) (r_concat3_1 _ _ _)) (concat0 u) ;
    concat0 (EConF u e) := s_cat (concat0 u) e .

  (* Flattens a pair of alternating environments for resp. player and opponent into a "closed" substitution *)
  Definition concat1 {M Δ a} b :
    alt_env M Δ b a ->
    alt_env M Δ (negb b) a ->
    (join_even_odd_aux b a) =[M.(val)]> Δ.
    revert b; induction a; intros b u v; dependent destruction u; dependent destruction v.
    - refine (s_empty).
    - refine (s_cat (IHa false u v) _).
      refine (e_comp _ s).
      refine (s_cat M.(v_var) (IHa true v u)).
    - exact (IHa true u v).
  Defined.

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
                  (s_cat (e_ren (r_concat3_1 _ _ _) (concat0 x))
                         (e_ren (r_concat_r _ _ ∘⊆ r_concat_r _ _) M.(v_var)))
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
    := (c_ren (r_concat_r _ _ ∘⊆ r_concat_r _ _) c , EConT ENil).

  Definition inj_init_pas {M : machine} {Δ Γ} (γ : Γ =[M.(val)]> Δ)
             : m_strat_pas M Δ (∅ ▶ Γ)
    := EConF ENil (e_ren (r_concat_l _ _) γ).

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
    reduce T1_0 u :=
      fmap (fun _ => (@projT1 _ _)) _ (M.(eval) (M.(c_sub) (s_cat (M.(v_var)) (concat1 _ (snd (fst (projT2 u))) (snd (projT2 u)))) (fst (fst (projT2 u))))) .

  From Coinduction Require Import coinduction tactics.

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
    
  Hypothesis eval_ok : forall {M : machine} {Γ Δ}
    (c : M.(conf) (Δ +▶ Γ))
    (e : Γ =[M.(val)]> Δ),
    it_eq
        (M.(eval) (M.(c_sub) (s_cat M.(v_var) e) c))
        (M.(eval) c >>= fun 'T1_0 x =>
               go (match cover_split cover_cat (fst (projT2 (projT1 x))) with
                   | inl h => RetF ((_ ,' (h , snd (projT2 (projT1 x)))) ,'
                                   e_comp (s_cat M.(v_var) e) (projT2 x))
                   | inr h => TauF (M.(eval) _)
                   end)) .
    refine (M.(c_sub) (s_cat (s_cat M.(v_var) e) (e_comp (s_cat M.(v_var) e) (projT2 x))) (M.(emb) (projT1 x))))
    refine (M.(eval) _).
    refine .
    refine (s_cat  _).
    refine ((_ ,' (h , snd (projT2 (projT1 x)))) ,' (e_comp (s_cat M.(v_var) e) (projT2 x))).
    cbv [dom'] in *; cbn in *.
    refine (e_comp (s_cat M.(v_var) e) (projT2 x)).

  Lemma quatre_trois {M : machine} {Δ a}
    (c : m_strat_act M Δ a)
    (e : m_strat_pas M Δ a)
    : it_eq (reduce _ (_ ,' (c , e))) (compo _ c e) .
    refine (iter_lem compo_body reduce _ _ (_ ,' (c , e))).
    clear a c e; intros [] [ ? [ u v ] ].
    etransitivity; cycle 1.
    symmetry; apply quatre_trois_pre.
    unfold reduce at 1.

  Theorem ogs_correction (M : machine) {Γ} Δ (x y : M.(conf) Γ)
          : barb M Δ x y -> ciu M Δ x y.
    Admitted.

End a.
