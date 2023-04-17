
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
    v_var {Γ} : has Γ ⇒ᵢ val Γ ;
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
    := fmap (pin_map (@projT1 _ _)) _ (M.(eval) (M.(c_sub) e t)).

  Definition ciu (M : machine) {Γ} Δ (x y : M.(conf) Γ) : Prop :=
    forall (e : Γ =[M.(val)]> Δ), it_wbisim _ _ _ (sub_eval_msg M e x) (sub_eval_msg M e y).

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
  Definition concat1 {M Δ a} b : alt_env M Δ b a
             -> alt_env M Δ (negb b) a -> (join_even_odd_aux b a) =[M.(val)]> Δ.
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
             : delay (msg' Δ + h_actv ogs_hg (m_strat_pas M Δ) a)%type.
  refine (bind (M.(eval) (fst x)) _).
  intros ? [[[? [i m]] γ]].
  destruct (cover_split cover_cat i).
  - refine (Ret' (Fib (inl (_ ,' (h , m))))).
  - refine (Ret' (Fib (inr ((_ ,' (h , m)) ,' EConF (snd x) γ)))).
  Defined.

  Definition m_strat_resp {M Δ a} (x : m_strat_pas M Δ a)
    : h_pasv ogs_hg (m_strat_act M Δ) a.
  intro m.
  refine (M.(c_sub) _ (M.(emb) m) , EConT x).
  refine (s_cat _ _).
  refine (e_ren (r_concat3_1 _ _ _) (concat0 x)).
  refine (e_ren (r_concat_r _ _ ∘⊆ r_concat_r _ _) M.(v_var)).
  Defined.

  Definition m_strat {M Δ} : m_strat_act M Δ ⇒ᵢ itree ogs_e (fun _ => msg' Δ).
    apply iter; intros ? e.
    refine (emb_delay (m_strat_play e) >>= fun _ x => _).
    destruct x as [[m | [m c]]].
    - refine (Ret' (inr m)).
    - refine (Vis' (m : ogs_e.(e_qry) i) (fun r => Ret' (inl (m_strat_resp c r)))).
  Defined.

  Definition inj_init_act {M : machine} {Δ Γ} (c : M.(conf) Γ)
             : m_strat_act M Δ (∅ ▶ Γ)
    := (c_ren (r_concat_r _ _ ∘⊆ r_concat_r _ _) c , EConT ENil).

  Definition inj_init_pas {M : machine} {Δ Γ} (γ : Γ =[M.(val)]> Δ)
             : m_strat_pas M Δ (∅ ▶ Γ)
    := EConF ENil (e_ren (r_concat_l _ _) γ).

End a.
