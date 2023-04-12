Require Import FunInd.
Require Import Program.Equality.

From OGS Require Import Utils.
From OGS.Utils Require Import Ctx.
From OGS.Game Require Import HalfGame Event.
From OGS.ITree Require Import ITree Monad Eq.

Open Scope ctx_scope.

(* domain of computations: isomorphic to Capretta's delay monad *)
Definition delay (X : Type) : Type :=
  itree ∅ₑ (fun _ => X) T1_0.

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
         Roughly: active states
       *)
    conf : ctx S.(typ) -> Type ;
      (* assignments
         Roughly: passive states
       *)
    env : ctx S.(typ) -> ctx S.(typ) -> Type ;
      (* evaluation function for configurations *)
    eval {Γ} : conf Γ -> delay { m : msg' Γ & env Γ (dom' m) } ;
      (* (very) Roughly: injecting patterns in terms *)
    emb {Γ} (m : msg' Γ) : conf (Γ +▶ dom' m) ;
      (* substitution *)
    c_sub {Γ Δ} : conf Γ -> env Δ Γ -> conf Δ ;

      (* axiomatization of the assignments *)
    e_empty {Δ} : env Δ ∅ ;
    e_cat {Γ1 Γ2 Δ} : env Δ Γ1 -> env Δ Γ2 -> env Δ (Γ1 +▶ Γ2) ;
    e_ren {Γ Δ1 Δ2} : Δ1 ⊆ Δ2 -> env Δ1 Γ -> env Δ2 Γ ;
    e_comp {Γ1 Γ2 Γ3} : env Γ1 Γ2 -> env Γ2 Γ3 -> env Γ1 Γ3 ;
    e_id {Γ} : env Γ Γ ;
  }.

  Arguments it_wbisim {I E X i}.
  Definition sub_eval_msg {Γ Δ}
    (M : machine) (e : M.(env) Δ Γ) (t : M.(conf) Γ)
    : delay (msg' Δ) :=
    fmap (fun _ r => projT1 r) _ (M.(eval) (M.(c_sub) t e)).

  (* The quantification over contexts is inlined in
     the quantification over assignments [forall (e : M.(env) Δ Γ)]
   *)
  Definition ciu
    (M : machine) {Γ} Δ (x y : M.(conf) Γ) : Prop :=
    forall (e : M.(env) Δ Γ),
      it_wbisim (sub_eval_msg M e x) (sub_eval_msg M e y).

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
                  -> M.(env) (Δ +▶ join_even a) Γ
                  -> alt_env M Δ opponent (a ▶ Γ)
  .
  Arguments ENil {M Δ b}.
  Arguments EConT {M Δ a Γ}.
  Arguments EConF {M Δ a Γ}.

  (* flattens an alternating environment into an unstructured one *)
  Equations concat0 {M Δ b a} :
    alt_env M Δ b a ->
    M.(env)
        (Δ +▶ join_even_odd_aux b a)
        (join_even_odd_aux (negb b) a) :=
    concat0 (ENil) := M.(e_empty) ;
    concat0 (EConT u) := M.(e_ren) (r_concat3_1 _ _ _) (concat0 u) ;
    concat0 (EConF u e) := M.(e_cat) (concat0 u) e .

  (* Flattens a pair of alternating environments for resp. player and opponent into a "closed" substitution
   *)
  Definition concat1 {M Δ a} b :
    alt_env M Δ player a ->
    alt_env M Δ opponent a ->
    M.(env) Δ (join_even_odd_aux b a).
    revert b; induction a.
    - intros b u v.
      exact (M.(e_empty)).
    - intros b u v.
      dependent destruction u.
      dependent destruction v.
      destruct b; cbn in *.
      * refine (M.(e_cat) (IHa false v u) _).
        refine (M.(e_comp) _ e).
        refine (M.(e_cat) M.(e_id) (IHa true v u)).
      * exact (IHa true v u).
  Defined.

  Lemma quatre_six_un {M Δ a}
    (u : alt_env M Δ player a)
    (v : alt_env M Δ opponent a) :
    M.(e_comp)
        (M.(e_cat) M.(e_id) (concat1 player u v))
        (concat0 u)
    = concat1 opponent u v.
  Admitted.

  Lemma quatre_six_deux {M Δ a}
    (u : alt_env M Δ player a)
    (v : alt_env M Δ opponent a) :
    M.(e_comp)
        (M.(e_cat) M.(e_id) (concat1 opponent u v))
        (concat0 v)
    = concat1 player u v.
  Admitted.


