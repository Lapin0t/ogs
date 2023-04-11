Require Import FunInd.
Require Import Program.Equality.

From OGS Require Import Utils.
From OGS.Utils Require Import Ctx.
From OGS.Game Require Import HalfGame Event.
From OGS.ITree Require Import ITree Monad Eq.

Open Scope ctx_scope.

Definition delay (X : Type) : Type := itree ∅ₑ (fun _ => X) T1_0.

Record lang_spec : Type := {
  typ : Type ;
  msg : typ -> Type ;
  dom : forall t, msg t -> ctx typ ; 
}.
Arguments dom _ [_].

Section a.

  Context (S : lang_spec).

  Definition msg' (Γ : ctx S.(typ)) : Type :=
    { t : S.(typ) & Γ ∋ t * S.(msg) t }%type.

  Definition dom' {Γ} (m : msg' Γ) : ctx S.(typ) :=
    S.(dom) (snd (projT2 m)).

  Record machine : Type := {
    conf : ctx S.(typ) -> Type ;
    env : ctx S.(typ) -> ctx S.(typ) -> Type ;
    eval {Γ} : conf Γ -> delay { m : msg' Γ & env Γ (dom' m) } ;
    emb {Γ} (m : msg' Γ) : conf (Γ +▶ dom' m) ;
    c_sub {Γ Δ} : conf Γ -> env Δ Γ -> conf Δ ;
    e_empty {Δ} : env Δ ∅ ;
    e_cat {Γ1 Γ2 Δ} : env Δ Γ1 -> env Δ Γ2 -> env Δ (Γ1 +▶ Γ2) ;
    e_ren {Γ Δ1 Δ2} : Δ1 ⊆ Δ2 -> env Δ1 Γ -> env Δ2 Γ ;
    e_comp {Γ1 Γ2 Γ3} : env Γ1 Γ2 -> env Γ2 Γ3 -> env Γ1 Γ3 ;
    e_id {Γ} : env Γ Γ ;
  }.

  Definition sub_eval_msg {Γ Δ} (M : machine) (e : M.(env) Δ Γ) (t : M.(conf) Γ) : delay (msg' Δ) :=
    fmap (fun _ r => projT1 r) _ (M.(eval) (M.(c_sub) t e)).      

  Definition ciu (M : machine) {Γ} Δ (x y : M.(conf) Γ) : Prop :=
    forall (e : M.(env) Δ Γ), it_wbisim _ _ _ (sub_eval_msg M e x) (sub_eval_msg M e y).

  Definition alt_ext : Type := ctx (ctx S.(typ)).

  Definition ogs_hg : half_game alt_ext alt_ext := {|
    g_move := fun es => msg' (join_even es) ;
    g_next := fun es m => (es ▶ dom' m) ;
  |}.

  Definition ogs_g : game alt_ext alt_ext :=
    {| g_client := ogs_hg ;
       g_server := ogs_hg |}.

  Definition ogs_e : event alt_ext alt_ext := e_of_g ogs_g.

  Inductive alt_env (M : machine) (Δ : ctx S.(typ)) : bool -> alt_ext -> Type :=
  | ENil {b} : alt_env M Δ b ∅
  | EConT {a Γ} : alt_env M Δ false a
                  -> alt_env M Δ true (a ▶ Γ)
  | EConF {a Γ} : alt_env M Δ true a
                  -> M.(env) (Δ +▶ join_even a) Γ
                  -> alt_env M Δ false (a ▶ Γ)
  .
  Arguments ENil {M Δ b}.
  Arguments EConT {M Δ a Γ}.
  Arguments EConF {M Δ a Γ}.

  Equations concat0 {M Δ b a} : alt_env M Δ b a
             -> M.(env) (Δ +▶ join_even_odd_aux b a) (join_even_odd_aux (negb b) a) :=
    concat0 (ENil) := M.(e_empty) ;
    concat0 (EConT u) := M.(e_ren) (r_concat3_1 _ _ _) (concat0 u) ;
    concat0 (EConF u e) := M.(e_cat) (concat0 u) e .

  Definition concat1 {M Δ a} b : alt_env M Δ true a
             -> alt_env M Δ false a -> M.(env) Δ (join_even_odd_aux b a).
    revert b; induction a; intros b u v; dependent destruction u; dependent destruction v.
    - refine (M.(e_empty)).
    - destruct b; cbn in *.
      * refine (M.(e_cat) (IHa false v u) _).
        refine (M.(e_comp) _ e).
        refine (M.(e_cat) M.(e_id) (IHa true v u)).
      * exact (IHa true v u).
   Qed.
