Set Printing Projections.
Set Primitive Projections.

From Coq Require Import Logic.
Import EqNotations.

From Equations Require Import Equations.
Set Equations Transparent.

From ExtLib.Data Require Import List Fin.

From OGS Require Import Utils.
From OGS.ITree Require Import Cat Event Dual ITree Rec Angelic Eq.
From OGS.STLC Require Import Ctx Syntax.

From OGS.ITree Require Import Eq.
From Paco Require Import paco.

Variant optP {X : Type} (P : X -> Type) : option X -> Type :=
| OptP {x} : P x -> optP P (Some x)
.
Arguments OptP {X P x} p.

Section optP.
  Context {X : Type} {P : X -> Type} {A : forall x, P x -> Type}.

  Equations optP_el {x} : optP P x -> X :=
    optP_el (@OptP _ _ x _) := x .

  Equations optP_coh {x} (o : optP P x) : P (optP_el o) :=
    optP_coh (OptP p) := p .

  Equations optP_eq {x} (o : optP P x) : x = Some (optP_el o) :=
    optP_eq (OptP _) := eq_refl .

  Equations optP_elim (f : forall x p, A x p) {x} (o : optP P x) : A _ (optP_coh o) :=
    optP_elim f (OptP p) := f _ p .
End optP.


Equations lift_opt {X} : X -> option X -> X :=
  lift_opt x (Some y) := y ;
  lift_opt x None     := x .

Equations mult_opt {X} : option X -> option X -> option X :=
  mult_opt x (Some y) := Some y ;
  mult_opt x None     := x .

Equations opt_lift_mult {X} {x : X} y : mult_opt (Some x) y = Some (lift_opt x y) :=
  opt_lift_mult (Some _) := eq_refl ;
  opt_lift_mult None     := eq_refl .
  
Definition xframe : Type := neg_ctx * option ty .
Definition lift_xframe (s : frame) (x : xframe) : frame :=
  (fst s +▶' fst x , lift_opt (snd s) (snd x)) .
Definition mult_xframe (s : xframe) (x : xframe) : xframe :=
  (fst s +▶' fst x , mult_opt (snd s) (snd x)) .
Definition inj_frame (s : frame) : xframe := (fst s , Some (snd s)) .
Definition lift_mult_inj s x : inj_frame (lift_xframe s x) = mult_xframe (inj_frame s) x.
  cbv [lift_xframe mult_xframe]; cbn.
  rewrite opt_lift_mult.
  reflexivity.
Defined.
Equations liftP_xframe (X : psh frame) : psh xframe :=
  liftP_xframe X (Γ , None)   := T0 ;
  liftP_xframe X (Γ , Some t) := X (Γ , t) .
  

(* argument and transition for CALL *)
Definition lsn_call_qry (Γ : neg_ctx) : Type := any_s t_obs Γ .
Definition lsn_call_nxt [Γ] (a : lsn_call_qry Γ) : xframe :=
  (any_s_elim t_obs_args a , Some (any_s_elim t_obs_goal a)) .

(* argument and transition for RET *)
Definition lsn_ret_qry (x : option ty) : Type := optP a_val x .
Definition lsn_ret_nxt [x] (a : lsn_ret_qry x) : xframe :=
  (optP_elim a_cext a , None) .
  
(* argument and transition for an xframe *)
Definition lsn_qry0 (s : xframe) := lsn_call_qry (fst s) + lsn_ret_qry (snd s) .
Equations lsn_nxt0 [s] : lsn_qry0 s -> xframe :=
  lsn_nxt0 (inl o) := lsn_call_nxt o ;
  lsn_nxt0 (inr a) := lsn_ret_nxt a .

(* query, response and transition for frame *)
Definition lsn_qry (s : frame) := lsn_qry0 (inj_frame s) .
Definition lsn_rsp [s] (q : lsn_qry s) := lsn_qry0 (lsn_nxt0 q) .
Definition lsn_nxt [s] [q : lsn_qry s] (r : lsn_rsp q) : frame :=
  lift_xframe s (lsn_nxt0 r) .

Definition g_lassen : event frame frame :=
  {| qry := lsn_qry ; rsp := lsn_rsp ; nxt := lsn_nxt |}.

Definition lsn_qry' (s : xframe) := lsn_qry0 s .
Definition lsn_rsp' [s] (q : lsn_qry' s) := lsn_qry0 (lsn_nxt0 q) .
Definition lsn_nxt' [s] [q : lsn_qry' s] (r : lsn_rsp' q) : xframe :=
  mult_xframe s (lsn_nxt0 r) .
Definition g_lassen' : event xframe xframe :=
  {| qry := lsn_qry' ; rsp := lsn_rsp' ; nxt := lsn_nxt' |}.

Definition lassen : endo (psh xframe) := itree g_lassen'.
Definition lassen' : endo (psh frame) :=
  fun X => lassen (liftP_xframe X) ∘ inj_frame.

Definition lsn_ret {Γ t} (a : a_val t) : g_lassen'.(qry) (Γ , Some t)
  := inr (OptP a) .
Definition lsn_call {f : xframe} {x : ty}
           (i : fst f ∋ x) (o : t_obs (Build_sigS _ _ _ (neg_var i)))
           : g_lassen'.(qry) f :=
  inl (AnyS (var_upg i) o) .
  
Definition e_val' : frame -> Type := uncurry (e_val ∘ neg_c_coe).

Equations lassen_p_ctx {f y} (E : e_ctx' y f)
          (a : lsn_ret_qry (Some y))
          : lassen' zterm' (lift_xframe f (lsn_ret_nxt a)) :=
  lassen_p_ctx E (OptP a) := Ret (EZ (e_rename (r_concat_l _ _) E)
                                     (t_rename (r_concat_r _ _) (t_of_a a))
                                  : liftP_xframe zterm' (_ +▶' _ , Some _)) .

Equations lassen_p_sub {f : frame} {Γ : neg_ctx}
          (σ : Γ =[ e_val ]> fst f)
          (a : lsn_call_qry Γ)
           : lassen' zterm' (lift_xframe f (lsn_call_nxt a)) :=
  lassen_p_sub σ (AnyS i o) := Ret (EZ EHole (t_obs_apply o (σ _ i))
                                    : liftP_xframe zterm' (_ +▶' _ , Some _)) .

Equations lassen_enf : e_nf' ⇒ᵢ lassen' zterm' :=
  lassen_enf _ (NVal v) :=
    Vis (lsn_ret (a_of_val v))
        (λ{ | inl o => lassen_p_sub (cext_get v) o }) ;
  lassen_enf _ (NRed E i0 r) :=
    Vis (lsn_call _ (o_of_elim i0 r))
        (λ{ | inl o := lassen_p_sub (o_args_get i0 r) o ;
            | inr u := lassen_p_ctx (rew <- [fun t => e_ctx _ _ t]
                                             (o_of_elim_eq i0 r) in E)
                                     u }) .

Definition lassen_zterm : zterm' ⇒ᵢ lassen' zterm' :=
  fun j m => emb_comp (e_nf' j) (inj_frame j) (eval_enf m) !>= lassen_enf j .

Definition eval_lassen : zterm' ⇒ᵢ (lassen ∅ᵢ ∘ inj_frame).
  refine (fun j m => loop _ (inj_frame j) (m : liftP_xframe zterm' (_ , Some _))).
  intros j' x.
  destruct j'.
  cbn in x.
  destruct o.
  shelve.
  
  intros j m.
  refine (loop _ (inj_frame j) m).

  := loop lassen_zterm ∘ inj_frame.

Definition g_lassen_arr : (g_lassen' <ₑ inj_frame) ⇒ₑ (inj_frame >ₑ g_lassen).
intros j q.
refine (existT _ q (fun r => _)).
cbn; cbv [lsn_nxt].
rewrite lift_mult_inj; exact (Fib r).
Defined.

Definition g_lassen_inj : (inj_frame >ₑ g_lassen) ⇒ₑ (g_lassen' <ₑ inj_frame).
intros j q.
refine (existT _ q (fun r => _)).
cbn; cbv [lsn_nxt'].
rewrite <- lift_mult_inj; exact (Fib r).
Defined.

Definition lassen_psv : endo ()



Record multi_sq : Type := MSQ { c_in : neg_ctx ; c_out : option ty }.

Variant o_any {X : Type} (P : X -> Type) : option X -> Type :=
  | OAny {x} : P x -> o_any P (Some x)
.
Arguments OAny {X P x}.

Equations o_any_el {X P o} : @o_any X P o -> X :=
  o_any_el (@OAny X P x p) := x .

Equations o_any_coh {X P o} (a : @o_any X P o) : P (o_any_el a) :=
  o_any_coh (OAny p) := p .

Equations o_any_elim {X P} {A : forall x, P x -> Type} (f : forall x (p : P x) , A x p)
          {o} (a : @o_any X P o) : A (o_any_el a) (o_any_coh a) :=
  o_any_elim f (OAny p) := f _ p .

Equations ogs_move : multi_sq -> Type :=
  ogs_move msq := any t_obs msq.(c_in) + o_any a_val msq.(c_out) .

Equations ogs_next : forall msq, ogs_move msq -> multi_sq :=
  ogs_next msq (inl m) := MSQ (any_elim (@t_obs_args) _ m)
                              (Some (any_elim (@t_obs_goal) _ m)) ;
  ogs_next msq (inr m) := MSQ (o_any_elim (@a_cext) m) None .

Definition inn_ogs_half : half_game multi_sq multi_sq :=
  {| move := ogs_move ;
     next := ogs_next |}.

