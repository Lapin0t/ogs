From OGS Require Import Utils CatD EventD ITreeD RecD AngelicD.
Set Primitive Projections.
Set Equations Transparent.


Record ogs_spec : Type := OGS_SPEC {
  idx_p : Type ;                          (* index at player move *)
  idx_o : Type ;                          (* index at opponent move *)
  act_p : idx_p -> Type ;                 (* player actions *)
  act_o : idx_o -> Type ;                 (* opponent actions *)
  conf_p : idx_p -> Type ;                (* player states *)
  conf_o : idx_o -> Type ;                (* opponent states *)
  nxt_p : forall i, act_p i -> idx_o ;    (* player index transition *)
  nxt_o : forall i, act_o i -> idx_p ;    (* opponent index transition *)
  (* opponent state transition *)
  app_o : forall i (oa : act_o i), conf_o i -> conf_p (nxt_o i oa) ;
  (* player action computation+transition *)
  play : forall i, conf_p i -> comp ({ pa : act_p i & conf_o (nxt_p i pa) })  
}.

Section OGS.
  Variable spec : ogs_spec.

  Variant ogs_idx : Type :=
  | Player : spec.(idx_p) -> ogs_idx
  | Opponent : spec.(idx_o) -> ogs_idx
  .

  Equations ogs_conf : ogs_idx -> Type :=
    ogs_conf (Player i) := spec.(conf_p) i ;
    ogs_conf (Opponent i) := spec.(conf_o) i .

  Equations ogs_qry : ogs_idx -> Type :=
    ogs_qry (Player i) := spec.(act_p) i ;
    ogs_qry (Opponent i) := T1.

  Equations ogs_rsp i : ogs_qry i -> Type :=
    ogs_rsp (Player i)   _ := T1 ;
    ogs_rsp (Opponent i) _ := spec.(act_o) i.

  Equations ogs_nxt i (q : ogs_qry i) : ogs_rsp i q -> ogs_idx :=
    ogs_nxt (Player i)   pa   _  := Opponent (spec.(nxt_p) _ pa) ;
    ogs_nxt (Opponent i) _    oa := Player (spec.(nxt_o) _ oa) .

  Definition e_ogs : event ogs_idx ogs_idx :=
    Event ogs_qry ogs_rsp ogs_nxt.

  Definition stepP {X i} (pa : spec.(act_p) i) t : itree e_ogs X (Player i) :=
    Vis (pa : qry e_ogs (Player i)) (fun 't1_0 => t).
  Definition stepO {X i} k : itree e_ogs X (Opponent i) :=
    Vis (t1_0 : qry e_ogs (Opponent i)) k.

  Definition ogs : ogs_conf ⇒ᵢ itree e_ogs (fun _ => T0) :=
    iter (fun i =>
      match i as i return (ogs_conf i -> itree _ _ i) with
      | Player i => fun c => emb_comp _ _ (spec.(play) i c) !>= fun r =>
                         stepP (projT1 r) (Ret (inl (projT2 r)))
      | Opponent i => fun c => stepO (fun oa => Ret (inl (spec.(app_o) i oa c)))
    end).
End OGS.

From OGS Require Import LCD.
From ExtLib Require Import Data.Nat Data.Fin Data.List.
Section LC_OGS.


(* type of stuff in γ, eg types of continuations *)
Variant kont_t : Type :=
| KVal : neg_ctx -> ty -> kont_t
| KCtx : neg_ctx -> ty -> ty -> kont_t
.

(* actual stuff inside γ *)
Equations kont : kont_t -> Type :=
  kont (KVal Γ t) := e_val Γ t ;
  kont (KCtx Γ a b) := e_ctx Γ a b .

(* stuff inside γ that opponent is allowed to query *)
Variant has_obs : kont_t -> Type :=
| OCtx {Γ a b} : has_obs (KCtx Γ a b)
| OLam {Γ a b} : has_obs (KVal Γ (a → b))
.

(* wrapping kont_t to typing envs ... *)
Equations wrap_kont_t i : has_obs i -> t_env :=
  wrap_kont_t _ (@OLam Γ a b) := Γ ▶ a ,  b ;
  wrap_kont_t _ (@OCtx Γ a b) := Γ ▶ a, b .

(* ... and kont to corresponding terms *)
Equations wrap_kont i (o : has_obs i) : kont i -> term' (wrap_kont_t i o) :=
  wrap_kont _ OLam v := App (t_shift (t_of_val v)) (Var top) ;
  wrap_kont _ OCtx E := e_fill E.

Definition lc_idx_o : Type := list kont_t.      (* a list of continuation types *)
Definition lc_idx_p : Type := t_env * lc_idx_o. (* that and a ctx/ty for the focus *)

(* the player can either say that he's done or that he's stuck on a redex *)
Variant lc_act_p (γ : lc_idx_p) : Type :=
| PAns : lc_act_p γ
| PReq a b : (fst γ).(Ctx) ∋ (a =:> b) -> lc_act_p γ
.
Arguments PAns {γ}.
Arguments PReq {γ} a b i.

(* we extend the context as usual after the player move *)
(* kinda ugly using accessors instead of pattern-match, but else coq gets stuck
   in stupid annoying ways *)
Equations lc_nxt_p γ (a : lc_act_p γ) : lc_idx_o :=
  lc_nxt_p γ PAns         := KVal (fst γ).(Ctx) (fst γ).(Ty) :: snd γ ;
  lc_nxt_p γ (PReq a b i) := KCtx (fst γ).(Ctx) b (fst γ).(Ty)
                             :: KVal (fst γ).(Ctx) a :: snd γ.

(* opponent actions are an index into γ such that the pointed element actually
   has a non-trivial observation (this is just to exclude non-lambda values).
   Note that we could also add other value types that have observations, like
   negative product (two observations: fst and snd), or thunks (single
   observation: eval). 
*)
Definition lc_act_o (γ : lc_idx_o) : Type :=
  { i : fin (length γ) & has_obs (l_get γ i) }.
Definition lc_nxt_o γ (a : lc_act_o γ) : lc_idx_p :=
  (wrap_kont_t _ (projT2 a) , γ).

(* configurations *)
Definition lc_conf_o (γ : lc_idx_o) : Type := dvec kont γ.
Definition lc_conf_p (γ : lc_idx_p) : Type := term' (fst γ) * lc_conf_o (snd γ).

Definition lc_app_o γ (oa : lc_act_o γ) (c : lc_conf_o γ) : lc_conf_p (lc_nxt_o γ oa) :=
  (wrap_kont _ (projT2 oa) (d_get γ c (projT1 oa)) , c).


(* the strategy: evaluate to eager-normal-form, the constructor will give the
   move and its arguments will give the next configuration *)
Definition lc_play γ (c : lc_conf_p γ) : comp ({ pa : lc_act_p γ & lc_conf_o (lc_nxt_p γ pa) }) :=
  emb_comp _ _ (eval_enf (fst c))
  !>= fun n => match n with
            | NVal v => ret₀ (existT _ PAns (v , snd c))
            | NRed E i v => ret₀ (existT _ (PReq _ _ i) (E , (v , snd c)))
            end.

Definition lc_spec : ogs_spec :=
  OGS_SPEC lc_idx_p lc_idx_o
           lc_act_p lc_act_o
           lc_conf_p lc_conf_o
           lc_nxt_p lc_nxt_o
           lc_app_o lc_play.

End LC_OGS.
