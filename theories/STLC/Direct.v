Set Primitive Projections.

From Coq Require Import Logic.
Import EqNotations.
Require Import Psatz.

From ExtLib.Data Require Import List Fin Bool.

From OGS Require Import Utils.
From OGS.ITree Require Import Cat Event Dual ITree Rec Angelic Eq.
From OGS.STLC Require Import Ctx Syntax.

From Equations Require Import Equations.
Set Equations Transparent.


Definition frame : Type := neg_ctx * ty.

(* CPS procrastination
Variant enf_kont : Type :=
| KCtx : neg_ctx -> ty -> ty -> enf_kont
| KVal : neg_ctx -> neg_ctx -> enf_kont
.

Variant enf_k_move : enf_kont -> Type :=
| RET {Γ s t} : a_val s -> enf_k_move (KCtx Γ s t)
| CALL {Γ Δ : neg_ctx} {s : neg_ty} : (Δ : ctx) ∋ (s : ty)
                                    -> t_obs s -> enf_k_move (KVal Γ Δ)
.

Equations enf_k_nxt {k} : enf_k_move k -> list enf_kont :=
  enf_k_nxt (@RET Γ s t v) := KVal _ (Γ +▶ a_cext v) ;
  enf_k_nxt (@CALL Γ Δ s i o) := _ .

  enf_k_move (KVal Γ Δ)   := 
*)


Variant enf_play (Γ : neg_ctx) : option ty -> Type :=
| RET {x} : a_val x -> enf_play Γ (Some x)
| CALL {x} {y : neg_ty} : (Γ : ctx) ∋ (y : ty) -> t_obs y -> enf_play Γ x
.
Arguments RET {Γ x} v.
Arguments CALL {Γ x y} i o.

Equations is_some {A} : option A -> bool :=
  is_some None     := false ;
  is_some (Some _) := true .

Variant stack_action : bool -> Type :=
| Push {b} : neg_ctx -> ty -> stack_action b
| Pop : neg_ctx -> stack_action true .

Equations enf_next {Γ x} : enf_play Γ x -> stack_action (is_some x) :=
  enf_next (RET v)    := Pop (a_cext v) ;
  enf_next (CALL i v) := Push (t_obs_args v) (t_obs_goal v) .

Module OGS.

  Inductive stack : bool -> Type :=
  | SNil : stack true
  | SCon {b} : ty -> neg_ctx * stack (negb b) -> stack b
  .
  Arguments SCon {b}.
  Definition index b := neg_ctx * stack b.

  Equations stack_ctx {b} : stack b -> neg_ctx :=
    @stack_ctx true  (SNil)                        := ∅ ;
    @stack_ctx false (SCon _ (_ , SNil))           := ∅ ;
    @stack_ctx b     (SCon _ (_ , SCon _ (Δ , s))) := stack_ctx s +▶ Δ .

  Definition index_ctx {b} (i : index b) : neg_ctx := stack_ctx (snd i) +▶ fst i.    

  (*
  Equations stack_ctx_aux : neg_ctx -> stack -> neg_ctx :=
    stack_ctx_aux Γ (SNil) := Γ ;
    stack_ctx_aux Γ (SCon _ (_ , SNil)) := Γ ;
    stack_ctx_aux Γ (SCon _ (_ , SCon _ s)) := (stack_ctx_aux (fst s) (snd s) +▶ Γ) .
*)

  Equations stack_ty {b} : index b -> option ty :=
    stack_ty (_ , SNil)   := None ;
    stack_ty (_ , SCon t _) := Some t .

  Equations ext_head {b} : index b -> neg_ctx -> index b :=
    ext_head i Δ := ((fst i +▶ Δ)%ctx , snd i) .

  Equations? stack_apply {b} (i : index b) : stack_action (is_some (stack_ty i)) -> index (negb b) :=
    @stack_apply b (Γ , SCon x s) (Pop Δ)    := ext_head s Δ ;
    @stack_apply b (Γ , SNil)     (Push Δ y) := (Δ , SCon y (Γ , _)) ;
    @stack_apply b (Γ , SCon x s) (Push Δ y) := (Δ , SCon y (Γ , SCon x _)) .
  + refine SNil.
  + rewrite Bool.negb_involutive. refine (n , s).
  Defined.

  Definition half_g b : half_game (index b) (index (negb b)) :=
    {| move := fun e => enf_play (index_ctx e) (stack_ty e) ;
       next := fun e m => stack_apply e (enf_next m) |} .

  Definition game_desc : game' (index false) (index true) :=
    {| client := half_g false ; server := half_g true |}.

  Definition ogs := itree game_desc ∅ᵢ.
  Definition ogs_opp := itree (dual game_desc) ∅ᵢ.

  (*
  Definition 
    a_s       =  T1 ;  T2 -> T3 ; []
    a_s + b_s = 'T1'-> T2 ;  T3 -> T4 ; T5 -> T6 ; []
  *)

  Equations stack_cat {b} : stack b -> stack false -> stack (negb b) :=
    stack_cat (SNil)     t := t ;
    stack_cat (SCon x s) t := SCon x (fst s , stack_cat (snd s) t) .

  Definition index_cat {b} (e : index b) (s : stack false) : index (negb b) :=
    (fst e , stack_cat (snd e) s) .

  Variant comp_arg (s : stack false) : Type :=
  | CompAP {e : index false} : ogs e
      -> (forall r : c_move game_desc e, ogs (index_cat (c_next game_desc e r) s))
      -> comp_arg s
  | CompPA {e : index true} :
      (forall r : s_move game_desc e, ogs (s_next game_desc e r))
      -> ogs (index_cat e s)
      -> comp_arg s
  .
  Arguments CompAP {s e} ply opp.
  Arguments CompPA {s e} ply opp.
  
  Equations split_var {s : index true} {t x} : index_ctx (index_cat s t) ∋ x -> index_ctx s ∋ x + index_ctx (∅%ctx, t) ∋ x :=
    @split_var (Γ , SNil)     t x i with concat_split _ _ i :=
      { | inl i := inr i ;
        | inr i := inl _ } ;
    @split_var (Γ , SCon _ (_ , SCon _ (Δ , s))) t x i with concat_split _ _ i :=
      { | inl i := @split_var (Δ , s) t x i ;
        | inr i := _ } .
  + cbn; rewrite app_nil_r; exact i.
  +  cbn in *.
  cbn in i.

  Equations? split_move {e : index true} {s} : c_move game_desc (index_cat e s) -> s_move game_desc e + c_move game_desc (∅%ctx , s) :=
    @split_move (_ , SNil)     (SCon _ _) (RET v) := inr (RET v) ;
    @split_move (_ , SCon _ _) _          (RET v) := inl (RET v) ;
    @split_move s              t          (CALL i v) := _ .
  + cbn in *; r_fixup. destruct (concat_split _ _ i) as [j|j].
    - refine (inr (CALL j v)).
    - rewrite app_nil_r; refine (inl (CALL j v)).
  + cbv [index_cat index_ctx] in i. cbn [fst snd] in i.
    refine (inr (CALL _ v)).
    
  shelve.
  cbv [index_ctx index_cat] in i. cbn[fst snd] in i.
  r_fixup.
  destruct (concat_split _ _ i).
  - shelve.
    - 


  Definition compo {e s} : comp_arg e s -> ogs (∅%ctx , s).
    revert e s.
    cofix CIH.
    intros e s [ply opp|ply opp].
    - destruct (observe ply).
      + destruct r.
      + exact (Tau (CIH _ _ (CompAP t opp))).
      + refine (Tau (CIH _ _ (CompPA k (opp e0)))).
    - destruct (observe opp).
      + destruct r.
      + exact (Tau (CIH _ _ (CompPA ply t))).
      + cbn in e0. dependent elimination e0.
        cbv
    
          Equations? split_move {e s} : c_move game_desc (index_cat e s) -> c_move game_desc e + c_move game_desc (∅%ctx , s) :=
          split
    inj_move (SCon x s) (RET v)    := RET v ;
    inj_move s          (CALL i v) := CALL _ v .
  refine (stack_ctx_top (Γ , t) i).
  cbn in i.
  refine (stack_ctx_top (Γ , t) i).

  r_fixup. cbn in i. cbv[stack_ctx_aux]. exact (r_concat_r _ _ _ i).

        cbv[rsp nxt event_of_game] in k.
        fold (event_of_game game_desc) in k.
        cbv [event_of_game game_desc half_g s_next extend] in opp. cbn in opp.
Check (opp e).
        pose (u := opp e).
        cbn in u.
        pose (u := s_next game_desc (Γ , Δ , SCon x (concat s1 s2)) e).
        fold (event_of_game game_desc) in k.
        Check (CompPA )
        fold (passive game_desc ∅ᵢ (c_next game_desc _ e)) in k.
        
        change (passive game_desc ∅ᵢ (c_next game_desc _ e)) in k.
        cbn in u.
        Check (CIH (Δ +▶ fst (enf_next e))%ctx Γ _ (stack_apply (SCon x (concat s1 s2)) (snd (enf_next e))) _ (opp e) k).
        cbn in k.
        destruct s1.
        - cbn in opp. cbn in e.
           
        dependent elimination e.
        - 
        

End OGS.

Module lassen.
  Variant request (Γ : neg_ctx) (x : ty) : Type :=
  | LRet : a_val x -> request Γ x
  | LCall : ctx_obs Γ -> request Γ x
  .

  Equations answer {Γ x} : request Γ x -> Type :=
    answer (LRet v) := ctx_obs (a_cext v) ;
    answer (LCall (CObs i o)) := a_val (t_obs_goal o) + ctx_obs (t_obs_args o) .

  Equations trans {Γ x} (r : request Γ x) : answer r -> neg_ctx * ty :=
    trans (LRet v)           (CObs i o) := ((Γ +▶ )%ctx , _) ;
    trans (LCall (CObs _ _)) (inl a) := _ ;
    trans (LCall (CObs _ _)) (inr (CObs i o)) := _ .

  (*Definition lassen_e : Event _ _ := { request answer trans }.*)


(*********************************)
(* OLD THINGS / SCRATCHPAD BELOW *)
  

(*

### G
c_mv : I -> Type                    # a_val
c_nxt {i} : c_mv i -> list I        # a_cext

c_mv' : list I -> Type := Any c_mv
c_nxt' {ii} (m : c_mv' ii) : list I * list I := c_nxt m , ii

s_mv' : list I * list I -> Type := Any (fst)
s_nxt' {ii} (m : s_mv' ii) : list I := snd ++ c_nxt m

### G
c_mv : I -> Type                    # a_val
c_nxt {i} : c_mv i -> list J        # a_cext
s_mv : J -> Type                    # ty_obs
s_nxt {j} : s_mv j -> I             # ty_obs_goal
s_ext {j} : s_mv j -> list J        # ty_obs_args

c_mv : I -> Type                    # a_val
c_nxt {i} : c_mv i -> list J        # a_cext
s_mv : J -> Type                    # ty_obs
s_nxt {j} : s_mv j -> I             # ty_obs_goal
s_ext {j} : s_mv j -> list J        # ty_obs_args
##

c_mv : list a_val' * ty -> Type
c_mv (vs, x) := Any s_mv vs + c_mv x
c_nxt {vs,x} : c_mv (vs,x) -> list a_val' * ty * ty + a_val'
c_nxt {vs,x} (inl (i,m)) := inl (s_ext m , [s_nxt m ~> x])
c_nxt {vs,x} (inr m)     := inr (x, m)

s_mv : list a_val' * ty * ty + a_val' -> Type
s_mv (inl (vs, x)) := Any s_mv vs + c_mv x
s_mv (inr v)       := s_mv v

s_mv {inl (vs, x)} (inl (i, m)) := 
s_mv {inl (vs, x)} (inr m) := 
s_mv {inr v}       m       := s_mv v

s_mv

### OGS

c_mv : list (J + I) * list (J + I) -> Type
c_mv (a,b) := Any (s_mv + c_mv) a
c_nxt {a,b} : c_mv (a,b) -> list (J + I) * list (J + I)
c_nxt {a,b} (i, inl m) := (b ++ inl (s_ext m) ++ [ inr s_nxt m ], a)
c_nxt {a,b} (i, inr m) := (b ++ inl (c_nxt m), a)

*)






(*
## Ty ⊸ Ty
c_mv : list J * I -> Type
c_mv (js,i) := Any js s_mv + c_mv i
c_nxt {js,i} : c_mv (js,i) -> I * I + list J * list J
c_nxt {js,i} (inl (v,m)) := inl (s_nxt m, i)
c_nxt {js,i} (inr m)     := inr (js, c_nxt m)

s_mv : I * I + list J * list J -> Type
s_mv (inl (i,i')) := c_mv i
s_mv (inr (js',js)) := Any js s_mv

### A
c_mv : list J * I -> Type
c_mv (js,i) := Any js s_mv + c_mv i
c_nxt {js,i} : c_mv (js,i) -> list J * I * list J * I + list J * list J
c_nxt {js,i} (inl (v,m)) := inl (s_ext m , s_nxt m , js , i)
c_nxt {js,i} (inr m)     := inr (js, c_nxt m)
s_mv : list J * I * list J * I + list J * list J -> Type
s_mv (inl (js', i', js, i)) := Any js' s_mv + c_mv i'
s_mv (inr (js, js')) := Any js' s_mv

s_nxt (inl (js', i', js, i)) (inl (v, m)) := js ++ s_ext m , s_nxt m
s_nxt (inl (js', i', js, i)) (inr m)      := js ++ c_nxt m , i
s_nxt (inr (js, js'))        (v, m) := js ++ s_ext m , s_nxt m

*)


  
Definition ty_ply_move : ty -> Type := a_val.
Definition ty_ply_nxt (x : ty) : ty_ply_move x -> neg_ctx := a_cext.
Variant ty_opp_move (Γ : neg_ctx) : Type :=
  | TObs {y : neg_ty} : (Γ : ctx) ∋ (y : ty) -> t_obs y -> ty_opp_move Γ
.


(*|
Lassen tree structure
^^^^^^^^^^^^^^^^^^^^^

ret(a, x1...xn)
                ask(xi, y1...yn)
                    






We now give the structure of Lassen trees using our itree library. Our
trees will be intrinsically typed and hence indexed by a negative
context ``Γ`` and a type ``x``.

Node shapes are as follows:
|*)

(*
stack:

ret: X
opp vals: Γ
--- P call Γ ∋ A -> B, a : a_val A
ret: B
ply vals: Δ = c_ext a
-- O call Δ ∋ C -> D, c : a_val C
ret: D
opp vals: E = Γ + c_ext c


*)

(*|
A "s_act" will be what our lassen trees will be indexed over: it is the state
of our game. It is called s_act in evocation of *stack-s_acts*.
- `f_env` are our free variables, that is what opponent has shared with us.
- `f_ret` is a description of the last stack s_act: if it is `None`
  that means there is no previous stack s_act: we can only call new
  things and not return (only opponent should ever be in this
  position). If it is `Some (Δ , x)` it means that we can return an x
  to opponent and restore his `f_env` to `Δ` (ie what we have shared
  to him).

Note that lassen trees are indexed of *s_acts* and not *stacks of
s_acts*: after a call we are forgetting where we were coming from. It might seem
weird but that in concordance with the fact that the opponent to a lassen tree
can only every query what was given last.
|*)
(*
Record enf_s_act : Type := S_Act {
  f_env : neg_ctx ;
  f_ret : option cframe
}.

(*|
Moves in the game of Lassen are of two kinds:
- `LRet`, return an abstract value in response to a call (only allowed
  if we have just been called)
- `LCal`, call (observe) an opponent name (free variable)

Note that these are both queries and responses since the Lassen game is symmetric.
More on that later.
|*)
Variant enf_move : enf_s_act -> Type :=
| LRet {Γ Δ x} : a_val x -> enf_move (S_Act Γ (Some (Δ , x)))
| LCal {Γ x y} : Γ ∋ y -> t_obs y -> enf_move (S_Act Γ x)
.
(*|
.. coq:: none
|*)
Arguments LRet {Γ Δ x}.
Arguments LCal {Γ x y}.

(*|
After a move we switch to a new s_act:
- after a return we would intuitively like to pop a s_act but we don't maintain
  a stack so we just say we're at a bottom s_act (None); still we have switched
  our opponent's env Δ into primary position and extended it with 
- 
|*)
Equations enf_next f : enf_move f -> enf_s_act :=
  enf_next _ (@LRet Γ Δ x v)   := S_Act (Δ +▶ a_cext v) None ;
  enf_next _ (@LCal Γ x y i v) :=
    let Δ := match x with Some (Δ , _) => Δ | None => ∅%ctx end in
    let (Δ', x') := t_obs_nxt v Δ
    in S_Act Δ' (Some (Γ , x')) .
*)



Variant enf_move (Γ : neg_ctx) : option ty -> Type :=
| RET {x} : a_val x -> enf_move Γ (Some x)
| CALL {x} {y : neg_ty} : (Γ : ctx) ∋ (y : ty) -> t_obs y -> enf_move Γ x
.
(*|
.. coq:: none
|*)
Derive Signature NoConfusion for enf_move.
Arguments RET {Γ x} v.
Arguments CALL {Γ x y} i o.

Definition enf_move' := uncurry enf_move.
Hint Transparent enf_move'.
Hint Transparent uncurry.

(*|
After a move we switch to a new s_act:
- after a return we would intuitively like to pop a s_act but we don't maintain
  a stack so we just say we're at a bottom s_act (None); still we have switched
  our opponent's env Δ into primary position and extended it with 
- after a call we do what the observation says (`t_obs_nxt`)
|*)

(*
Equations frame_map {A B} : (A -> B) -> frame A -> frame B :=
  frame_map f e := (fst e , f (snd e)).
*)

(*
Variant frame_action : Type :=
| FPush : frame ty -> frame_action
| FPop : neg_ctx -> frame_action
.

Equations bla_of_s_act : frame_action -> frame (option ty) :=
  bla_of_s_act (FPush (Δ , x)) := (Δ , Some x) ;
  bla_of_s_act (FPop Δ)     := (Δ , None) .

*)

Variant iopt (A : Type) : bool -> Type :=
| ISome : A -> iopt A true
| INone : iopt A false
.

Equations iopt_get {A} : iopt A true -> A :=
  iopt_get (ISome a) := a .

Equations iopt_fgt {A b} : iopt A b -> option A :=
  iopt_fgt (ISome a) := Some a ;
  iopt_fgt (INone) := None .  

Definition iframe (b : bool) : Type := neg_ctx * iopt ty b.

Variant stack_action : bool -> Type :=
| Push {b} : iframe true -> stack_action b
| Pop : neg_ctx -> stack_action true .



(*
Equations is_some {A} : option A -> bool :=
  is_some None     := false ;
  is_some (Some _) := true .


Equations enf_next Γ x : enf_move Γ x -> stack_action (is_some x) :=
  enf_next _ _ (RET v)    := Pop (a_cext v) ;
  enf_next _ _ (CALL i v) := Push (t_obs_nxt v) .

Equations apply_active {b} : frame -> stack_action b -> frame :=
  apply_active e (Pop Δ)        := ((fst e +▶ Δ)%ctx , snd e) ;
  apply_active e (Push (Δ , x)) := ((fst e +▶ Δ)%ctx , x) .

Equations apply_passive : neg_ctx -> stack_action false -> frame :=
  apply_passive Γ (Push (Δ , x)) := ((Γ +▶ Δ)%ctx , x) .

Variant passive_frame : bool -> Type :=
| PFNil : neg_ctx -> neg_ctx -> passive_frame false
| PFCon : frame -> frame -> passive_frame true
.
    
Definition lassen_g : game' frame (frame ty * frame (option ty)) :=
  {| client :=
       {| move e := enf_move (fst e) (Some (snd e)) ;
          next e m := (e , enf_next _ _ m) |} ;
     server :=
       {| move e := enf_move (fst (snd e)) (snd (snd e)) ;
          next e m := extend_env (fst e) (enf_next _ _ m) |}
  |}.

(*
Definition lassen_g : game' (frame ty) (frame ty * frame (option ty)) :=
  Game (HGame (enf_move' ∘ frame_map Some)
              (fun e => pair e ∘ (uncurry enf_next _)))
       (HGame (enf_move' ∘ snd)
              (fun e => extend_env (fst e) ∘ uncurry enf_next _)) .
*)

Definition lassen : endo (frame ty -> Type) := itree lassen_g.

Definition lassen_val {Γ : neg_ctx} {x} {y : neg_ty} (v : e_val Γ x)
           (i : (a_cext (a_of_val v) : ctx) ∋ y) (a : t_obs y)
           : lassen (eval_arg' +ᵢ ∅ᵢ) (lift_frame Γ (t_obs_nxt a))
  := Ret (inl (earg_start' (t_obs_apply a (cext_get _ v _ i)))).

Definition lassen_ectx {Γ : neg_ctx} {x y} (E : e_ctx Γ x y) (a : a_val y)
           : lassen (eval_arg' +ᵢ ∅ᵢ) ((Γ +▶ a_cext a)%ctx , x)
  := Ret (inl (@earg' _ (_ , _) (e_rename r_concat_l' E)
                                (t_rename r_concat_r' (t_of_a a)))).

Equations lassen_enf {Γ : neg_ctx} {x} (v : e_nf Γ x)
          : lassen (eval_arg' +ᵢ ∅ᵢ) (Γ , x) :=
  lassen_enf (NVal v) := Vis (RET (a_of_val v) : qry lassen_g (_ , _))
                             (λ { | CALL i a := lassen_val v i a }) ;
  lassen_enf (NRed E i r) with neg_var i := {
    lassen_enf (NRed E i (RApp v)) NArr :=
      Vis (@CALL _ _ (_ ,' NArr) i (a_of_val v) : qry lassen_g (_, _))
          (λ { | RET a := _ ;
               | CALL i a := lassen_val v i a })
    }.
Obligation 1. refine (lassen_ectx E a). Defined.

(*|
And finally we tie the knot and iterate a sequence of evaluation to
eager normal form and injection into lassen trees.
|*)
Definition eval_lassen' : eval_arg' ⇒ᵢ lassen ∅ᵢ :=
  iter (fun '(_ , _) t => emb_comp _ _ (eval_enf t) !>= lassen_enf).

(*|
And to wrap up, a cleaner interface starting with an empty evaluation context.
|*)
Definition eval_lassen {Γ : neg_ctx} {x} (u : term Γ x) : lassen ∅ᵢ (Γ , x) :=
  eval_lassen' _ (EArg EHole (u : term' (_ , _))).


(*
TODO
  1. raffiner type action stack
  2. sinon tentative pseudo cps
*)
                       
Inductive pstack : Type :=
| PNil : neg_ctx -> pstack
| PCon : frame ty -> frame ty -> pstack -> pstack
.

Equations extend_stack : pstack -> neg_ctx -> pstack :=
  extend_stack (PNil Γ) Δ := PNil (Γ +▶ Δ) ;
  extend_stack (PCon e2 e1 s) Δ := PCon ((fst e2 +▶ Δ)%ctx , snd e2) e1 s .

Definition astack : Type := frame ty * pstack.

Equations apply_action : astack -> frame (option ty) -> pstack :=
  apply_action a (Δ , None)   := extend_stack (snd a) Δ ;
  apply_action a (Δ , Some x) := PCon (Δ , x) (fst a) (snd a) .


Equations bla_of_pstack : pstack -> frame (option ty) :=
  bla_of_pstack (PNil Δ) := (Δ , None) ;
  bla_of_pstack (PCon e1 e2 s) := frame_map Some e1 .

Equations ogs_opp_nxt (i : pstack) : enf_move' (bla_of_pstack i) -> astack :=
  ogs_opp_nxt (PNil Γ)       (CALL i v) := (lift_frame Γ (t_obs_nxt v) , PNil Γ) ;
  ogs_opp_nxt (PCon e1 e2 s) (RET v)    := (((fst e2 +▶ a_cext v)%ctx , snd e2) , s) ;
  ogs_opp_nxt (PCon e1 e2 s) (CALL i v) := (lift_frame (fst e2) (t_obs_nxt v) , PCon e1 e2 s) .

Equations ogs_opp_nxt' (i : pstack) : enf_move' (bla_of_pstack i) -> astack :=
  ogs_opp_nxt' (PNil Γ)       m with enf_next _ _ m := {
    ogs_opp_nxt' (PNil Γ)       (CALL i v) (Δ , Some x) := _ ;
    ogs_opp_nxt' (PNil Γ)       (CALL i v) (Δ , None)   := _ 
                                                      } ;
  ogs_opp_nxt' (PCon e1 e2 Γ) m := _ .
Obligation 2.

Definition ogs_g : game' astack pstack := 
  {| client :=
       {| move := enf_move' ∘ frame_map Some ∘ fst;
          next e := apply_action e ∘ uncurry enf_next (frame_map Some (fst e))
       |};
     server :=
       {| move := enf_move' ∘ bla_of_pstack;
          next := ogs_opp_nxt
       |}
  |}.
Definition ogs_g : game' astack pstack.
 unshelve econstructor.
 + unshelve econstructor.
   - refine (enf_move' ∘ frame_map Some ∘ fst).
   - intros e m. refine (apply_action e (uncurry enf_next _ m)).
 + unshelve econstructor.
   - refine (enf_move' ∘ bla_of_pstack).
   - exact ogs_opp_nxt.
Defined.

Print ogs_g.
