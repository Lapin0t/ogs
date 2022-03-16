Set Primitive Projections.

From Coq Require Import Logic Program.Equality.
Import EqNotations.
Require Import Psatz.

From ExtLib.Data Require Import List Fin Bool.

From OGS Require Import Utils.
From OGS.ITree Require Import Cat Event Dual ITree Rec Angelic Eq.
From OGS.STLC Require Import Ctx Syntax.

From Equations Require Import Equations.
Set Equations Transparent.

Notation Act := (true).
Notation Pass := (false).
Notation switch := (negb).

Inductive stack : bool -> Type :=
| SNil : neg_ctx -> stack Pass
| SCon {role} : neg_ctx -> ty -> stack (switch role) -> stack role
.
Arguments SCon {role}.



(* r : parité de la stack (SNil = pair = false)
   autre: Act = je commence ; Pass = iel commence *)
Equations stack_ctx {r} : bool -> stack r -> neg_ctx :=
  stack_ctx Act  (SNil Γ)     := Γ ;
  stack_ctx Pass (SNil Γ)     := ∅%ctx ;
  stack_ctx Act  (SCon Γ x s) := stack_ctx Pass s +▶ Γ ;
  stack_ctx Pass (SCon Γ x s) := stack_ctx Act s .

Equations stack_ty {r} : stack r -> option ty :=
  stack_ty (SNil _)     := None ;
  stack_ty (SCon _ t _) := Some t .

Equations ext_head {r} : stack r -> neg_ctx -> stack r :=
  ext_head (SNil Γ)     Δ := SNil (Γ +▶ Δ) ;
  ext_head (SCon Γ x s) Δ := SCon (Γ +▶ Δ) x s .

Variant move_alt : Type :=
| RET' {x} : a_val x -> move_alt
| CALL' {x} : t_obs x -> move_alt
.
  
Variant justify {r} : stack r -> move_alt -> Type :=
| JR {Γ x s} {a : a_val x} : justify (SCon Γ x s) (RET' a)
| JC {s x} {o : t_obs x} : stack_ctx Act s ∋ x -> justify s (CALL' o)
.
Arguments JR {r Γ x s a}.
Arguments JC {r s x o} i.

Equations stack_apply {r} {s : stack r} {m : move_alt}
  : justify s m -> stack (switch r) :=
  stack_apply (@JR _ _ _ s a) := ext_head s (a_cext a) ;
  stack_apply (@JC r s _ o _) := @SCon (switch r) (t_obs_args o) (t_obs_goal o)
                                       ltac:(destruct r; exact s).

Variant enf_play (Γ : neg_ctx) : option ty -> Type :=
| RET {x} : a_val x -> enf_play Γ (Some x)
| CALL {x y} : Γ ∋ y -> t_obs y -> enf_play Γ x
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
  (*
  (Γ0 , SCon x0 (Δ0 , SNIL +++ SCon y0 (Γ1 , SCon x1 (Δ1 , SNil))))

NOUS  Γ0 ⊢ x0                ++          Γ1 ⊢ x1
EUX                Δ0 ⊢ ⊥   ++ Δ0' ⊢ y0            Δ1 ⊢ ⊥
      ^^^^^^^^^^^^^^^^^       ^^^^^^^^^^^^^^^^^^^^^^^^
        b = haut                a = bas
r = Pass = true
me = Act ; res = Pass
me = Pass ; res = Act

cas simple
      ^^^^^^^^^^^^^^^^
      ask Γ0 : push ...
   ou ret x0 : pop Γ0 ⊢ x0
               ^^^^^
               on applique sur le haut + concaténer avec bas
             == appliquer sur tout

cas compliqué
                            ^^^^^^^^^^^^^^^^^^^^^^^^^
                            ask Γ1 : push ..
                            ret x1 impossible

                                 vvvv
                  appli +  concaténer avec le haut 
              !=   appliquer push sur tout

               Γ0 ⊢ x0            ++          Γ1 ⊢ x1
Δ00 ⊢ x00               Δ0 ⊢ ⊥   ++ ∅ ⊢ y0            Δ1 ⊢ ⊥
                  
           

  

  

  
  



  Γ1 + Γ0 ⊢ x0
  Δ1 + Δ0 ⊢ y0
  Γ1 ⊢ x1
  Δ1
  *)


  Definition half_g r : half_game (stack r) (stack (switch r)) :=
    {| move := fun e => enf_play (stack_ctx Act e) (stack_ty e) ;
       next := fun e m => stack_apply e (enf_next m) |} .

  Definition game_desc : game' (stack Act) (stack Pass) :=
    {| client := half_g Act ; server := half_g Pass |}.

  Definition ogs := itree game_desc ∅ᵢ.
  Definition ogs_opp := itree (dual game_desc) ∅ᵢ.

  Equations stack_cat {r s} : stack r -> stack s -> stack (xorb r s) :=
    @stack_cat Act  Pass a (SNil Γ)     := ext_head a Γ ;
    @stack_cat Pass Pass a (SNil Γ)     := ext_head a Γ ;
    @stack_cat Act  Act  a (SCon Γ x b) := @SCon Pass Γ x (stack_cat a b) ;
    @stack_cat Act  Pass a (SCon Γ x b) := @SCon Act  Γ x (stack_cat a b) ;
    @stack_cat Pass Act  a (SCon Γ x b) := @SCon Act  Γ x (stack_cat a b) ;
    @stack_cat Pass Pass a (SCon Γ x b) := @SCon Pass Γ x (stack_cat a b) .

  Infix "s▶" := (stack_cat) (at level 40).

  Variant implyb : bool -> bool -> Type :=
    | ImpTT : implyb true true
    | ImpFA {b} : implyb false b
  .
  Notation "a =b> b" := (implyb a b) (at level 30).  

  Equations imply_refl {a} : implyb a a :=
    @imply_refl true := ImpTT ;
    @imply_refl false := ImpFA .

  Equations fix_action {a b} : a =b> b -> stack_action a -> stack_action b :=
    fix_action (ImpTT) (Pop Δ)    := Pop Δ ;
    fix_action _       (Push Δ x) := Push Δ x .

  Definition cat_head {r s} (a : stack r) (b : stack s)
    : is_some (stack_ty a) =b> is_some (stack_ty (a s▶ b)).
    dependent elimination a; [exact (ImpFA)|].
    dependent elimination b; [destruct role|destruct role,role0]; exact (ImpTT).
  Defined.

  Definition stack_cat_join {r s} me (a : stack r) (b : stack s) 
    : stack_ctx me (a s▶ b)
      = (stack_ctx (xorb s me) a +▶ stack_ctx me b)%ctx.
    funelim (a s▶ b); destruct me.
    all: cbn; try (rewrite app_assoc_reverse; f_equal); try apply H.
    all: dependent elimination a; try reflexivity; apply app_assoc_reverse.
  Defined.

  Definition stack_cat_inj_l {r s me} (a : stack r) (b : stack s) {x}
    : stack_ctx me b ∋ x -> stack_ctx me (a s▶ b) ∋ x :=
    rew <- [fun n => _ -> n ∋ _ ] stack_cat_join _ _ _
    in r_concat_r _ _ _.

  (*
  Equations stack_cat_apply_top {Γ x a} (b : stack Act) (m : stack_action true)
    : stack_apply (a s▶ @SCon Pass Γ x b) m
    = a s▶ (stack_apply (@SCon Pass Γ x b) m)
    :=
    stack_cat_apply_top (SCon _ _ _) (Pop _)    := eq_refl ;
    stack_cat_apply_top (SCon _ _ _) (Push _ _) := eq_refl .
  *)

  (*
  Equations stack_cat_apply_bot {Γ x a} (b : stack Act) (mv : stack_action false)
    : stack_apply (a s▶ @SCon Pass Γ x b) mv
    = stack_apply (@SCon Pass Γ x a) mv s▶ b
    :=
    stack_cat_apply (SCon _ _ _) (Pop _)    := eq_refl ;
    stack_cat_apply (SCon _ _ _) (Push _ _) := eq_refl .
  Check stack_cat_apply.
*)

  Variant comp_arg (s : stack Act) : Type :=
  | CompAP {e} :
        ogs e
      -> (forall r : c_move game_desc e, ogs (s s▶ c_next game_desc e r))
      -> comp_arg s
  | CompPA {e} :
      (forall r : s_move game_desc e, ogs (s_next game_desc e r))
      -> ogs (s s▶ e)
      -> comp_arg s
  .
  Arguments CompAP {s e} ply opp.
  Arguments CompPA {s e} ply opp.

  Definition split_var (a : stack Act) {r} (b : stack r) {x}
             (i : stack_ctx Act (a s▶ b) ∋ x)
             : stack_ctx (switch r) a ∋ x + stack_ctx Act b ∋ x.
    refine (concat_split _ _ _).
    destruct r; exact (rew [fun t => t ∋ _ ] stack_cat_join _ _ _ in i).
  Defined.
    
  Equations split_move (a : stack Act) (b : stack Pass)
    : c_move game_desc (a s▶ b)
      -> c_move game_desc a + s_move game_desc b :=
    split_move (SCon _ _ _) (SNil _)     (RET v) := inl (RET v) ;
    split_move (SCon _ _ _) (SCon _ _ _) (RET v) := inr (RET v) ;
    split_move a            b            (CALL i v) :=
      match (split_var a b i) with
      | inl j => inl (CALL j v)
      | inr j => inr (CALL j v)
      end.

  Definition split_resp {a : stack Act} {b : stack Pass}
     (m : c_move game_desc a + s_move game_desc b) : Type
    := match m with
      | inl m => s_move game_desc (c_next game_desc _ m)
      | inr m => c_move game_desc (s_next game_desc _ m)
      end.

  Equations split_resp_next (a : stack Act) (b : stack Pass)
            (m : c_move game_desc (a s▶ b))
            : split_resp (split_move a b m) -> stack Act :=
    split_resp_next a b m r with split_move a b m :=
      { | inl m' := stack_apply (stack_apply (a s▶ b) (fix_action (cat_head _ b)
                                                                  (enf_next m')))
                                (fix_action _ (enf_next r))
        | inr m' => a s▶ (c_next game_desc _ r) } .
  Obligation 1.
  dependent elimination a.
  dependent elimination m'.
  - dependent elimination s.
    + exact (ImpFA).
    + dependent elimination b; [|dependent induction s0]; exact imply_refl.
  - dependent elimination b; exact (imply_refl).
  Defined.

  Definition inj_split_resp (a : stack Act) (b : stack Pass)
             (c : c_move game_desc (a s▶ b)) (w : split_resp (split_move a b c))
             : fiber (s_next game_desc (c_next game_desc (a s▶ b) c))
                     (split_resp_next _ _ _ w).
    cbv [split_resp_next].
    funelim (split_move a b c); cbn in w. all: swap 3 2.
    - apply (fib_constr w).
      dependent elimination s; dependent elimination w; reflexivity.
    - dependent elimination s0; dependent elimination w.
      + apply (fib_constr (RET a)).
        dependent elimination s0; [cbn; rewrite app_assoc|]; reflexivity.
      + unshelve eapply (fib_constr (CALL _ t1)).
        exact (rew <- [fun x => (x +▶ _)%ctx ∋ _] (stack_cat_join _ _ _)
               in rew [fun x => x ∋ _] app_assoc_reverse _ _ _
               in r_concat_r _ _ _ h).
        reflexivity.
    - cbn. cbn in w; destruct (split_var (SCon n0 t s) (SNil n) i); cbn in w.
      + apply (fib_constr w); cbn.
        dependent elimination w; reflexivity.
      + dependent elimination w.
        * apply (fib_constr (RET a)). cbn. f_equal. apply app_assoc.
        * unshelve eapply (fib_constr (CALL (r_concat_r _ _ _ _) t0)).
          destruct (concat_split _ _ h0); [dependent elimination h1|exact h1].
          cbn. reflexivity.
    - cbn in w. cbn.
      destruct (split_var (SCon n0 t s) (SCon n1 t0 s0) i); cbn in w.
      all: dependent elimination w.
      1,3: apply (fib_constr (RET a)); reflexivity.
      all: unshelve eapply (fib_constr (CALL _ t1)); cbn.
      1,2: refine (rew <- [fun x => (x +▶ _)%ctx ∋ _] (stack_cat_join _ _ _) in _).
      1,2: destruct (concat_split _ _ h0); cbn.
      2,4: exact (r_concat_r _ _ _ h1).
      exact (r_concat_l _ _ _ (r_concat_l _ _ _ h1)).
      exact (r_concat_l _ _ _ (r_concat_r _ _ _ h1)).
      reflexivity.
      reflexivity.
  Defined.

  Definition compo : forall s, comp_arg s -> ogs s.
  refine (
    cofix CIH s arg :=
      match arg with
      | CompAP ply opp =>
          match observe ply with
          | RetF r => ex_falso r
          | TauF t => Tau (CIH _ (CompAP t opp))
          | VisF e k => Tau (CIH _ (CompPA k (opp e)))
          end
      | CompPA ply opp =>
          match observe opp with
          | RetF r => ex_falso r
          | TauF t => Tau (CIH _ (CompPA ply t))
          | VisF e k =>
            match split_move _ _ e as s1
            return ((forall w, fiber (s_next game_desc _)
                                (match s1 as s2 return (match s2 with
                                                        | inl m => _
                                                        | inr m => _
                                                        end -> stack Act)
                                 with
                                 | inl r => _
                                 | inr r => _
                                 end w)
                    ) -> ogs _)
            with
            | inl e' => fun f => Vis (e' : qry game_desc _) (fun r => _) (*(fib_into ogs k _ ∘ f)*)
            | inr e' => fun f => Tau (CIH _ (CompAP (ply e') (fib_into ogs k _ ∘ f)))
            end (inj_split_resp _ _ e)
          end
      end).
  
  Check f r.
  Check (CIH _ (CompPA (fun r => fib_into ogs k _ r) _)).
  Arguments compo {s}.
          
    

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
split_resp but that in concordance with the fact that the opponent to a lassen tree
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
