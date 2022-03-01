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
  Notation Act := (false).
  Notation Pass := (true).
  Notation switch := (negb).

  Inductive stack : bool -> Type :=
  | SNil : stack Pass
  | SCon {role} : ty -> neg_ctx * stack (switch role) -> stack role
  .
  Arguments SCon {role}.
  Definition index b := neg_ctx * stack b.

  (*
  (Γ0 , SCon x0 (Δ0 , SCon y0 (Γ1 , SCon x1 (Δ1 , SNil))))
  Γ1 + Γ0 ⊢ x0
  Δ1 + Δ0 ⊢ y0
  Γ1 ⊢ x1
  Δ1
  *)

  Equations s_flat_ctx {r} : stack r -> list neg_ctx :=
    s_flat_ctx (SNil)           := ∅%ctx ;
    s_flat_ctx (SCon _ (Γ , s)) := (s_flat_ctx s ▶ Γ)%ctx .

  Definition i_flat_ctx {r} (a : index r) : list neg_ctx :=
    (s_flat_ctx (snd a) ▶ fst a)%ctx .

  Equations deinterlace : bool -> list neg_ctx -> list neg_ctx :=
    

  (** Get the list of context extensions for either player or opponent. *)
  Equations s_ctx {a} (r : bool) (Γ : neg_ctx) (s : stack a) : list neg_ctx by struct s :=
    s_ctx Act  Γ s := (s_ctx_aux Pass s ▶ Γ)%ctx ;
    s_ctx Pass Γ s := s_ctx_aux Act s
  with s_ctx_aux {a} (r : bool) (s : stack a) : list neg_ctx by struct s :=
    s_ctx_aux r (SNil)     := ∅%ctx ;
    s_ctx_aux r (SCon _ i) := s_ctx r (fst i) (snd i) .

  Equations i_ctx {b} (i : index b) (r : bool) : list neg_ctx :=
    i_ctx i Act := cons (fst i) (s_ctx (snd i) Act) ;
    i_ctx i Pass := s_ctx (snd i) Pass .
  Definition stack_ctx {b} (s : stack b) : neg_ctx := join (s_ctx s Act).
  Definition index_ctx {b} (s : index b) : neg_ctx := join (i_ctx s Act).

  (*
  Equations s_ctx : neg_ctx -> stack -> neg_ctx :=
    s_ctx Γ (SNil) := Γ ;
    s_ctx Γ (SCon _ (_ , SNil)) := Γ ;
    s_ctx Γ (SCon _ (_ , SCon _ s)) := (s_ctx (fst s) (snd s) +▶ Γ) .
*)

  Equations stack_ty {b} : index b -> option ty :=
    stack_ty (_ , SNil)   := None ;
    stack_ty (_ , SCon t _) := Some t .

  Equations ext_head {b} : index b -> neg_ctx -> index b :=
    ext_head i Δ := ((fst i +▶ Δ)%ctx , snd i) .

  Equations stack_apply {b} (i : index b) : stack_action (is_some (stack_ty i)) -> index (switch b) :=
    @stack_apply Pass (Γ , SCon x s)  (Pop Δ) := ext_head s Δ ;
    @stack_apply Act  (Γ , SCon x s)  (Pop Δ) := ext_head s Δ ;
    @stack_apply Pass (Γ , s)         (Push Δ y) := (Δ , @SCon Act y (Γ , s)) ;
    @stack_apply Act  (Γ , s)         (Push Δ y) := (Δ , @SCon Pass y (Γ , s)) .

  Definition half_g b : half_game (index b) (index (switch b)) :=
    {| move := fun e => enf_play (index_ctx e) (stack_ty e) ;
       next := fun e m => stack_apply e (enf_next m) |} .

  Definition game_desc : game' (index false) (index true) :=
    {| client := half_g Act ; server := half_g Pass |}.

  Definition ogs := itree game_desc ∅ᵢ.
  Definition ogs_opp := itree (dual game_desc) ∅ᵢ.

  (*
  Definition 
    a_s       =  T1 ;  T2 -> T3 ; []
    a_s + b_s =  T1 -> T2 ;  T3 -> T4 ; []

    comp =                         T4 ; []
  *)

  Equations aux_cat {r} : index Act -> neg_ctx -> stack r -> index (switch r) :=
    aux_cat t Γ (SNil)     := ext_head t Γ ;
    aux_cat t Γ (SCon x s) := (Γ , SCon x (aux_cat t (fst s) (snd s))) .

  Definition index_cat {r} (a : index Act) (b : index r) :=
    aux_cat a (fst b) (snd b) .

  (*Infix "s▶" := (stack_cat) (at level 40).*)
  Infix "i▶" := (index_cat) (at level 40).

  Definition stack_cat_join {r} s (a : index r) (b : index Act)
    :   join (i_ctx (b i▶ a) s)
        = join (i_ctx b (xorb (negb s) r) +▶ i_ctx a s)%ctx.
    cbv [index_cat i_ctx]. cbn.
    funelim (aux_cat b (fst a) (snd a)).
    + rewrite <- e. cbn.
      destruct s.
      - reflexivity.
      - cbn. exact (app_assoc_reverse _ _ _).
    + rewrite <- e. cbn.
      destruct s.
      - cbn.

  Equations stack_cat_join {r} s (a : index r) (b : index Act)
    :   join (i_ctx (b i▶ a) s)
        = join (i_ctx b (xorb (negb s) r) +▶ i_ctx a s)%ctx
               by struct a
    :=
    stack_cat_join true  (_ , SNil)                  t := eq_refl ;
    stack_cat_join false (_ , SNil)                  t := app_assoc_reverse _ _ _ ;
    stack_cat_join true  (_ , @SCon true  _ (Δ , SCon _ (_ , s))) t
      := _ ;
    stack_cat_join false (_ , @SCon true  _ (Δ , s)) t := _ ;
    stack_cat_join true  (_ , @SCon false _ (Δ , s)) t := _ ;
    stack_cat_join false (_ , @SCon false _ (Δ , s)) t := _ .
  Obligation 1.
  dependent elimination s.
  + reflexivity.
  + destruct p. cbn. refine (f_equal (fun x => x +▶ Δ)%ctx _).
    dependent elimination s. cbn.

     + cbn.
  refine (stack_cat_join _ Pass (Δ , s) t).

  dependent elimination s. destruct p.
  cbn [aux_cat]. cbn [fst snd join].
  dependent elimination s. destruct p.
  dependent elimination s.
  cbn. shelve.
  cbn.
  destruct 
  cbv beta.

  cbv [i_ctx]. cbn. 
  refine (app_assoc_reverse _ _ _).
  Search (_ +▶ (_ +▶ _)%ctx)%ctx.
 
  Search join.
  cbv [i_ctx join]


    stack_cat_join true  (_ , SNil)                  t := eq_refl ;
    stack_cat_join false (_ , SNil)                  t := eq_refl ;
    stack_cat_join true  (_ , @SCon true  _ (Δ , s)) t := f_equal (cons Δ) (stack_cat_join _ s t) ;
    stack_cat_join false (_ , @SCon true  _ (Δ , s)) t := stack_cat_join _ s t ;
    stack_cat_join true  (_ , @SCon false _ (Δ , s)) t := f_equal (cons Δ) (stack_cat_join _ s t) ;
    stack_cat_join false (_ , @SCon false _ (Δ , s)) t := stack_cat_join _ s t .

  Definition stack_cat_inj_l {a b} (t : stack Act) (s : stack a) {x}
    (i : join (s_ctx s b) ∋ x) : join (s_ctx (t s▶ s) b) ∋ x.
    rewrite stack_cat_join.
    rewrite (@join_cat _ (s_ctx t _) (s_ctx s b)).
    refine (r_concat_r _ _ _ i).
  Defined.

  Definition index_cat_join {b} (e : index b) (t : stack Act)
    : i_ctx (t i▶ e) = (s_ctx t _ +▶ i_ctx e)%ctx
    := f_equal (cons _) (stack_cat_join _ (snd e) t).

  Equations stack_cat_apply {Γ x t} (e : index Act) a
    : stack_apply (t i▶ (Γ , @SCon Pass x e)) a
      = t i▶ (stack_apply (Γ , @SCon Pass x e) a) :=
    stack_cat_apply (_ , SCon _ _) (Pop _)    := eq_refl ;
    stack_cat_apply (_ , SCon _ _) (Push _ _) := eq_refl .

  Variant comp_arg (s : stack Act) : Type :=
  | CompAP {e} :
        ogs e
      -> (forall r : c_move game_desc e, ogs (s i▶ c_next game_desc e r))
      -> comp_arg s
  | CompPA {e} :
      (forall r : s_move game_desc e, ogs (s_next game_desc e r))
      -> ogs (s i▶ e)
      -> comp_arg s
  .
  Arguments CompAP {s e} ply opp.
  Arguments CompPA {s e} ply opp.

  Definition split_var (e : index true) {t x} (i : index_ctx (t i▶ e) ∋ x)
             : index_ctx (∅%ctx , t) ∋ x + index_ctx e ∋ x
        := concat_split _ _
              (rew [fun x => x ∋ _] (join_cat _ _)
               in rew [fun x => join x ∋ _ ] index_cat_join e t
               in i).

  Equations split_move {e : index true} {s} : c_move game_desc (s i▶ e) -> c_move game_desc (∅%ctx , s) + s_move game_desc e :=
    @split_move (_ , SNil)     (SCon _ _) (RET v) := inl (RET v) ;
    @split_move (_ , SCon _ _) _          (RET v) := inr (RET v) ;
    @split_move (Γ , s)        t          (CALL i v) with split_var (Γ , s) i :=
      { | inl i := inl (CALL i v) ;
        | inr i := inr (CALL i v) } .


  Definition split_resp {e : index true} {s} (c : c_move game_desc (s i▶ e)) : Type := match split_move c with
      | inl m => s_move game_desc (c_next game_desc (∅%ctx , s) m)
      | inr m => c_move game_desc (s_next game_desc e m)
      end.
  (*Arguments split_resp /.*)

  Definition split_resp_next {e : index true} {s} (c : c_move game_desc (s i▶ e)) : split_resp c -> index Act.
    intros w. unfold split_resp in w.
    destruct (split_move c).
    - Check (s_next game_desc _ w).
    - exact (s i▶ c_next game_desc _ w).
  Defined.


  Equations inj_split_resp {e : index true} {s} (c : c_move game_desc (s i▶ e))
    (w : split_resp c) : s_move game_desc (c_next game_desc (s i▶ e) c) :=
    @inj_split_resp (_ , SNil)                        (SCon _ _) (RET v) m := m ;
    @inj_split_resp (_ , SCon _ (_ , SCon _ _))                _ (RET v) (RET w) := RET w ;
    @inj_split_resp (_ , SCon _ (_ , (SCon _ (_ , SNil))))     _ (RET v) (CALL i w) := CALL (r_concat_r _ _ _ _) w ;
    @inj_split_resp (_ , SCon _ (_ , (SCon _ (_ , SCon _ _)))) _ (RET v) (CALL i w) := CALL _ w ;
    @inj_split_resp (Γ , SNil)               t                   (CALL i v) m := _ ;
    @inj_split_resp (Γ , SCon _ (_ , _))     t                   (CALL i v) m := _ .
  Obligation 2. cbn in i; rewrite app_nil_r in i; exact i. Defined.
  Obligation 3.
  cbn in *.
  destruct (concat_split _ _ i) as [j|j].
  - destruct (concat_split _ _ j) as [k|k].
    + refine (r_concat_l _ _ _ (r_concat_l _ _ _ _)).
      refine (stack_cat_inj_l _ _ k).
    + refine (r_concat_l _ _ _ (r_concat_r _ _ _ k)).
  - refine (r_concat_r _ _ _ j).
  Defined.
  Obligation 1.
  cbv [split_resp] in m; cbn in m. cbv [split_move_clause_3] in m. cbn in m.
  destruct (split_var (Γ , SNil) i); cbn in m.
  - dependent elimination m.
    + refine (RET a).
    + refine (CALL h0 t).
  - dependent elimination m.
    + refine (RET a).
    + refine (CALL (r_concat_r _ _ _ (rew [fun x => x ∋ y] (app_nil_r _) in h0)) t).
  Defined.
  Obligation 4.
  cbv [split_resp split_move_clause_3_1] in m; cbn in m.
  dependent elimination t.
  destruct (split_var (Γ , @SCon Pass e0 (e1 , @SCon Act t0 (n , s))) i); cbn in m.
  - dependent elimination m.
    + refine (RET a).
    + refine (CALL _ t1).
      destruct p; cbn.
      destruct (concat_split _ _ h0).
      refine (r_concat_l _ _ _ (r_concat_l _ _ _ _)).
      cbn in h1.
      destruct (concat_split _ _ h1).
      refine (rew <- [fun x => join x ∋ y] (stack_cat_join Pass s (SCon t (n0 , s0))) in _).
      cbn. refine (rew <- [fun x => x ∋ y] (join_cat _ _) in _).
      refine (r_concat_l _ _ _ _).
      cbn. refine (r_concat_l _ _ _ h2).
      refine (rew <- [fun x => join x ∋ y] (stack_cat_join Pass s (SCon t (n0 , s0))) in _).
      cbn. refine (rew <- [fun x => x ∋ y] (join_cat _ _) in _).
      refine (r_concat_l _ _ _ _).
      refine (r_concat_r _ _ _ h2).
      refine (r_concat_r _ _ _ h1).
  - dependent elimination m.
    + refine (RET a).
    + refine (CALL _ t1).
      cbn in *.
      destruct (concat_split _ _ h0).
      * refine (r_concat_l _ _ _ _).
      destruct (concat_split _ _ h1).
      refine (r_concat_l _ _ _ _).
      destruct p.
      refine (rew <- [fun x => join x ∋ y] (stack_cat_join Pass s (SCon t _)) in _).
      cbn. refine (rew <- [fun x => x ∋ y] (join_cat _ _) in _).
      refine (r_concat_r _ _ _ h2).
      refine (r_concat_r _ _ _ h2).
      * refine (r_concat_r _ _ _ h1).
 Defined.

  Definition inj_split_resp_coh {e : index true} {s} (c : c_move game_desc (s i▶ e))
    (w : split_resp c) : s_next game_desc _ (inj_split_resp c w) = split_resp_next _ w.
    funelim (inj_split_resp c w); auto.
    - 
      destruct p.
      cbv [split_resp split_move] in w. cbn in w.
      cbv [split_move_clause_3] in w.

      cbv [s_next game_desc half_g next client server c_next next event_of_game]. 
      cbv [inj_split_resp enf_next]. cbn.
      cbv [split_resp_next split_move]. cbn.
      cbv [split_move_clause_3].
      revert w.
      destruct (@split_var (n, SNil) (@SCon Act t (n0, s)) y h) eqn:H; cbn in H; rewrite H; intro w.
      + dependent elimination w.
        * cbv [ext_head]; cbn. admit. (*wrong*)
        * cbv [ext_head]; cbn. cbn in h1. admit. (*wrong*)
      + dependent elimination w; reflexivity.
    -
      destruct p.
      cbv [split_resp split_move] in w. cbn in w.
      cbv [split_move_clause_3] in w.
      cbv [split_move_clause_3_1] in w.

      cbv [s_next game_desc half_g next client server c_next next event_of_game]. 
      cbv [inj_split_resp enf_next]. cbn.
      cbv [split_resp_next split_move]. cbn.
      cbv [split_move_clause_3].
      cbv [split_move_clause_3_1]. cbn.
      dependent elimination s; cbn.
      +  revert w.
        destruct (split_var (n, @SCon Pass t (n0, @SCon Act t0 (n1, s0)))) eqn:H; intro w; cbn.
         * cbv [ext_head]; cbn. cbn in w. dependent elimination w.
           cbn. admit.
           cbn. admit.
        * dependent elimination w; reflexivity.
Admitted.

(*
  n : neg_ctx
  t : ty
  n0 : neg_ctx
  s : stack (switch Act)
  y : neg_ty
  h : index_ctx (SCon t (n0, s) i▶ (n, SNil)) ∋ y
  t0 : t_obs y
  h0 : index_ctx (∅, SCon t (n0, s)) ∋ y
  H : split_var (n, SNil) h = inl h0
  a : a_val (t_obs_goal t0)
  ============================
  ((n +▶ a_cext a)%ctx, SCon t (n0, s)) = ((∅ +▶ a_cext a)%ctx, SCon t (n0, s))


  n : neg_ctx
  t : ty
  n0 : neg_ctx
  s : stack (switch Act)
  y : neg_ty
  h : index_ctx (SCon t (n0, s) i▶ (n, SNil)) ∋ y
  t0 : t_obs y
  h0 : index_ctx (∅, SCon t (n0, s)) ∋ y
  H : split_var (n, SNil) h = inl h0
  y0 : neg_ty
  h1 : (join (s_ctx s Act) +▶ n0 +▶ t_obs_args t0) ∋ y0
  t1 : t_obs y0
  ============================
  (t_obs_args t1,
  SCon (t_obs_goal t1) (t_obs_args t0, SCon (t_obs_goal t0) (n, SCon t (n0, s)))) =
  (t_obs_args t1,
  SCon (t_obs_goal t1) (t_obs_args t0, SCon (t_obs_goal t0) (∅%ctx, SCon t (n0, s))))


  n : neg_ctx
  t : ty
  n0 : neg_ctx
  t0 : ty
  n1 : neg_ctx
  s0 : stack (switch Act)
  t2 : ty
  p : neg_ctx * stack (switch Act)
  y : neg_ty
  h : index_ctx (SCon t2 p i▶ (n, SCon t (n0, SCon t0 (n1, s0)))) ∋ y
  t1 : t_obs y
  h0 : index_ctx (∅, SCon t2 p) ∋ y
  H : split_var (n, SCon t (n0, SCon t0 (n1, s0))) h = inl h0
  a : a_val (t_obs_goal t1)
  ============================
  ((n +▶ a_cext a)%ctx, SCon t (n0, SCon t0 (n1, SCon t2 p s▶ s0))) =
  ((∅ +▶ a_cext a)%ctx, SCon t2 p)


  n : neg_ctx
  t : ty
  n0 : neg_ctx
  t0 : ty
  n1 : neg_ctx
  s0 : stack (switch Act)
  t2 : ty
  p : neg_ctx * stack (switch Act)
  y : neg_ty
  h : index_ctx (SCon t2 p i▶ (n, SCon t (n0, SCon t0 (n1, s0)))) ∋ y
  t1 : t_obs y
  h0 : index_ctx (∅, SCon t2 p) ∋ y
  H : split_var (n, SCon t (n0, SCon t0 (n1, s0))) h = inl h0
  y0 : neg_ty
  h1 : (join
          ((let (n, s) := p in
            fun b : bool => if b then s_ctx s Act ▶ n else s_ctx s Pass) Pass) +▶
        t_obs_args t1) ∋ y0
  t3 : t_obs y0
  ============================
  (t_obs_args t3, SCon (t_obs_goal t3)
                       (t_obs_args t1, SCon (t_obs_goal t1)
                                            (n, SCon t (n0, SCon t0 (n1, SCon t2 p s▶ s0))))) =
  (t_obs_args t3, SCon (t_obs_goal t3)
                       (t_obs_args t1, SCon (t_obs_goal t1)
                                            (∅%ctx, SCon t2 p)))


*)


  Definition inj_split_resp_good {e : index true} {s} (c : c_move game_desc (s i▶ e))
            (w : split_resp c)
            : fiber (s_next game_desc (c_next game_desc (s i▶ e) c))
                                      (split_resp_next _ w) :=
  fib_constr _ _ (inj_split_resp_coh c w).


  Definition compo : forall s, comp_arg s -> ogs (∅%ctx , s) :=
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
            match split_move e as s1
            return ((forall w, fiber (s_next game_desc _)
                                (match s1 as s2 return (match s2 with
                                                        | inl m => _
                                                        | inr m => _
                                                        end -> index Act)
                                 with
                                 | inl r => fun w => s_next game_desc _ w
                                 | inr r => fun w => index_cat s (c_next game_desc _ w)
                                 end w)
                    ) -> ogs (_ , _))
            with
            | inl e' => fun f => Vis (e' : qry game_desc (_ , _)) (fib_into ogs k _ ∘ f)
            | inr e' => fun f => Tau (CIH _ (CompAP (ply e') (fib_into ogs k _ ∘ f)))
            end (inj_split_resp_good e)
          end
      end.
  Arguments compo {s}.
          
    
  (*
  Definition s_unit : stack Act := @SCon Act Unit (∅%ctx , SNil).
  Definition app_unit {b} (s : index b) : index (switch b) :=
    s_unit i▶ s.

  Variant comp_arg_simple  : Type :=
  | CompAP {e} :
        ogs e
      -> (forall r : c_move game_desc e, ogs (app_unit (c_next game_desc e r)))
      -> comp_arg_simple
  | CompPA {e} :
      (forall r : s_move game_desc e, ogs (s_next game_desc e r))
      -> ogs (app_unit e)
      -> comp_arg_simple
  .
  Arguments CompAP {e} ply opp.
  Arguments CompPA {e} ply opp.

  Definition split_var (e : index true) {x} (i : index_ctx (app_unit e) ∋ x)
             : index_ctx (∅%ctx , s_unit) ∋ x + index_ctx e ∋ x
        := concat_split _ _
              (rew [fun x => x ∋ _] (join_cat _ _)
               in rew [fun x => join x ∋ _ ] index_cat_join e s_unit
               in i).

  Definition compo : comp_arg_simple -> ogs (∅%ctx , s_unit).
    cofix CIH.
    intros [e ply opp|e ply opp].
    - destruct (observe ply).
      + destruct r.
      + exact (Tau (CIH (CompAP t opp))).
      + exact (Tau (CIH (CompPA k (opp e0)))).
    - destruct (observe opp).
      + destruct r.
      + exact (Tau (CIH (CompPA ply t))).
      + 
        destruct (split_move e0) eqn:H.
        * refine (Vis (c : qry game_desc _) (fun r => _)).
          cbv [game_desc half_g s_move c_move move server client c_next next event_of_game rsp] in r.
          cbv [game_desc half_g nxt rsp event_of_game s_move s_next next c_move c_next move client server] in k.
          admit.
        * refine (Tau (CIH _ (CompAP (ply s0) (fun r => _)))).
          admit.
  Admitted.
        

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
