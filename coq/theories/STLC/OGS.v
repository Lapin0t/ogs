Set Printing Projections.
Set Primitive Projections.

From Coq Require Import Logic.
Require Import Coq.Program.Equality.
Import EqNotations.

From ExtLib.Data Require Import List Fin.

From OGS Require Import Utils.
From OGS.ITree Require Import Cat Event Dual ITree Rec Angelic Eq.
From OGS.STLC Require Import Ctx Syntax.


From OGS.ITree Require Import Eq.
From Paco Require Import paco.
(*Require Import Coq.Program.Equality.*)
Require Import RelationClasses.

From Equations Require Import Equations.
Set Equations Transparent.

(*|

Introduction
------------

In this file, we first define an OGS arena, ie a specification
constraining the shape of OGS-like strategies, defining the abstract
states the game can be in, the allowed moves at each of these states
and the abstract state transition function.

Later, we define the proper OGS LTS, which we think of as an injection
from concrete configurations (similar to the one presented above) to
strategies over the OGS game/arena. Since this development is based on
intrinsic term typing and likewise precisely typed strategies, we will
need make variant of configurations with full typing information. We
will precisely relate our typed configuration with Jaber & Tzevelekos
configurations.

Description of the OGS game
---------------------------

Several constraints could be set on OGS strategies like innocence,
scope closing or well-bracketing. Our main game will feature none of these
constraints, describing the most general possible set of OGS-like
strategies. The game is symmetric: abstract states, moves and
transitions are the same for PLY and OPP (swapping roles after each
move), hence we will only describe half of it (from the point of view
of PLY).

Abstract states are pairs ``{ p_ctx : list chan_t ; o_ctx : list chan_t }``
where ``p_ctx`` is akin to a typing scope for channels given by OPP to PLY and
``o_ctx`` is the reverse. Channel names will be represented in typed-de-bruijn,
ie a channel name will be an indice into the scope (0 being the last
introduced channel).

A move in state ``(p_ctx , o_ctx)`` is a pair ``(i , m)`` such that:

- ``i`` is a channel in ``p_ctx`` that is ``i : p_ctx ∋ t`` where
  ``t`` is the type of the channel
- ``m`` is a channel message valid for that channel, that is
  ``m : ch_move t``

Details: channel typing
^^^^^^^^^^^^^^^^^^^^^^^

Channels are of two kinds: input channels and output channels. Things
related to channels are usually prefixed with "ch". Their set of types
is ``chan_t : Type``.

Input channels act as proxies for PLY to semantically inspect values
from OPP which he doesn't have the right to syntactically
inspect. They will accept observation queries as messages. By
definition, values which are not allowed to syntactically cross player
boundaries are values of negative types, (ie functional-esque values
like lambda abstractions). Their type is ``CIn t : chan_t`` where
``t : neg_ty``.

Output channels stand for return addresses on which PLY can respond to
a query from OPP. They will accept *abstract values*, that is the
positive fragment (also called ultimate pattern) of a value. Their
type is ``COut t : chan_t`` where ``t : ty``.

One can think of channel types as a CPS extension of negative types
where ``CIn`` is the embedding ``neg_ty ↪ chan_t`` and ``COut t``
represents ``t → ⊥`` or ``¬ t`` the dual of ``t``.
|*)
Variant chan_t : Type :=
| COut : ty -> chan_t
| CIn : neg_ty -> chan_t
.
(*| .. coq:: none |*)
Derive NoConfusion for chan_t.

(*| Channel scope: a list of channel types. |*)
Definition ch_ctx : Type := Ctx.ctx chan_t.
(*| .. coq:: none |*)
Bind Scope ctx_scope with ch_ctx.

(*| Injecting type scopes into channel scopes |*)
Definition ch_vars (Γ : neg_ctx) : ch_ctx := map CIn (ctx_s_to_ctx Γ) .
Equations eq_cong [A B : Type] (f : A -> B) [x y : A] : x = y -> f x = f y :=
  eq_cong f eq_refl := eq_refl .

Definition ch_vars_cat Γ Δ : ch_vars (Γ +▶' Δ) = (ch_vars Γ +▶ ch_vars Δ)%ctx.
  destruct Δ; dependent induction sub_elt.
  reflexivity.
  apply (eq_cong (fun Γ => (Γ ▶ CIn _)%ctx)); exact (IHsub_elt _).
Defined.
  
Definition ch_vars_elim (P : chan_t -> Type) [Γ : neg_ctx]
           (H : forall (x : neg_ty), Γ ∋ x -> P (CIn x))
  : forall k, ch_vars Γ ∋ k -> P k.
  intros k i; destruct Γ; dependent induction sub_elt.
  - dependent elimination i.
  - dependent elimination i.
    + apply H; exact top.
    + apply (IHsub_elt (fun x i => sub_prf x (pop i)) (fun x i => H x (pop i))); exact h.
Defined.

Definition ch_var_upg [Γ : neg_ctx] [x : ty] (i : Γ ∋ x) : ch_vars Γ ∋ CIn {| sub_elt := x ; sub_prf := Γ.(sub_prf) _ i |}.
  destruct Γ. dependent induction sub_elt.
  + dependent elimination i.
  + dependent elimination i.
    exact top.
    exact (pop (IHsub_elt (fun x i => sub_prf x (pop i)) _ h)).
Defined.

(*|
Details: channel messages and transitions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The set of "messages" (moves) accepted by a channel of some type is
either an abstract value (for output channels) or an observation/query
(for input channels).
|*)
Equations ch_move : chan_t -> Type :=
  ch_move (COut x) := a_val x ;
  ch_move (CIn x) := t_obs x .

(*|
The response to passing a message on some channel will be to spawn new
channels (giving them to OPP). ``ch_next`` computes the list of the new
channel types.

For an output channel ``COut t`` to which we pass an abstract value
``a``, we will give to OPP an input channel for each negative hole in
``a`` (given by ``a_cext a : neg_ctx``).

For an input channel ``CIn t`` to which we pass an observation ``o``,
we will give to OPP an input channel for each argument of the
observation and an output channel for the goal of the observation.
|*)

Equations ch_next (k : chan_t) : ch_move k -> ch_ctx :=
  ch_next (COut x) a := ch_vars (a_cext a) ;
  ch_next (CIn x) o := ch_vars (t_obs_args o) ▶ COut (t_obs_goal o) .

(*|
The type of "abstract states", that is the indices of the OGS game. We
call it ``state`` for "OGS position".
|*)
Record state : Type := State { p_ctx : ch_ctx ; o_ctx : ch_ctx }.
Definition s_swap (p : state) := {| p_ctx := p.(o_ctx) ; o_ctx := p.(p_ctx) |}.

(*|
OGS game
^^^^^^^^

With now everything in place we can define the OGS half-game and
game. ``move`` is expressed using the ``any`` combinator which lifts a
proposition to lists ("any" being the finitary "∃"). The transition
function ``next`` swaps ``i.(p_ctx)`` and ``i.(o_ctx)`` and extends
``i.(o_ctx)`` with the newly spawned channels.
|*)
Definition half_ogs : half_game state state :=
  {| move := fun s => any ch_move s.(p_ctx) ;
     next := fun s m => {| p_ctx := s.(o_ctx) +▶ any_elim ch_next s.(p_ctx) m ;
                        o_ctx := s.(p_ctx) |} |} .

Definition g_ogs : game' state state :=
  {| client := half_ogs ; server := half_ogs |}.

(*| The type of OGS strategies. |*)
Definition ogs' := itree g_ogs.
Definition ogs := ogs' ∅ᵢ.
Definition ogs_p' := iforest g_ogs.
Definition ogs_p := ogs_p' ∅ᵢ.

Definition ogs_mv {Γ Δ : ch_ctx} {k} (i : Γ ∋ k) (m : ch_move k) : qry g_ogs (State Γ Δ) := Any i m.

(*|
The OGS LTS: injecting terms into OGS strategies
------------------------------------------------

Now that the game is defined we can explain how a term gives rise to
an OGS strategy. Using ITrees, an LTS is implemented as a corecursive
function ``states → itree E ∅``. But in fact, this method can be used
to implement more general kinds of strategy families than what is
usually called an LTS. An LTS can be more precisely defined as such a
function that is "tail-corecursive".

.. note:: TODO

  Actually an LTS is more than tail-corecursive: we could have the
  additional constraint that each step only gives a single level of
  event.  This is related to the two flavors of guarded recursive
  equation systems:
  
  * ``X ⇒ itree E (X +ᵢ Y)``: multi-level, as implemented by ``iter``
  * ``X ⇒ ⟦ E ⟧ X +ᵢ Y``: single-level, not implemented

Both to make this constraint explicit and to have a clean
implementation, we will use the ITree combinator ``iter`` which
implements tail-corecursion. ``iter`` takes a family
``f : A ⇒ itree E (A +ᵢ B)`` to ``iter f : A ⇒ itree E B``, expanding
``A`` leaves of ``f`` into tail-calls of ``f``.

Typing configurations
^^^^^^^^^^^^^^^^^^^^^

In Jaber & Tzevelekos -- removing the store which is only used for
references which we don't have in our language -- the OGS LTS is
represented as such:

- passive configurations ``(π ; γ)`` which are pairs of a context
  stack ``π`` and a value store ``γ``
- active configurations ``(M ; π ; γ)`` which are triplets with first
  component an active term (also called "focus") and the rest being a
  passive configuration.

The ``π`` stack is made up of pairs ``(E, p)`` where ``E`` is an
evaluation context and ``p`` is the output channel on which we should
answer an OPP query directed at this pair. The ``γ`` store is made up
of values ``v``. There is a bijection between elements of ``π`` and
output channels given by PLY to OPP and between elements of ``γ`` and
input channels given by PLY to OPP.

Our goal here is to refine abstract states ``(p_ctx , o_ctx)`` --
which already contain some information relative to the configuration
-- with additional data to complete it into something looking like
Jaber & Tzevelekos configurations.

Passive configurations
^^^^^^^^^^^^^^^^^^^^^^

The first difference in our presentation is that ``π`` and ``γ`` are
fused into a heterogeneous list ``α`` containing values or evaluation
contexts & return channels: for each channel type ``k`` in ``o_ctx``
(channels given by PLY to OPP), we would like ``α`` to contain some
``ch_val k`` where ``ch_val : chan_t → Type`` computes the type of the
things that we need to store for that kind of channel.

Missing data ...
~~~~~~~~~~~~~~~~

But recall that values are typed as ``e_val Γ x`` where ``Γ`` is the
free variable scope and ``x`` is the type of the value, whereas an
input channel is typed as ``CIn x`` where ``x`` is the type of the
value. Looking only at the channel typing (contained in ``o_ctx``) we
are missing some data, namely ``Γ``.

Likewise contexts are typed as ``e_ctx Γ y x`` whereas output channels
are typed by ``COut x``: we are missing both the scope ``Γ`` and the
outside type ``y``.

Thus, channel typing doesn't give us enough information to express the
type of what we will put inside ``α``. Let us define the extra
information required as ``chan_t_ext : chan_t → Type``.
|*)

Equations chan_t_ext : chan_t -> Type :=
  chan_t_ext (COut x) := frame ;
  chan_t_ext (CIn x) := neg_ctx .

(*|
Now we can define ``ch_val``, taking both a channel type and the extra
typing data and returning either ``e_ctx ...`` or ``e_val ...``, ie the
syntactic data that we need to store in the configuration.
|*)
Equations ch_val (k : chan_t) : chan_t_ext k -> Type :=
  ch_val (COut x) f := e_ctx (fst f) (snd f) x ;
  ch_val (CIn x) Γ := e_val (Γ : neg_ctx) x .

(*|
Return channels and scope consistency
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

One has perhaps noticed that with ``chan_t_ext`` and ``ch_val`` we are
now expressing the full content of the old ``γ`` store, but only the
``E`` part of ``(E, p)`` pairs inside ``π``. Indeed we are missing the
name of the return channel for evaluation contexts.

These return channels arise from the fact that PLY always is trying to
reduce a term to a value and put the result in an output channel given
by OPP. When OPP makes a query on a ``CIn`` channel, the move will
give PLY some input channels for arguments and an output channel for
the result. But when OPP makes a return on a ``COut`` channel, the
move won't give PLY the output channel to continue on: the
configuration needs to remember what channel PLY was trying to respond
on when they got stuck and spawned that ``COut`` channel.

For an ``E : e_ctx Γ y x``, the return channel is thus an output
channel given by OPP to PLY of type ``COut y``, ie the type of the
exterior of ``E``. Hence the name of the return channel is an index
``r : p_ctx ∋ COut y``. We call that type ``ch_ret_loc`` for "channel
return location".
|*)

Definition ch_ret_loc (ks : ch_ctx) (x : ty) := ks ∋ COut x.

(*|
In fact this is not enough since when PLY is stuck reducing it's
focus, it needs to now how to map the free variable it is stuck on to
a ``CIn`` channel from OPP. This is not needed in Jaber & Tzevelekos
since the nominal representation of channel names an variables makes
weakening a no-op. Our de-bruijn representation needs explicit
shifting around.

Hence we will also need ``ch_vars_loc`` for these term-scope to
channel-scope renamings. We also define ``ch_frame_loc`` for a package
of a ``ch_ret_loc`` and a ``ch_vars_loc``.
|*)

Definition ch_vars_loc (ks : ch_ctx) (Γ : neg_ctx) := ch_vars Γ ⊆ ks.
Definition ch_frame_loc (ks : ch_ctx) (f : frame) :=
  ch_vars_loc ks (fst f) * ch_ret_loc ks (snd f) .

Equations ch_loc (ks : ch_ctx) (k : chan_t) : chan_t_ext k -> Type :=
  ch_loc ks (COut x) f := ch_frame_loc ks f ;
  ch_loc ks (CIn x) Γ := ch_vars_loc ks Γ.

(* configuration passive permettant de réponde à 1 unique chan_t donné
à l'opposant *)
Record conf_pass_el (ks : ch_ctx) (k : chan_t) : Type := ConfP1 {
  (* typage supplémentaire pour savoir comment continuer après *)
  C_chan_t : chan_t_ext k ;
  (* preuve que l'on peut effectivement continuer comme on veut *)
  C_move_v : ch_loc ks k C_chan_t ;
  (* soit un e_ctx soit une e_val, donnant notre stratégie *)
  C_move : ch_val k C_chan_t ;
} .
Arguments ConfP1 {ks k}.
Arguments C_chan_t {ks k}.
Arguments C_move_v {ks k}.
Arguments C_move {ks k}.

(* configuration passive: pour chaque chan_t donné à l'opposant on doit avoir
   une conf_pass_el *)
Definition conf_pass (p : state) : Type :=
  forall k, p.(o_ctx) ∋ k -> conf_pass_el p.(p_ctx) k .

Record conf_foc (ks : ch_ctx) : Type := ConfA {
  C_focus_t : frame ;
  C_focus_v : ch_frame_loc ks C_focus_t ;
  C_focus : zterm' C_focus_t ;
}.
Arguments ConfA {ks}.
Arguments C_focus_t {ks}.
Arguments C_focus_v {ks}.
Arguments C_focus {ks}.

Definition conf_act (p : state) : Type := conf_foc p.(p_ctx) * conf_pass p .
Definition C_foc {p} : conf_act p -> conf_foc p.(p_ctx) := fst.
Definition C_pass {p} : conf_act p -> conf_pass p := snd.

(* weakening the inclusion proofs for a singleton passive configuration *)
Equations ch_loc_lift {ks ks'} (k : chan_t) (e : chan_t_ext k)
  : ch_loc ks k e -> ch_loc (ks +▶ ks') k e :=
  ch_loc_lift (COut x) s v :=
    (fun _ i => r_concat_l _ _ _ (fst v _ i) ,
     r_concat_l _ _ _ (snd v)) ;
  ch_loc_lift (CIn x) s v :=
    fun _ i => r_concat_l _ _ _ (v _ i) .

Definition conf_p_el_lift {ks ks' k} (c : conf_pass_el ks k) : conf_pass_el (ks +▶ ks') k :=
  {| C_chan_t := c.(C_chan_t) ;
     C_move_v := ch_loc_lift k _ c.(C_move_v) ;
     C_move   := c.(C_move) |} .

(* append a singleton passive configuration to a passive configuration *)
Equations conf_p_app {ps k os} (c : conf_pass (State ps os)) (d : conf_pass_el ps k)
           : conf_pass (State ps (os ▶ k)%ctx) :=  
  conf_p_app c d _ top := d ;
  conf_p_app c d _ (pop i) := c _ i .

(* concatenating passive configurations (could be defined by iterating conf_p_app) *)
Definition conf_p_cat {ps os os'}
           (c : conf_pass (State ps os))
           (d : conf_pass (State ps os'))
           : conf_pass (State ps (os +▶ os')%ctx) :=  
 fun k i => match concat_split os os' i with
         | inl j => c k j
         | inr j => d k j
         end.

Notation "c ▶ₚ d" := (conf_p_app c d) (at level 40).
Notation "c +▶ₚ d" := (conf_p_cat c d) (at level 40).


(* create an active configuration given a passive configuration and a move on it *)
Equations? conf_p_apply {ks} (k : chan_t) (c : conf_pass_el ks k) (m : ch_move k)
          : conf_foc (ks +▶ ch_next k m) :=
  conf_p_apply (COut x) c m :=
    ConfA ((fst c.(C_chan_t) +▶' a_cext m) , snd c.(C_chan_t))
          (_ , r_concat_l _ _ _ (snd c.(C_move_v)))
          (EZ (e_rename (r_concat_l _ _) c.(C_move))
              (t_rename (r_concat_r _ _) (t_of_a m))) ;
  conf_p_apply (CIn x) c m :=
    ConfA ((c.(C_chan_t) +▶' t_obs_args m) , t_obs_goal m)
          (_ , top)
          (EZ EHole (t_obs_apply m c.(C_move))) .
all: rewrite ch_vars_cat in X.
all: destruct (concat_split _ _ X).
exact (r_concat_l _ _ _ (fst c.(C_move_v) _ h)).
exact (r_concat_r _ _ _ h).
exact (pop (r_concat_l _ _ _ (c.(C_move_v) _ h))).
exact (pop (r_concat_r _ _ _ h)).
Defined.

(* inject passive configurations into passive opponent strategies *)
Equations inj_ogs_p_aux {p} (c : conf_pass p) : passive g_ogs conf_act (s_swap p) :=
  inj_ogs_p_aux c (@Any _ _ _ k i m) :=
    (conf_p_apply k (c k i) m , (fun k i => conf_p_el_lift (c k i))).

(* create a passive configuration from a set of variables *)
Equations conf_p_vars {ks} (c : conf_foc ks)
          {Γ : neg_ctx} (f : forall x, Γ ∋ x -> e_val (fst c.(C_focus_t)) x)
          : conf_pass {| p_ctx := ks ; o_ctx := ch_vars Γ |} :=
  conf_p_vars c f :=
    ch_vars_elim (conf_pass_el ks)
                 (fun x i => {| C_chan_t := fst c.(C_focus_t) : chan_t_ext (CIn _) ;
                             C_move_v := fst c.(C_focus_v) ;
                             C_move := f x i |}).

(* create a passive configuration from an evaluation context *)
Equations conf_p_el_ctx {ks b} (c : conf_foc ks)
          : e_ctx (fst c.(C_focus_t)) (snd c.(C_focus_t)) b
            -> conf_pass_el ks (COut b) :=
  conf_p_el_ctx c e :=
    {| C_chan_t := c.(C_focus_t) : chan_t_ext (COut _);   (* \Delta , y *)
       C_move_v := c.(C_focus_v) ;                        (* \Delta \subseteq ks *)
       C_move := e |} .                                   (* E : \Delta |- x -o y *)

(* inject normal forms into active player strategies *)
Equations inj_ogs_enf_aux {p} (c : conf_act p) : e_nf' (C_foc c).(C_focus_t)
                                           -> itree g_ogs (conf_act +ᵢ ∅ᵢ) p :=
  inj_ogs_enf_aux c (NVal v) :=
    (* get the return channel from the config *)
    let ch_ret := snd (C_focus_v (C_foc c)) in
    (* construct new passive configs for input/value channels *)
    let cp_ext := conf_p_vars _ (fun _ i => cext_get v i) in

    Vis (ogs_mv ch_ret (a_of_val v))
        (ret ∘ inl ∘ inj_ogs_p_aux (C_pass c +▶ₚ cp_ext)) ;

  inj_ogs_enf_aux c (NRed E i v) :=
    (* get query channel by renaming [i], plus some type fixup *)
    let ch_qry := fst (C_focus_v (C_foc c)) _ (ch_var_upg i) in
    (* construct new passive configs for input/value channels *)
    let cp_ext1 := conf_p_vars _ (fun _ i => o_args_get _ v i) in
    (* construct new passive config for the output/ctx channel *)
    let cp_ext2 := conf_p_el_ctx _ (rew <- [fun t => e_ctx _ _ t]
                                          o_of_elim_eq i v in E) in

    Vis (ogs_mv ch_qry (o_of_elim i v))
        (ret ∘ inl ∘ inj_ogs_p_aux (C_pass c +▶ₚ cp_ext1 ▶ₚ cp_ext2)) .

(* inject active and passive configurations into strategies *)
Definition inj_ogs_act : conf_act ⇒ᵢ itree g_ogs ∅ᵢ :=
  iter (fun _ c => emb_comp _ _ (eval_enf (fst c).(C_focus)) !>= inj_ogs_enf_aux _).

Definition inj_ogs_pass p (c : conf_pass p) : ogs_p (s_swap p) :=
  fun r => inj_ogs_act _ (inj_ogs_p_aux c r).

Definition mk_conf_act {Γ : neg_ctx} {x} (a : zterm Γ x)
  : conf_act (State (ch_vars Γ ▶ COut x) ∅) :=
  ({| C_focus_t := (Γ , x) ;
      C_focus_v := (r_pop , top) ;
      C_focus := a |},
   (fun k (i : ∅ ∋ k) => match i with end)).

Section composition.

(*jeudi 14h*)
  
Variant _compo_arg (X : Type) (h : state) : Type :=
| _c_ap  : ogs' (fun _ => X) h -> ogs_p' (fun _ => X) h -> _compo_arg X h
| _c_pa : ogs_p' (fun _ => X) (s_swap h) -> ogs' (fun _ => X) (s_swap h) -> _compo_arg X h
  .
Arguments _c_pa {X h} a b.
Arguments _c_ap {X h} a b.

Equations _compo_body {X} : endo (forall h, _compo_arg X h -> ogs' (fun _ => X) (State ∅ ∅)) :=
  _compo_body CIH h (_c_ap a b) with observe a := {
    | RetF x := Ret (x : X) ;
    | TauF t := Tau (CIH h (_c_ap t b)) ;
    | VisF e k := Tau (CIH _ (_c_pa (k : ogs_p' _ (s_swap (State _ _))) (b e))) ;
    } ;
  _compo_body CIH h (_c_pa a b) with observe b := {
    | RetF x := Ret (x : X) ;
    | TauF t := Tau (CIH h (_c_pa a t)) ;
    | VisF e k := Tau (CIH _ (_c_ap (a e) (k : ogs_p' _ (s_swap (State _ _)))))
    }.

Definition _compo {X h} : _compo_arg X h -> ogs' (fun _ => X) (State ∅ ∅) :=
  (cofix CIH h a := _compo_body CIH h a) h.

Definition inj_ectx_barb {Γ : neg_ctx} {x y}
           (E : e_ctx Γ y x)
           (ρ : forall t, Γ ∋ t -> e_val ∅ t)
  : ogs_p' (fun _ => a_val y) (State (map CIn Γ ▶ COut x) (∅ ▶ COut y)).
  revert E ρ.
  cofix CIH.
  intros E ρ r.
  dependent elimination r.
  dependent elimination h.
  - refine (_ !>= fun m => _).
    refine (emb_comp _ _
              (eval_enf (EZ (e_rename r_concat_l' E)
                            (t_rename r_concat_r' (t_of_a c))))).
    destruct m.
    + refine (Ret (a_of_val e)).
    + 
      rewrite <- (has_map2 of_n_ty _ h) in e0.
      destruct (concat_split Γ _ (has_map1 of_n_ty _ h)).
      * Check (ρ _ h0).
        
      
      rewrite (has_map2 of_n_ty _ h).
    intros 
    
  - cbn in c.
    Check (EZ (e_rename r_concat_l' E) (t_rename r_concat_r' (t_of_a c))).
  cbn in c.
  refine (emb_comp _ _ (eval_enf (EZ (e_rename r_concat_l' E)
                   (t_rename r_concat_r' (t_of_a c)))) !>= _).
  intro e.
  refine (eval_enf (EZ ))
  cbn in r.


(*
Obligation 1.
Variant _compo_arg (X : psh state) (h f : state) : Type :=
| _c_ap  : ogs' X f -> ogs_p h -> _compo_arg X h f
| _c_pa : ogs_p' X (s_swap f) -> ogs (s_swap h) -> _compo_arg X h f
  .
Arguments _c_pa {X h f} a b.
Arguments _c_ap {X h f} a b.

(* hand eta-expanding type parameters *)
Definition _c_pa' {X} {hₚ hₒ fₚ fₒ}
           (a : ogs_p' X (State fₒ fₚ))
           (b : ogs (State hₒ hₚ))
  : _compo_arg X (State hₚ hₒ) (State fₚ fₒ)
  := _c_pa (a : ogs_p' X (s_swap (State _ _)))
           (b : ogs (s_swap (State _ _))).

Equations _compo_body {X : psh state}
  : endo (forall s h f, compat s h f -> _compo_arg X h f -> ogs' X s) :=
  _compo_body CIH s h f c (_c_ap a b) with observe a := {
    | RetF r := _ ;
    | TauF t := Tau (CIH s h f c (_c_ap t b)) ;
    | VisF (Any i m) k with cover_split (p_compat c) i := {
      | inl j := Vis (ogs_mv j m)
                     (λ{ | Any j' m' :=
                           let ρ0 := ext_cover_l _ (p_compat c) in
                           let ρ1 := ext_cover_l _ (o_compat c) in
                           CIH _ _ _
                               (mk_compat ρ0 ρ1)
                               (_c_ap (k (ogs_mv (r_cover_l ρ1 _ j') m')) b) }) ;
      | inr j := Tau (CIH _ _ _
                          (mk_compat (p_compat c) (ext_cover_r _ (o_compat c)))
                          (_c_pa' k (b (Any j m))))
      } ;
    } ;
  _compo_body CIH s h f c (_c_pa a b) with observe b := {
    | RetF r := _ ;
    | TauF t := Tau (CIH _ _ _ c (_c_pa a t)) ;
    | VisF (Any i m) k :=
      Tau (CIH _ _ _ 
               (mk_compat (ext_cover_r _ (p_compat c)) (o_compat c))
               (_c_ap (a (ogs_mv (r_cover_r (o_compat c) _ i) m)) k))
    }.
Obligation 2.

Definition _compo {X : psh state} : forall s h f, compat s h f -> _compo_arg X h f -> ogs' X s. refine (
  cofix CIH s h f c arg :=
  match arg with
  | _c_ap a b =>
      match observe a with
      | RetF r => _
      | TauF t => Tau (CIH s h f c (_c_ap t b))
      | VisF e k => match e as a return (forall r : rsp g_ogs a, _) -> _ with | Any i m =>
          match cover_split (p_compat c) i with
          | inl j => fun k => (* let the event through *)
              let ρ := ext_cover_l _ (o_compat c) in
              Vis (Any j m : qry g_ogs (State _ _))
                  (fun r => CIH
                    (State (_ +▶ _)%ctx (_ +▶ _)%ctx)
                    (State _ _)
                    (State (_ +▶ _)%ctx (_ +▶ _)%ctx )
                    (Compat _ _)
                    (*({| p_compat := ext_cover_l _ (p_compat c)
                      ; o_compat := ρ |})*)
                    (_c_ap (match r with | Any ri rm =>
                               k (Any (r_cover_l ρ _ ri) rm) end)
                           b))
          | inr j => fun k => (* synchronize the event *)
              Tau (CIH
                (State _ _)
                (State _ (_ +▶ _)%ctx)
                (State _ (_ +▶ _)%ctx)
                _(*(Compat (p_compat c) (ext_cover_r _ (o_compat c)))*)
                (_c_pa (k : ogs_p' X (s_swap (State _ _)))
                       (b (Any j m) : ogs (s_swap (State _ _)))))
          end end k
        end
  | _c_pa a b =>
      match observe b with
      | RetF r => _
      | TauF t => Tau (CIH s h f c (_c_pa a t))
      | VisF e k => (* synchronize the event *)
          Tau (CIH
            (State _ _)
            (State _ _)
            (State _ _)
            (Compat _ _) (*(Compat (ext_cover_r _ (p_compat c)) (o_compat c))*)
            (_c_ap
               match e as a return (ogs' X (State (_ +▶ any_elim _ _ a)%ctx _))
               with | Any ri rm => a (Any (r_cover_r (o_compat c) _ ri) rm) end
               k))
      end
  end).
                                                                                         shelve.
Arguments _compo {s h f}.

Definition compo_ap {s h f} (c : compat s h f) a b := _compo c (_c_ap a b).
Definition compo_pa' {s h f} (c : compat s h f) a b := _compo c (_c_pa a b).

Definition compo_pa {s h f} (c : compat s h f) (a : ogs_p f) (b : ogs h) : ogs (s_swap s) := _compo ((snd c , fst c) : compat (State _ _) (State _ _) (State _ _)) (_c_pa (a : ogs_p (s_swap (State _ _))) (b : ogs (s_swap (State _ _)))).

(*
Definition compo_pp {sₚ sₒ hₚ hₒ fₚ fₒ} (cₚ : sₚ ⊎ hₚ ≡ fₚ) (cₒ : sₒ ⊎ hₒ ≡ fₒ)
           (a : iforest g_ogs ∅ᵢ (State fₚ fₒ)) (b : iforest g_ogs ∅ᵢ (State hₚ hₒ))
       : iforest g_ogs ∅ᵢ (State sₚ sₒ).
  intros [x h m].
  refine (compo_ap _ _ (a _) b).
  cbn.
*)

*)
(**********)
(* PROOFS *)
(**********)


(*
(* CONGRUENCE OF COMPOSITION *)

Variant _compo_arg_eq (h f : state) : Type :=
| _c_pa2 (a0 a1 : ogs_p (s_swap f)) (b0 b1 : ogs (s_swap h))
  : (forall r, a0 r ≈ a1 r) -> b0 ≈ b1 -> _compo_arg_eq h f
| _c_ap2 (a0 a1 : ogs f) (b0 b1 : ogs_p h)
  : a0 ≈ a1 -> (forall r, b0 r ≈ b1 r) -> _compo_arg_eq h f
  .
Arguments _c_pa2 {h f} a0 a1 b0 b1 ea eb.
Arguments _c_ap2 {h f} a0 a1 b0 b1 ea eb.

Equations _c_arg_eq_l {h f} : _compo_arg_eq h f -> _compo_arg h f :=
  _c_arg_eq_l (_c_pa2 a0 a1 b0 b1 ea eb) := _c_pa a0 b0 ;
  _c_arg_eq_l (_c_ap2 a0 a1 b0 b1 ea eb) := _c_ap a0 b0 .

Equations _c_arg_eq_r {h f} : _compo_arg_eq h f -> _compo_arg h f :=
  _c_arg_eq_r (_c_pa2 a0 a1 b0 b1 ea eb) := _c_pa a1 b1 ;
  _c_arg_eq_r (_c_ap2 a0 a1 b0 b1 ea eb) := _c_ap a1 b1 .


(* bisimilarity of composition of pairwise bisimilar arguments *)
Lemma _compo_cong {s h f} (c : compat s h f)
      (a : _compo_arg_eq h f)
      : _compo c (_c_arg_eq_l a) ≈ _compo c (_c_arg_eq_r a).
  revert s h f c a.
  pcofix CIH; pstep.
  intros ? ? ? [cₚ cₒ] [ a0 a1 b0 b1 ea eb | a0 a1 b0 b1 ea eb ].
  - cbv [eqit_ observe]; cbn; cbv [observe].
    punfold eb; cbv [eqit_ observe _observe] in eb; cbn in eb.
    dependent induction eb; cbv [_observe]; try rewrite <- x0; try rewrite <- x.
    + destruct r1.
    + econstructor; right.
      refine (CIH _ _ _ _ (_c_pa2 _ _ _ _ ea _)).
      destruct REL; [exact H|destruct H].
    + destruct e.
      econstructor; right.
      refine (CIH _ _ _ _ (_c_ap2 _ _ _ _ (ea (Any _ _)) _)).
      intro r0; destruct (REL r0); [exact H|destruct H].
    + econstructor; auto.
      cbv [observe]; cbn; cbv [observe].
      exact (IHeb CIH _ _ _ _ _ _ ea eq_refl eq_refl).
    + econstructor; auto.
      cbv [observe]; cbn; cbv [observe].
      exact (IHeb CIH _ _ _ _ _ _ ea eq_refl eq_refl).
  - cbv [eqit_ observe]; cbn; cbv [observe].
    punfold ea; cbv [eqit_ observe _observe] in ea; cbn in ea.
    dependent induction ea; cbv [_observe]; try rewrite <- x0; try rewrite <- x.
    + destruct r1.
    + econstructor; right.
      refine (CIH _ _ _ _ (_c_ap2 _ _ _ _ _ eb)).
      destruct (REL); [exact H|destruct H].
    + destruct e; destruct (cover_split cₚ h0).
      * econstructor; right.
        refine (CIH _ _ _ _ (_c_ap2 _ _ _ _ _ eb)).
        destruct v as [? j m].
        destruct (REL (Any (r_cover_l (ext_cover_l _ cₒ) _ j) m));
          [exact H|destruct H].
      * econstructor; right.
        refine (CIH _ _ _ _ (_c_pa2 _ _ _ _ _ _)).
        intro r0; destruct (REL r0); [exact H|destruct H].
        eapply (eb (Any h1 c : s_move g_ogs (State _ _))).
    + econstructor; auto.
      cbv [observe]; cbn; cbv [observe].
      refine (IHea CIH _ _ _ _ _ _ eq_refl eq_refl eb).
    + econstructor; auto.
      cbv [observe]; cbn; cbv [observe].
      refine (IHea CIH _ _ _ _ _ _ eq_refl eq_refl eb).
Qed.

(* ASSOCIATIVITY OF COMPOSITION *)
(*
Variant _compo_arg_assoc (hₚ hₒ iₚ iₒ fₚ fₒ : ch_ctx) : Type :=
  | _c_app : ogs (State fₚ fₒ)
             -> ogs_p (State iₚ iₒ)
             -> ogs_p (State hₚ hₒ)
             -> _compo_arg_assoc hₚ hₒ iₚ iₒ fₚ fₒ
  | _c_pap : ogs_p (State fₒ fₚ)
             -> ogs (State iₒ iₚ)
             -> ogs_p (State hₚ hₒ)
             -> _compo_arg_assoc hₚ hₒ iₚ iₒ fₚ fₒ
  | _c_ppa : ogs_p (State fₒ fₚ)
             -> ogs_p (State iₚ iₒ)
             -> ogs (State hₒ hₚ)
             -> _compo_arg_assoc hₚ hₒ iₚ iₒ fₚ fₒ
.

Equations _compo_assoc_left {hₚ hₒ iₚ iₒ fₚ fₒ s1ₚ s1ₒ s2ₚ s2ₒ}
    (c1ₚ : s1ₚ ⊎ iₚ ≡ fₚ) (c1ₒ : s1ₒ ⊎ iₒ ≡ fₒ)
    (c2ₚ : s2ₚ ⊎ hₚ ≡ s1ₚ) (c2ₒ : s2ₒ ⊎ hₒ ≡ s1ₒ)
    (arg : _compo_arg_assoc hₚ hₒ iₚ iₒ fₚ fₒ)
  : ogs (State s2ₚ s2ₒ) :=
  _compo_assoc_left c1ₚ c1ₒ c2ₚ c2ₒ (_c_app a b c) :=
    _compo c2ₚ c2ₒ (_c_ap (_compo c1ₚ c1ₒ (_c_ap a b)) c) ;
  _compo_assoc_left c1ₚ c1ₒ c2ₚ c2ₒ (_c_pap a b c) :=
    _compo c2ₚ c2ₒ (_c_ap (_compo c1ₚ c1ₒ (_c_pa a b)) c) ;
  _compo_assoc_left c1ₚ c1ₒ c2ₚ c2ₒ (_c_ppa a b c) := _.
Obligation 1.
cbn.
refine (_compo c2ₚ c2ₒ (_c_pa _ c)).
refine (fun r => _compo _ _ (_c_ap (a r) b)).
cbn.
Check ()
    _compo c2ₚ c2ₒ (_c_pa (fun r => _compo c1ₚ c1ₒ (_c_pa a (b r))) c) .
*)
*)

End composition.

Definition eval_ogs {Γ : neg_ctx} {x} (a : zterm Γ x) :=
  inj_ogs_act _ (mk_conf_act a).

Equations obs_eq_aux {Γ : neg_ctx} {x} (a b : term Γ x) {y} (E : e_ctx Γ y x) : Prop :=
  obs_eq_aux a b E :=  eval_enf (EZ E a)
                     ≈ eval_enf (EZ E b) .

(*
Definition compat_nil {p} : compat (State ∅%ctx ∅%ctx) p p :=
  (cover_nil_l , cover_nil_l) .

*)
Definition ogs_eq {Γ : neg_ctx} {x} (a b : zterm Γ x) : Prop :=
  eval_ogs a ≈ eval_ogs b.

Definition cio_eq_aux {Γ : neg_ctx} {x} (a b : zterm Γ x) E : Prop :=
   _compo (_c_pa E (eval_ogs a))
 ≈ _compo (_c_pa E (eval_ogs b)).

Notation "a ≈obs b" := (forall y (E : e_ctx _ y _), obs_eq_aux a b E) (at level 40).
Notation "a ≈ogs b" := (ogs_eq a b) (at level 40).
Notation "a ≈cio b" := (forall E, cio_eq_aux a b E) (at level 40).

Definition cio_ogs_complete {Γ : neg_ctx} {x} (a b : zterm Γ x)
  : a ≈ogs b -> a ≈cio b :=
  fun H E => _compo_cong _ (_c_pa2 _ _
      (E : ogs_p (s_swap (State _ _)))
      (E : ogs_p (s_swap (State _ _)))
      (eval_ogs a : ogs (s_swap (State _ _)))
      (eval_ogs b : ogs (s_swap (State _ _)))
      (fun r => reflexivity (E r))
      H).

(* TODO: need to define the identity of composition and prove unit law
   TODO: should not be needed for correction of ogs.
Definition cio_ogs_correct {Γ : neg_ctx} {x} (a b : term Γ x)
  : a ≈cio b -> a ≈ogs b.
*)
Require Import OGS.ITree.Eq.
Require Import OGS.ITree.EqProps.

(*
Lemma ogs_focus {Γ : neg_ctx} {x} (a b : zterm Γ x) : a ≈ogs b -> eval_enf a ≈ eval_enf b.
  revert a b.
  pcofix CIH.
  intros a b H.
  cbv [ogs_eq eval_ogs inj_ogs_act eutt] in H.
  Search eq_itree.
  Check unfold_iter.
  rewrite 2 unfold_iter in H.
  cbv [iter_] in H.
  Check eval_ogs.
  fold (inj_ogs_act) in H.
  cbn in H.
  cbv [bind] in H.
  *)


Lemma cio_obs_correct {Γ : neg_ctx} {x} (a b : zterm Γ x) : a ≈cio b -> a ≈obs b.
  destruct a as [za Ea a], b as [zb Eb b].
  intros H y E.
  cbv [cio_eq_aux ogs_p iforest passive g_ogs] in H. cbn in H.
  fold g_ogs in H; fold ogs in H.
  cbv [obs_eq_aux].
  cbv [eutt] in *.
  pstep.
  cbv [eqit_ observe]. cbn.

  

Lemma ogs_correctness {Γ : neg_ctx} {x} (a b : term Γ x) (H : a ≈ogs b) : a ≈obs b.


  apply _compo_cong.
  Check _compo_cong.
  revert Γ x a b H.
  pcofix CIH.
  intros Γ x a b H E.
  

Lemma ogs_correctness {Γ : neg_ctx} {x} (a b : term Γ x) (H : a ≈ogs b) : a ≈obs b.
  intros y E.
  punfold H.
  cbn in H.
  cbv [eqit_] in H.
  cbv [observe] in H; cbn in H.
  cbv [observe] in H; cbn in H.
  cbv [observe] in H; cbn in H.
  cbv [observe] in H; cbn in H.
  cbv [observe] in H; cbn in H.
  cbv [observe] in H; cbn in H.
  cbv [observe] in H; cbn in H.
  cbv [eqit_ observe]; cbn. cbv [observe]; cbn. cbv [observe]; cbn.
  cbv [eqit_].
  intros H.
  pcofix CIH.
  Admitted.



    
(***

DEFS
norm : term -> triv-strategy (normal-form)
inj_ogs : term -> ogs-strategy

a ≈obs b := forall E, norm (E[a]) ≈ norm (E[b])
s_a ≈cio s_b := forall s_x, (s_x ∘ s_a) ≈ (s_x ∘ s_b) 

### CHEMIN 1 (peio, ≈obs est la plus grand rel compatible&adequate)

lem1 : norm a ≈ norm b -> inj_ogs a ≈ inj_ogs b

lem_joker: t diverges iff inj_ogs(t) diverges?
t ≈ spin <-> inj_ogs(t) ≈ spin
inf_ogs(t) ≈ norm(t);;?k

COEUR DE LA PREUVE:
lem2 : inj_ogs (E[t]) ≈ (inj_ogs_ctx E) ∘ (inj_ogs t)

  Preuve par coinduction.
  - inj_ogs (E[t]) calcule donc E[t] calcule donc t calcul et on case split

  Attaque: quid si
  t = E'[f v]
  inj_ogs(t) ≈ _compo (inj_ogs_ctx E', inj_ogs (f v))
  inj_ogs_ctx E ∘ inj_ogs t ≈
  inj_ogs_ctx E ∘ (inj_ogs_ctx E' ∘ inj_ogs (f v))
  ≈
  (inj_ogs_ctx E ∘ inj_ogs_ctx E') ∘ inj_ogs (f v)
  ≈ (?)
  (inj_ogs_ctx (E ∘ E')) ∘ inj_ogs (f v)

  Défense: E[E'[f v]] == E↺E'[f v]

### CHEMIN 2 (guilhem, rel CIO)











-----------
THM1 (soundness):
forall {Γ : neg_ctx} {τ} (a b : term Γ τ)
 (BIS : inj_ogs a ≈ inj_ogs b),
 a ≈obs b
Proof.



THM2 (full abstraction):
forall {Γ : neg_ctx} {τ} (a b : term Γ τ),
 a ≈obs b ->
 inj_ogs a ≈ inj_ogs b

***)

Definition g_lassen : game frame {ks : ch_ctx & forall k , ks ∋ k -> chan_t_ext k} frame.
  econstructor.
  - unshelve econstructor.
    + intros s. refine (a_val (snd s) + any t_obs (fst s)).
    + intros s [a | [y i o]].
      * refine (ch_vars (a_cext a) ,' fun k i => _).
        cbv [ch_vars] in i.
        rewrite <- (has_map2 CIn _ i).
        refine (fst s).
      * refine ((ch_vars (t_obs_args o) ▶ COut (t_obs_goal o))%ctx ,' fun k i => _).
        dependent elimination i.
        refine s.
        rewrite <- (has_map2 CIn _ h).
        cbn. refine (fst s).
  - unshelve econstructor.
    + intros s. refine (any ch_move (projT1 s)).
    + intros s [[] i m].
      * refine ((fst (projT2 s _ i) +▶ a_cext m)%ctx , snd (projT2 s _ i)).
      * refine ((projT2 s _ i +▶ t_obs_args m)%ctx , t_obs_goal m).
Defined.
Print g_lassen.
    
