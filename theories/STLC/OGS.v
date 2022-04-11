Set Primitive Projections.

From Coq Require Import Logic.
Import EqNotations.
Require Import Psatz.

From ExtLib.Data Require Import List Fin.

From OGS Require Import Utils.
From OGS.ITree Require Import Cat Event Dual ITree Rec Angelic Eq.
From OGS.STLC Require Import Ctx Syntax.

From Equations Require Import Equations.
Set Equations Transparent.


From OGS.ITree Require Import Eq.
From Paco Require Import paco.
Require Import Coq.Program.Equality.

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
Definition ch_vars (Γ : neg_ctx) : ch_ctx := map CIn Γ .

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

(*| The type of OGS strategies that don't return a value. |*)
Definition ogs := itree g_ogs ∅ᵢ.

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
Definition conf_pass (p : state) : Type := forall k, p.(o_ctx) ∋ k -> conf_pass_el p.(p_ctx) k .

Record conf_foc (ks : ch_ctx) : Type := ConfA {
  C_focus_t : frame ;
  C_focus_v : ch_frame_loc ks C_focus_t ;
  C_focus : eval_arg' C_focus_t ;
}.
Arguments ConfA {ks}.
Arguments C_focus_t {ks}.
Arguments C_focus_v {ks}.
Arguments C_focus {ks}.

Definition conf_act (p : state) : Type := conf_foc p.(p_ctx) * conf_pass p .

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

Notation "c ▶p d" := (conf_p_app c d) (at level 40).
Notation "c +▶p d" := (conf_p_cat c d) (at level 40).


(* create an active configuration given a passive configuration and a move on it *)
Equations? conf_p_apply {ks} (k : chan_t) (c : conf_pass_el ks k) (m : ch_move k)
          : conf_foc (ks +▶ ch_next k m) :=
  conf_p_apply (COut x) c m :=
    ConfA ((fst c.(C_chan_t) +▶ a_cext m)%ctx , snd c.(C_chan_t))
          (_ , r_concat_l _ _ _ (snd c.(C_move_v)))
          (EArg (e_rename r_concat_l' c.(C_move))
                (t_rename r_concat_r' (t_of_a m))) ;
  conf_p_apply (CIn x) c m :=
    ConfA ((c.(C_chan_t) +▶ t_obs_args m)%ctx , t_obs_goal m)
          (_ , top)
          (EArg EHole (t_obs_apply m c.(C_move))) .
all: cbv [ch_vars] in X; r_fixup.
all: destruct (concat_split _ _ X).
refine (r_concat_l _ _ _ (fst c.(C_move_v) _ h)).
refine (r_concat_r _ _ _ h).
refine (pop (r_concat_l _ _ _ (c.(C_move_v) _ h))).
refine (pop (r_concat_r _ _ _ h)).
Defined.

(* inject passive configurations into passive opponent strategies *)
Equations inj_ogs_p_aux {p} (c : conf_pass p) : passive g_ogs conf_act (s_swap p) :=
  inj_ogs_p_aux c (@Any _ _ _ k i m) :=
    (conf_p_apply k (c k i) m , (fun k i => conf_p_el_lift (c k i))).

Definition e_val' : frame -> Type := uncurry (e_val ∘ of_n_ctx).

(* create a passive configuration from a set of variables *)
Equations conf_p_vars {ks} (c : conf_foc ks)
          {Γ : neg_ctx} (f : forall x, Γ ∋ x -> e_val (fst c.(C_focus_t)) x)
          : conf_pass {| p_ctx := ks ; o_ctx := ch_vars Γ |} :=
  conf_p_vars c f k i :=
    rew has_map2 CIn _ i
    in {| C_chan_t := fst c.(C_focus_t) : chan_t_ext (CIn _) ;
          C_move_v := fst c.(C_focus_v) ;
          C_move := f _ (has_map1 _ _ i) |}.

(* create a passive configuration from an evaluation context *)
Equations conf_p_el_ctx {ks b} (c : conf_foc ks)
          : e_ctx (fst c.(C_focus_t)) (snd c.(C_focus_t)) b
            -> conf_pass_el ks (COut b) :=
  conf_p_el_ctx c e :=
    {| C_chan_t := c.(C_focus_t) : chan_t_ext (COut _);
       C_move_v := c.(C_focus_v) ;
       C_move := e |} .

(* inject normal forms into active player strategies *)
Equations inj_ogs_enf_aux {p} (c : conf_act p) : e_nf' (fst c).(C_focus_t)
                                           -> itree g_ogs (conf_act +ᵢ ∅ᵢ) p :=
  inj_ogs_enf_aux c (NVal v) :=
    Vis (Any (snd (fst c).(C_focus_v))
             (a_of_val v) : qry g_ogs _)
        (fun r =>
           Ret (inl (inj_ogs_p_aux
                       (snd c +▶p conf_p_vars _ (fun _ i => cext_get _ v i)) r))) ;

  inj_ogs_enf_aux c (NRed E i v) :=
    Vis (Any (fst (fst c).(C_focus_v) _ (map_has CIn _ (neg_upgrade i)))
             (o_of_elim i v) : qry g_ogs _)
        (fun r =>
           Ret (inl (inj_ogs_p_aux
                       (snd c
                        +▶p conf_p_vars _ (fun _ i => o_args_get _ v i)
                         ▶p conf_p_el_ctx _ (rew <- [fun t => e_ctx _ _ t]
                                             o_of_elim_eq i v in E)) r))) .

(* inject active and passive configurations into strategies *)
Definition inj_ogs_act : forall p, conf_act p -> itree g_ogs ∅ᵢ p :=
  iter (fun _ c => emb_comp _ _ (eval_enf (fst c).(C_focus))
                !>= inj_ogs_enf_aux c).

Definition inj_ogs_pass p (c : conf_pass p) : iforest g_ogs ∅ᵢ (s_swap p) :=
  fun r => inj_ogs_act _ (inj_ogs_p_aux c r).

Definition conf_start {Γ : neg_ctx} {x} (a : term Γ x)
  : conf_act (State (ch_vars Γ ▶ COut x) ∅) :=
  ({| C_focus_t := (Γ , x);
      C_focus_v := ((fun _ i => pop i) , top);
      C_focus := earg_start a |},
   (fun k (i : ∅ ∋ k) => match i with end)).  

Section composition.

Definition compat (s h f : state) :=
  s.(p_ctx) ⊎ h.(p_ctx) ≡ f.(p_ctx)
  * s.(o_ctx) ⊎ h.(o_ctx) ≡ f.(o_ctx).

Variant _compo_arg (hideₚ hideₒ fullₚ fullₒ : ch_ctx) : Type :=
| _c_ap  : ogs (State fullₚ fullₒ) -> iforest g_ogs ∅ᵢ (State hideₚ hideₒ)
         -> _compo_arg hideₚ hideₒ fullₚ fullₒ
| _c_pa : iforest g_ogs ∅ᵢ (State fullₒ fullₚ) -> ogs (State hideₒ hideₚ)
        -> _compo_arg hideₚ hideₒ fullₚ fullₒ
  .
Arguments _c_pa {hideₚ hideₒ fullₚ fullₒ} a b.
Arguments _c_ap {hideₚ hideₒ fullₚ fullₒ} a b.

Definition _compo : forall showₚ showₒ hideₚ hideₒ fullₚ fullₒ
                    , showₚ ⊎ hideₚ ≡ fullₚ
                    -> showₒ ⊎ hideₒ ≡ fullₒ
                    -> _compo_arg hideₚ hideₒ fullₚ fullₒ
                    -> ogs (State showₚ showₒ).
  cofix CIH.
  intros ? ? ? ? ? ? cₚ cₒ [a b|a b].
  - destruct (observe a).
    + destruct r.
    + exact (Tau (CIH _ _ _ _ _ _ cₚ cₒ (_c_ap t b))).
    + destruct e as [x i m].
      destruct (cover_split cₚ i) as [j|j].
      * refine (Vis (Any j m : qry g_ogs (State _ _)) (fun r => _)).
        refine (CIH _ _ _ _ _ _ _ (ext_cover_l _ cₒ)
                    (_c_ap (k (r_any (r_cover_l (ext_cover_l _ cₒ)) r)) b)).
        refine (@cat_cover _ _ _ _ ∅ _ _ cₚ _); destruct r; refine (cover_nil_r).
      * exact (Tau (CIH _ _ _ _ _ _ cₚ (ext_cover_r _ cₒ)
                        (_c_pa k (b (Any j m))))).
  - destruct (observe b).
    + destruct r.
    + exact (Tau (CIH _ _ _ _ _ _ cₚ cₒ (_c_pa a t))).
    + destruct e as [x i m].
      exact (Tau (CIH _ _ _ _ _ _ (ext_cover_r _ cₚ) cₒ
                      (_c_ap (a (Any (r_cover_r cₒ x i) m)) k))).
Defined.
Arguments _compo {_ _ _ _ _ _}.

Definition compo_ap {sₚ sₒ hₚ hₒ fₚ fₒ} (cₚ : sₚ ⊎ hₚ ≡ fₚ) (cₒ : sₒ ⊎ hₒ ≡ fₒ)
      := fun a b => _compo cₚ cₒ (_c_ap a b).

Definition compo_pa {sₚ sₒ hₚ hₒ fₚ fₒ} (cₚ : sₚ ⊎ hₚ ≡ fₚ) (cₒ : sₒ ⊎ hₒ ≡ fₒ)
      := fun a b => _compo cₚ cₒ (_c_pa a b).
Check compo_ap.

(*
Definition compo_pp {sₚ sₒ hₚ hₒ fₚ fₒ} (cₚ : sₚ ⊎ hₚ ≡ fₚ) (cₒ : sₒ ⊎ hₒ ≡ fₒ)
           (a : iforest g_ogs ∅ᵢ (State fₚ fₒ)) (b : iforest g_ogs ∅ᵢ (State hₚ hₒ))
       : iforest g_ogs ∅ᵢ (State sₚ sₒ).
  intros [x h m].
  refine (compo_ap _ _ (a _) b).
  cbn.
*)

(**********)
(* PROOFS *)
(**********)


Variant _compo_arg_eq (hideₚ hideₒ fullₚ fullₒ : ch_ctx) : Type :=
| _c_pa2 (a0 a1 : iforest g_ogs ∅ᵢ (State fullₒ fullₚ)) (b0 b1 : ogs (State hideₒ hideₚ))
  : (forall r, a0 r ≈ a1 r) -> b0 ≈ b1 -> _compo_arg_eq hideₚ hideₒ fullₚ fullₒ
| _c_ap2 (a0 a1 : ogs (State fullₚ fullₒ)) (b0 b1 : iforest g_ogs ∅ᵢ (State hideₚ hideₒ))
  : a0 ≈ a1 -> (forall r, b0 r ≈ b1 r) -> _compo_arg_eq hideₚ hideₒ fullₚ fullₒ
  .
Arguments _c_pa2 {hideₚ hideₒ fullₚ fullₒ} a0 a1 b0 b1 ea eb.
Arguments _c_ap2 {hideₚ hideₒ fullₚ fullₒ} a0 a1 b0 b1 ea eb.

Equations _c_arg_eq_l {hₚ hₒ fₚ fₒ} : _compo_arg_eq hₚ hₒ fₚ fₒ
                                    -> _compo_arg hₚ hₒ fₚ fₒ :=
  _c_arg_eq_l (_c_pa2 a0 a1 b0 b1 ea eb) := _c_pa a0 b0 ;
  _c_arg_eq_l (_c_ap2 a0 a1 b0 b1 ea eb) := _c_ap a0 b0 .

Equations _c_arg_eq_r {hₚ hₒ fₚ fₒ} : _compo_arg_eq hₚ hₒ fₚ fₒ
                                    -> _compo_arg hₚ hₒ fₚ fₒ :=
  _c_arg_eq_r (_c_pa2 a0 a1 b0 b1 ea eb) := _c_pa a1 b1 ;
  _c_arg_eq_r (_c_ap2 a0 a1 b0 b1 ea eb) := _c_ap a1 b1 .


(* bisimilarity of composition of pairwise bisimilar arguments *)
Lemma _compo_cong {sₚ sₒ hₚ hₒ fₚ fₒ} (cₚ : sₚ ⊎ hₚ ≡ fₚ) (cₒ : sₒ ⊎ hₒ ≡ fₒ)
      (a : _compo_arg_eq hₚ hₒ fₚ fₒ)
      : _compo cₚ cₒ (_c_arg_eq_l a) ≈ _compo cₚ cₒ (_c_arg_eq_r a).
  revert sₚ sₒ hₚ hₒ fₚ fₒ cₚ cₒ a.
  pcofix CIH; pstep.
  intros ? ? ? ? ? ? ? ? [ a0 a1 b0 b1 ea eb | a0 a1 b0 b1 ea eb ].
  - cbv [eqit_ observe]; cbn; cbv [observe].
    punfold eb; cbv [eqit_ observe _observe] in eb; cbn in eb.
    dependent induction eb; cbv [_observe]; try rewrite <- x0; try rewrite <- x.
    + destruct r1.
    + econstructor; right.
      refine (CIH _ _ _ _ _ _ _ _ (_c_pa2 _ _ _ _ ea _)).
      destruct REL; [exact H|destruct H].
    + destruct e.
      econstructor; right.
      refine (CIH _ _ _ _ _ _ _ _ (_c_ap2 _ _ _ _ (ea (Any _ _)) _)).
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
      refine (CIH _ _ _ _ _ _ _ _ (_c_ap2 _ _ _ _ _ eb)).
      destruct (REL); [exact H|destruct H].
    + destruct e; destruct (cover_split cₚ h).
      * econstructor; right.
        refine (CIH _ _ _ _ _ _ _ _ (_c_ap2 _ _ _ _ _ eb)).
        destruct (REL (r_any (r_cover_l (ext_cover_l _ cₒ)) v));
          [exact H|destruct H].
      * econstructor; right.
        refine (CIH _ _ _ _ _ _ _ _ (_c_pa2 _ _ _ _ _ (eb (Any _ _)))).
        intro r0; destruct (REL r0); [exact H|destruct H].
    + econstructor; auto.
      cbv [observe]; cbn; cbv [observe].
      refine (IHea CIH _ _ _ _ _ _ eq_refl eq_refl eb).
    + econstructor; auto.
      cbv [observe]; cbn; cbv [observe].
      refine (IHea CIH _ _ _ _ _ _ eq_refl eq_refl eb).
Qed.

Variant _compo_arg_assoc (hₚ hₒ iₚ iₒ fₚ fₒ : ch_ctx) : Type :=
  | _c_app : ogs (State fₚ fₒ)
             -> iforest g_ogs ∅ᵢ (State iₚ iₒ)
             -> iforest g_ogs ∅ᵢ (State hₚ hₒ)
             -> _compo_arg_assoc hₚ hₒ iₚ iₒ fₚ fₒ
  | _c_pap : iforest g_ogs ∅ᵢ (State fₒ fₚ)
             -> ogs (State iₒ iₚ)
             -> iforest g_ogs ∅ᵢ (State hₚ hₒ)
             -> _compo_arg_assoc hₚ hₒ iₚ iₒ fₚ fₒ
  | _c_ppa : iforest g_ogs ∅ᵢ (State fₒ fₚ)
             -> iforest g_ogs ∅ᵢ (State iₚ iₒ)
             -> ogs (State hₒ hₚ)
             -> _compo_arg_assoc hₚ hₒ iₚ iₒ fₚ fₒ
.

(*
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

End composition.

Definition obs_eq {Γ x} (a b : term Γ x) : Prop :=
  forall y (E : e_ctx Γ y x), eval_enf (EArg E a) ≈ eval_enf (EArg E b).

Definition ogs_eq {Γ : neg_ctx} {x} (a b : term Γ x) : Prop :=
  inj_ogs_act _ (conf_start a) ≈ inj_ogs_act _ (conf_start b).

Notation "a ≈obs b" := (obs_eq a b) (at level 40).
Notation "a ≈ogs b" := (ogs_eq a b) (at level 40).


Lemma ogs_correctness {Γ : neg_ctx} {x} (a b : term Γ x) : a ≈ogs b -> a ≈obs b.
  (*
intros H y E.
cbv [eval_enf].
pstep.
cbv [eqit_ observe]. cbv [iterₐ].
cbv [NonDep.ret bind ret pin bindₐ fib_into].
fold (fun x0 => tauₐ (@iterₐ T1 ∅ₑ (eval_arg Γ y + e_nf Γ y) (e_nf Γ y) T1_0 x0)).
Locate "=<<".
cbv [e_focus].
funelim (focus_aux.focus_aux E (inl a)).
+ cbn in *.
+ cbn.
*)
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
