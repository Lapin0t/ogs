(*|
A development on duality for interaction structures.

As `event`s describe some interaction type with questions and answers, we'd
hope to be able to describe the *dual* interaction type, that is the one
where roles (questioning and answering) are reversed.
|*)
Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

(*From ExtLib.Data Require Import Nat Fin List Unit.*)

From OGS Require Import Utils.
From OGS.ITree Require Import Event ITree Angelic Rec.

(*|
Dualization of an interaction is intuitively described as reversing *roles*,
as such we'll have to describe what that role is: we call it a
half-game. `I` (resp. `J`) are player (resp. opponent) states; `moves` and `next`
describe what moves can be made to change from a player state to an opponent state.
|*)
Record half_game (I J : Type) : Type := HGame {
  move : I -> Type ;
  next : forall i, move i -> J ;
}.

(*| A 2-player game is then simply two half-games with matching state-space. |*)
Record game (I J : Type) : Type := Game {
  client : half_game I J ;
  server : half_game J I ;
}.

Definition c_move {I J : Type} (G : game I J) := G.(client).(move).
Definition c_next {I J : Type} (G : game I J) := G.(client).(next).
Definition s_move {I J : Type} (G : game I J) := G.(server).(move).
Definition s_next {I J : Type} (G : game I J) := G.(server).(next).

Definition dual {I J} (G : game I J) : game J I :=
  Game (server G) (client G).

(*|
We can fuse a 2-player game into an interaction type (event) where
queries are client moves and responses are server moves. Note how the
opponent state space `J` disappears, which is why we couldn't dualize
events easily.
|*)
Definition event_of_game {I J} (G : game I J) : event I I :=
  Event (c_move G)
        (fun i q => s_move G (c_next G i q))
        (fun i q r => s_next G _ r).
Coercion event_of_game : game >-> event.

(*|
For a game `G`, `itree G` describes *active* strategies for
*client*. Here we introduce `iforest G` which describes *passive*
strategies for *server*.

"active" means that we have the first move, "passive" that our it's our opponent
who starts.
|*)
Definition iforest {I J} (G : game I J) (X : J -> Type) (i : I) : Type :=
  forall q : c_move G i, itree (dual G) X (c_next G i q).

(*|
Parallel composition: because of clean dualization we can now "zip" an
active strategy for a client together with a passive strategy for a
server. This yields a computation.
|*)
Definition compose {I J} (G : game I J) {X : (I + J)%type -> Type}
  : forall i, itree G (X ∘ inl) i
    -> iforest G (X ∘ inr) i
    -> computation ({ a : (I + J) & X a }) :=
  cofix _comp i ply opp :=
    match (_observe ply) with
    | RetF r => NonDep.ret (inl i ,' r )
    | TauF t => NonDep.tau (_comp i t opp)
    | VisF e_c k_c =>
      (cofix _aux (opp : itree (dual G) (X ∘ inr) _) :=
         match (_observe opp) with
         | RetF r => NonDep.ret (inr _ ,' r)
         | TauF t => NonDep.tau (_aux t)
         | VisF e_s k_s => NonDep.tau (_comp _ (k_c e_s) k_s)
         end) (opp e_c)
    end.
