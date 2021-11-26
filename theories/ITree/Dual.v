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
Record game (I J K : Type) : Type := Game {
  client : half_game I J ;
  server : half_game J K ;
}.

Definition c_move {I J K : Type} (G : game I J K) := G.(client).(move).
Definition c_next {I J K : Type} (G : game I J K) := G.(client).(next).
Definition s_move {I J K : Type} (G : game I J K) := G.(server).(move).
Definition s_next {I J K : Type} (G : game I J K) := G.(server).(next).

Definition game' I J := game I J I.

(*|
We can fuse a 2-player game into an interaction type (event) where
queries are client moves and responses are server moves. Note how the
opponent state space `J` disappears, which is why we couldn't dualize
events easily.
|*)
Definition event_of_game {I J} (G : game' I J) : event I I :=
  Event (c_move G)
        (fun i q => s_move G (c_next G i q))
        (fun i q r => s_next G _ r).
Coercion event_of_game : game' >-> event.

Definition iforest {I J} (G : game' I J) (X : I -> Type) (j : J) : Type :=
  forall q : s_move G j, itree G X (s_next G j q).

Definition dual {I J} (G : game' I J) : game' J I :=
  Game (server G) (client G).

(* Definition of lollipop. This can also be taken as the definition for the tensor
   since our dualization is clean (A ⊗ B) = (dual A ⊗ B).
   The essence is: we can either say on the output or ask on the input, and then
   the opponent will match our play to go back to the middle.
*)
Definition lollipop {I J K L} (A : game' I J) (B : game' K L)
           : game' (J * K) (I * K + J * L).
  unshelve econstructor; unshelve econstructor.
  + intros [j k]. refine (s_move A j + c_move B k)%type.
  + intros [[i k] | [j l]].
    - refine (c_move A i).
    - refine (s_move B l).
  + intros [j k] [m | m].
    - refine (inl (s_next A j m , k)).
    - refine (inr (j , c_next B k m)).
  + intros [[i k] | [j l]] m.
    - refine (c_next A i m , k).
    - refine (j , s_next B l m).
Defined.
Notation "A -o B" := (lollipop A B) (at level 30).

Definition compose_lolli {I J K L M N}
           (A : game' I J) (B : game' K L) (C : game' M N)
           {X Y Z} (f : forall j l m, X (l , m) -> Z (j , m))
           (g : forall j l m, Y (j , l) -> Z (j , m))
  : forall {j l m}, itree (B -o C) X (l , m)
  -> iforest (A -o B) Y (inr (j , l))
  -> itree (A -o C) Z (j , m).
cofix _aux.
intros j l m a b.
destruct (_observe a).
- refine (ret (f _ _ _ r)).
- refine (tau (_aux _ _ _ t b)).
- destruct e.
  + specialize (b s).
    revert j b.
    cofix _aux2.
    intros j b.
    destruct (_observe b).
    * refine (ret (g _ _ _ r)).
    * refine (tau (_aux2 _ t)).
    * destruct e.
      unshelve refine (vis _ _). refine (inl s0). refine (fun r => _aux2 _ (k0 r)).
      refine (tau (_aux _ _ _ (k c) k0)).
  + unshelve refine (vis _ _).
    * refine (inr c).
    * refine (fun r => _aux _ _ _ (k r) b).
Defined.

(****
(*|
For a game `G`, `itree G` describes *active* strategies for
*client*. Here we introduce `iforest G` which describes *passive*
strategies for *server*.

"active" means that we have the first move, "passive" that our it's our opponent
who starts.
|*)
Definition passive {I J} (H : half_game I J) (X : psh J) (i : I) : Type :=
  forall q : move H i, X (next H i q).

Definition active {I J} (H : half_game I J) (X : J -> Type) (i : I) : Type :=
  { q : move H i &  X (next H i q) }.

Definition iforest {I J} (G : game I J) (X : J -> Type) (i : I) : Type :=
  passive (client G) (itree (dual G) X) i.

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

****)
