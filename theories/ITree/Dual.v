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
Definition event_of_game {I J K} (G : game I J K) : event K I :=
  Event (c_move G)
        (fun i q => s_move G (c_next G i q))
        (fun i q r => s_next G _ r).
Coercion event_of_game : game >-> event.

Definition passive {I J} (G : game' I J) (X : I -> Type) (j : J) : Type :=
  forall q : s_move G j, X (s_next G j q).

Definition iforest {I J} (G : game' I J) (X : I -> Type) (j : J) : Type :=
  passive G (itree G X) j.

Definition dual {I J} (G : game' I J) : game' J I :=
  Game (server G) (client G).

Definition tensor {I J K L} (A : game' I J) (B : game' K L)
  : game' (I * K) (J * K + I * L) :=
{| client := {|
     move := fun ix => (c_move A (fst ix) + c_move B (snd ix))%type;
     next := fun ix c => match c with
                      | inl m => inl (c_next A (fst ix) m, snd ix)
                      | inr m => inr (fst ix, c_next B (snd ix) m)
                      end |};
   server := {|
     move := fun ix => match ix with
                   | inl ix0 => s_move A (fst ix0)
                   | inr ix0 => s_move B (snd ix0)
                   end;
     next := fun ix => match ix as s
                    return (match s with | inl _ => _ | inr _ => _ end -> I * K)
                    with
                    | inl p => fun m => (s_next A (fst p) m, snd p)
                    | inr p => fun m => (fst p , s_next B (snd p) m)
                    end |} |}.

Notation "A ⊗ B" := (tensor A B) (at level 30).

Definition lollipop {I J K L} (A : game' I J) (B : game' K L) := dual A ⊗ B.
Notation "A ⊸ B" := (lollipop A B) (at level 30).

Definition comp_arg {I J K L M N}
           (A : game' I J) (B : game' K L) (C : game' M N) X Y j m : Type :=
    ({ l : _ & ( itree (B ⊸ C) X (l , m)
               * iforest (A ⊸ B) Y (inr (j , l)))%type }
    +{ k : _ & ( iforest (B ⊸ C) X (inl (k , m))
               * itree (A ⊸ B) Y (j , k))%type }).

Definition comp {I J K L M N} {A : game' I J} {B : game' K L} {C : game' M N}
  {X Y Z} (f : forall j l m, X (l , m) -> Z (j , m)) (g : forall j l m, Y (j , l) -> Z (j , m))
  : forall {j m}, comp_arg A B C X Y j m -> itree (A ⊸ C) Z (j , m) :=
cofix _aux _ _ x :=
  match x with
  | inl (_ ,' (a , b)) =>
    match (observe a) with
    | RetF r => Ret (f _ _ _ r)
    | TauF t => Tau (_aux _ _ (inl (_ ,' (t, b))))
    | VisF e k =>
      match e as s return (forall r, itree (B ⊸ C) X (nxt (B ⊸ C) s r)) -> _ with
      | inl c => fun k => Tau (_aux _ _ (inr (_ ,' (k , b c))))
      | inr c => fun k => Vis (inr c : qry (A ⊸ C) (_ , _))
                          (fun r => _aux _ _ (inl (_ ,' (k r , b))))
      end k
    end
  | inr (_ ,' (a , b)) =>
    match (observe b) with
    | RetF r => Ret (g _ _ _ r)
    | TauF t => Tau (_aux _ _ (inr (_ ,' (a, t))))
    | VisF e k =>
      match e as s return (forall r, itree (A ⊸ B) Y (nxt (A ⊸ B) s r)) -> _ with
      | inl c => fun k => Vis (inl c : qry (A ⊸ C) (_ , _))
                          (fun r => _aux _ _ (inr (_ ,' (a , k r))))
      | inr c => fun k => Tau (_aux _ _ (inl (_ ,' (a c , k))))
      end k
    end
  end.

From OGS.ITree Require Import Eq.
From Paco Require Import paco.

(* WIP
Definition comp_assoc {I J K L M N O P}
           {A : game' I J} {B : game' K L} {C : game' M N} {D : game' O P}
           {X Y Z U V W}
           (f0 : forall l n o, X (n , o) -> U (l , o))
           (g0 : forall l m o, Y (l , m) -> U (l , o))
           (f1 : forall j l o, U (l, o) -> W (j, o))
           (g1 : forall j k o, Z (j, k) -> W (j, o))
           (f0' : forall j l m, Y (l, m) -> V (j, m))
           (g0' : forall j k m, Z (j, k) -> V (j, m))
           (f1' : forall j n o, X (n, o) -> W (j, o))
           (g1' : forall j m o, V (j, m) -> W (j, o))
           (eq0 : forall j l n o x, f1 j l o (f0 l n o x) = f1' j n o x)
           (eq1 : forall j l m o y, f1 j l o (g0 l m o y) = g1' j m o (f0' j l m y))
           (eq2 : forall j k m o z, g1 j k o z = g1' j m o (g0' j k m z))
  : forall {j o}
    ({ n : _ & ( comp_arg B C D X Y (l , o)
                 * iforest (A ⊸ B) Z (inr (j , l)))%type }
    +{ k : _ & ( iforest (C ⊸ D) X (inl (k , o))
               * comp_arg A B C Y Z (j , k))%type })

    comp f1 g1   (inl (_ ,' (comp f0 g0 (inl (_ ,' (a,  b))) , c))
  ≊ comp f1' g1' (_ ,' (a (fun q => comp f0' g0' (b q) c)).
  pcofix CIH.
  intros j l n o a b c.
  pstep.
  cbv [eqit_ observe _observe]; cbn [comp].
  cbv [observe]; cbn [_observe comp].
  cbv [observe].
  destruct (_observe a); cbn.
  + econstructor; apply eq0.
  + econstructor; right; apply CIH.
  + destruct e.
    - cbn [_observe comp]. cbv [observe].
      destruct (_observe (b c0)); cbn.
      * econstructor; apply eq1.
      * econstructor.
        cbn.
      Printing all.
    - econstructor; right; apply CIH.
  cbv [eqit_].
  cbv [ observe _observe comp].
*)
