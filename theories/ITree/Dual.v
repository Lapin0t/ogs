(*|
A development on duality for interaction structures.

As `event`s describe some interaction type with questions and answers, we'd
hope to be able to describe the *dual* interaction type, that is the one
where roles (questioning and answering) are reversed.
|*)
Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.
From Equations Require Import Equations.
Set Equations Transparent.

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

Definition parallel {I J K L} (A : game' I J) (B : game' K L)
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

Notation "A ⅋ B" := (parallel A B) (at level 30).
Notation "A ⊸ B" := (dual A ⅋ B) (at level 30).
Notation "A ⊗ B" := (dual (dual A ⅋ dual B)) (at level 30).

Section comp.
  Context {I J K L M N : Type}.
  Context {A : game' I J} {B : game' K L} {C : game' M N}.
  Context {X : L * M -> Type} {Y : J * K -> Type} {Z : J * M -> Type}.
  Context (f : forall j l m, X (l , m) -> Z (j , m))
          (g : forall j k m, Y (j , k) -> Z (j , m)).

Variant comp_arg (j : J) (m : M) : Type :=
| C_ap {l} : itree (B ⊸ C) X (l , m) -> iforest (A ⊸ B) Y (inr (j , l)) -> comp_arg j m
| C_pa {k} : iforest (B ⊸ C) X (inl (k , m)) -> itree (A ⊸ B) Y (j , k) -> comp_arg j m
.

Definition comp : forall {j m}, comp_arg j m -> itree (A ⊸ C) Z (j , m) :=
cofix _aux _ _ x :=
  match x with
  | C_ap a b =>
    match (observe a) with
    | RetF r => Ret (f r)
    | TauF t => Tau (_aux _ _ (C_ap t b))
    | VisF e k =>
      match e as s return (forall r, itree (B ⊸ C) X (nxt (B ⊸ C) s r)) -> _ with
      | inl c => fun k => Tau (_aux _ _ (C_pa k (b c)))
      | inr c => fun k => Vis (inr c : qry (A ⊸ C) (_ , _))
                          (fun r => _aux _ _ (C_ap (k r) b))
      end k
    end
  | C_pa a b =>
    match (observe b) with
    | RetF r => Ret (g r)
    | TauF t => Tau (_aux _ _ (C_pa a t))
    | VisF e k =>
      match e as s return (forall r, itree (A ⊸ B) Y (nxt (A ⊸ B) s r)) -> _ with
      | inl c => fun k => Vis (inl c : qry (A ⊸ C) (_ , _))
                          (fun r => _aux _ _ (C_pa a (k r)))
      | inr c => fun k => Tau (_aux _ _ (C_ap (a c) k))
      end k
    end
  end.
End comp.

From OGS.ITree Require Import Eq.
From Paco Require Import paco.

Section assoc.
  Context {I J K L M N O P : Type}.
  Context {A : game' I J} {B : game' K L} {C : game' M N} {D : game' O P}.
  Context {X : N * O -> Type} {Y : L * M -> Type} {Z : J * K -> Type}
          {U : L * O -> Type} {V : J * M -> Type} {W : J * O -> Type}.
  Context (f0 : forall l n o, X (n, o) -> U (l, o))
          (g0 : forall l m o, Y (l, m) -> U (l, o))
          (f1 : forall j l o, U (l, o) -> W (j, o))
          (g1 : forall j k o, Z (j, k) -> W (j, o))
          (f0' : forall j l m, Y (l, m) -> V (j, m))
          (g0' : forall j k m, Z (j, k) -> V (j, m))
          (f1' : forall j n o, X (n, o) -> W (j, o))
          (g1' : forall j m o, V (j, m) -> W (j, o)).
  Context (eq0 : forall j l n o x, @f1 j l o (@f0 l n o x) = @f1' j n o x)
          (eq1 : forall j l m o y, @f1 j l o (@g0 l m o y) = @g1' j m o (@f0' j l m y))
          (eq2 : forall j k m o z, @g1 j k o z = @g1' j m o (@g0' j k m z)).


Variant assoc_arg (j : J) (o : O) : Type :=
| C_app {l n} : itree (C ⊸ D) X (n , o)
              -> iforest (B ⊸ C) Y (inr (l , n))
              -> iforest (A ⊸ B) Z (inr (j , l))
              -> assoc_arg j o
| C_pap {l m} : iforest (C ⊸ D) X (inl (m , o))
              -> itree (B ⊸ C) Y (l , m)
              -> iforest (A ⊸ B) Z (inr (j , l))
              -> assoc_arg j o
| C_ppa {k m} : iforest (C ⊸ D) X (inl (m , o))
              -> iforest (B ⊸ C) Y (inl (k , m))
              -> itree (A ⊸ B) Z (j , k)
              -> assoc_arg j o
.

Definition assoc_left {j o} (x : assoc_arg j o) : itree (A ⊸ D) W (j , o) :=
match x with
| C_app a b c => comp f1 g1 (C_ap (comp f0 g0 (C_ap a b)) c)
| C_pap a b c => comp f1 g1 (C_ap (comp f0 g0 (C_pa a b)) c)
| C_ppa a b c => comp f1 g1 (C_pa (fun r => comp f0 g0 (C_pa a (b _))) c) 
end.

Definition assoc_right {j o} (x : assoc_arg j o) : itree (A ⊸ D) W (j , o) :=
match x with
| C_app a b c => comp f1' g1' (C_ap a (fun r => comp f0' g0' (C_ap (b _) c)))
| C_pap a b c => comp f1' g1' (C_pa a (comp f0' g0' (C_ap b c)))
| C_ppa a b c => comp f1' g1' (C_pa a (comp f0' g0' (C_pa b c))) 
end.

Definition comp_assoc {j o} (x : assoc_arg j o) : assoc_left x ≊ assoc_right x.
revert j o x; pcofix CIH; pstep.
intros ? ? [? ? a ? ?|? ? ? a ?|? ? ? ? a].
all:
  cbn; cbv [eqit_ observe _observe];
  cbn [comp]; cbv [observe];
  cbn [_observe comp]; cbv [observe];
  destruct (_observe a); cbn.
3,6,9: destruct e. (* case split on event in 'VisF' goals *)
all:
  econstructor;
  try apply eq0;
  try apply eq1;
  try apply eq2;
  right;
  try (exact (CIH _ _ (C_app _ _ _)));
  try (exact (CIH _ _ (C_pap _ _ _)));
  try (exact (CIH _ _ (C_ppa _ _ _))).
Qed.
End assoc.
Arguments assoc_arg {I J K L M N O P} A B C D X Y Z.

Definition copycat {I J} (A : game' I J) X : forall u : I + J,
    iforest (A ⊸ A) X (match u with | inl i => inl (i , i)
                                    | inr j => inr (j , j) end) :=
cofix _copycat u := match u with
| inl i => fun r => Vis (inr r : qry (A ⊸ A) (_ , _)) (_copycat (inr _))
| inr i => fun r => Vis (inl r : qry (A ⊸ A) (_ , _)) (_copycat (inl _))
end.
Arguments copycat {I J} A X u.

(* Proofs that copycat ∘ f ≈ f and f ∘ copycat ≈ f *)
Section comp_id.
  Context {I J K L : Type}.
  Context {A : game' I J} {B : game' K L}.
  Context {X : J * K -> Type}.

  Variant comp_id_right_arg k :=
  | C_ai {j} : itree (A ⊸ B) X (j , k) -> comp_id_right_arg k
  | C_pi {i} : iforest (A ⊸ B) X (inl (i , k)) -> c_move A i -> comp_id_right_arg k
  .

  Equations comp_id_right_j {k} : comp_id_right_arg k -> J :=
    comp_id_right_j (@C_ai _ j a) := j ;
    comp_id_right_j (@C_pi _ i a v) := c_next A i v .

  Context {Y : J * I -> Type}.
  Context {f0 : forall j0 j1 k, X (j1, k) -> X (j0, k)}
          {g0 : forall j i k, Y (j, i) -> X (j, k)}.
  Context (eq0 : forall j k r, @f0 j j k r = r).

  Equations comp_id_right_left {k} (x : comp_id_right_arg k) : itree (A ⊸ B) X (comp_id_right_j x , k) :=
    comp_id_right_left (C_ai a) := comp f0 g0 (C_ap a (copycat A Y (inr _))) ;
    comp_id_right_left (C_pi a v) := comp f0 g0 (C_pa a (copycat A Y (inl _) v)) .

  Equations comp_id_right_right {k} (x : comp_id_right_arg k) : itree (A ⊸ B) X (comp_id_right_j x , k) :=
    comp_id_right_right (C_ai a) := a ;
    comp_id_right_right (C_pi a v) := a v .

  Definition comp_id_right {k} (x : comp_id_right_arg k)
             : comp_id_right_left x ≈ comp_id_right_right x.
    revert k x.
    pcofix CIH. intros k x.
    pstep. cbv [eqit_ observe].
    destruct x as [j a | i a v]; cbv [comp_id_right_right comp_id_right_left].
    - cbn; cbv [observe].
      destruct (_observe a).
      + econstructor. apply eq0.
      + econstructor. right. apply (CIH _ (C_ai _)).
      + destruct e.
        * econstructor. auto.
          cbn. econstructor.
          intro v.
          right. apply (CIH _ (C_pi _ _)).
        *  econstructor.
           intro v.
           right. apply (CIH _ (C_ai _)).
    - cbn. econstructor. auto.
      cbv [observe]; cbn. cbv [observe].
      destruct (_observe (a v)).
      +  econstructor. apply eq0.
      + econstructor. right. apply (CIH _ (C_ai _)).
      + destruct e.
        *  econstructor. auto.
           cbn. econstructor.
           intro v1. right. apply (CIH _ (C_pi _ _)).
        * econstructor. intro v1. right. apply (CIH _ (C_ai _)).
Qed.

  Context {Z : L * K -> Type}.
  Context {f1 : forall j l k, Z (l, k) -> X (j, k)}
          {g1 : forall j k0 k1, X (j, k0) -> X (j, k1)}.
  Context (eq1 : forall j k r, @g1 j k k r = r).

  Variant comp_id_left_arg j :=
  | C_ia {k} : itree (A ⊸ B) X (j , k) -> comp_id_left_arg j
  | C_ip {l} : iforest (A ⊸ B) X (inr (j , l)) -> s_move B l -> comp_id_left_arg j
  .

  Equations comp_id_left_k {j} : comp_id_left_arg j -> K :=
    comp_id_left_k (@C_ia _ k a) := k ;
    comp_id_left_k (@C_ip _ l a v) := s_next B l v .

  Equations comp_id_left_left {j} (x : comp_id_left_arg j) : itree (A ⊸ B) X (j, comp_id_left_k x) :=
    comp_id_left_left (C_ia a) := comp f1 g1 (C_pa (copycat B Z (inl _)) a) ;
    comp_id_left_left (C_ip a v) := comp f1 g1 (C_ap (copycat B Z (inr _) v) a) .

  Equations comp_id_left_right {j} (x : comp_id_left_arg j) : itree (A ⊸ B) X (j, comp_id_left_k x) :=
    comp_id_left_right (C_ia a) := a ;
    comp_id_left_right (C_ip a v) := a v .

  Definition comp_id_left {j} (x : comp_id_left_arg j)
             : comp_id_left_left x ≈ comp_id_left_right x.
    revert j x.
    pcofix CIH. intros j x.
    pstep. cbv [eqit_ observe].
    destruct x as [k a | l a v ].
    - cbn. cbv [observe].
      destruct (_observe a).
      + econstructor. apply eq1.
      + econstructor. right. apply (CIH _ (C_ia _)).
      + destruct e.
        * econstructor. intro v. right. apply (CIH _ (C_ia _)).
        * econstructor. auto.
          cbn. econstructor.
          intro v. right. apply (CIH _ (C_ip _ _)).
    -  cbn. econstructor. auto.
      cbv [observe]; cbn. cbv [observe].
      destruct (_observe (a v)).
      + econstructor. apply eq1.
      + econstructor. right. apply (CIH _ (C_ia _)).
      + destruct e.
        * econstructor. intro v1. right. apply (CIH _ (C_ia _)).
        * econstructor. auto.
          cbn. econstructor. intro v1. right. apply (CIH _ (C_ip _ _)).
  Qed.
End comp_id.


Definition bang {I J} (A : game' I J)
  : game' (I * list J) (list J) :=
{| client :=
   {| move := fun ix => c_move A (fst ix) ;
      next := fun ix m => c_next A (fst ix) m :: snd ix |} ;
   server :=
   {| move := fun js => { n : fin (length js) & s_move A (js .[ n ]) } ;
      next := fun js m => (s_next A (js .[ projT1 m]) (projT2 m), js) |} |}.
