From Coinduction Require Import coinduction tactics.

From OGS Require Import Prelude.
From OGS.Utils Require Import Rel.
From OGS.Game Require Import Event.
From OGS.ITree Require Import ITree Structure Eq.

Module stuff.
  Context {I} {E : event I I}.

  Definition eqn R X Y : Type := X ⇒ᵢ itree E (Y +ᵢ R) .
  Definition apply_eqn {R X Y} (q : eqn R X Y) : itree E (X +ᵢ R) ⇒ᵢ itree E (Y +ᵢ R) :=
    fun _ t => t >>= fun _ r => match r with
                            | inl x => q _ x
                            | inr y => Ret' (inr y)
                            end .

  Variant guarded' {X Y i} : itree' E (X +ᵢ Y) i -> Type :=
  | GRet y : guarded' (RetF (inr y))
  | GTau t : guarded' (TauF t)
  | GVis e k : guarded' (VisF e k)
  .
  Definition guarded {X Y i} (t : itree E (X +ᵢ Y) i) := guarded' t.(_observe). 
  Definition eqn_guarded {R X Y} (e : eqn R X Y) : Type := forall i (x : X i), guarded (e i x) .

  Definition apply_guarded_l {R X Y} (e : eqn R X Y) {i} (t : itree E (X +ᵢ R) i)
             : guarded t -> guarded (apply_eqn e _ t) .
  intro H; unfold guarded in *; cbn in *.
  destruct t.(_observe); dependent elimination H; cbn; econstructor.
  Defined.

  Definition apply_guarded_r {R X Y} (e : eqn R X Y) (H : eqn_guarded e) {i} (t : itree E (X +ᵢ R) i)
             : guarded (apply_eqn e _ t) .
    unfold guarded in *; cbn in *.
    destruct (_observe t) as [ [] | | ]; try econstructor.
    exact (H _ x).
  Defined.
  
  Definition iter_guarded_aux {R X} (e : eqn R X X) (H : eqn_guarded e) : itree E (X +ᵢ R) ⇒ᵢ itree E R :=
    cofix CIH i t := go match t.(_observe) with
                        | RetF (inl x) => match H i x with
                                          | GRet y => RetF y
                                          | GTau t => TauF (CIH _ t)
                                          | GVis e k => VisF e (fun r => CIH _ (k r))
                                          end
                        | RetF (inr y) => RetF y
                        | TauF t => TauF (CIH _ t)
                        | VisF e k => VisF e (fun r => CIH _ (k r))
                        end .

  Definition iter_guarded {R X} (e : eqn R X X) (H : eqn_guarded e) : X ⇒ᵢ itree E R :=
    fun _ x => iter_guarded_aux e H _ (e _ x) .

  Lemma iter_guarded_unfold {X Y RY} {_ : Reflexiveᵢ RY} (f : eqn Y X X) (H : eqn_guarded f) {i x}
    : it_eq RY
        (iter_guarded f H i x)
        (bind (f i x) (fun _ r => match r with
                                | inl x => iter_guarded f H _ x
                                | inr y => Ret' y end)).
    unfold iter_guarded; remember (f i x) as t; clear Heqt; clear x.
    revert i t; unfold it_eq; coinduction R CIH; intros i t.
    cbn; pose (ot := _observe t); fold ot; destruct ot as [ [] | | ]; cbn; auto.
    pose (Hix := H i x); pose (fix_ := f i x); fold Hix; fold fix_ in Hix |- *.
    destruct (Hix); auto.
  Qed.

  (*
  Lemma iter_guarded_lem {X Y RY} {_ : Equivalenceᵢ RY} (f : eqn Y X X) (g : X ⇒ᵢ itree E Y)
                 (H0 : eqn_guarded f)
                 (H : forall i x, it_eq RY (g i x) (bind (f i x) (fun _ r => match r with
                                                  | inl x => g _ x
                                                  | inr y => Ret' y end)))
                 : forall i x, it_eq RY (g i x) (iter_guarded f H0 i x).
    unfold it_eq; coinduction R CIH; intros i x.
    etransitivity; [ | symmetry; apply it_eq_t_bt, (iter_guarded_unfold f H0) ].
    rewrite (H i x); cbn.
    pose (a := (f i x).(_observe)); fold a.
    pose (Ha := H0 i x); unfold guarded in Ha; fold a in Ha.
    destruct Ha; cbn; econstructor; auto; [ | intro r ].
    all: change (subst ?f _ ?t) with (bind t f).
    all: eapply (tt_t (it_eq_map E RY)).
    all: refine (it_eq_up2bind_t _ _ _ _ _ _ _); econstructor; eauto.
    all: intros ? ? ? <-; destruct x1; auto.
  Qed.
*)

  (* eventually guarded equations *)

  Inductive ev_guarded' {X Y} (e : eqn Y X X) {i} : itree' E (X +ᵢ Y) i -> Type :=
  | GHead t : guarded' t -> ev_guarded' e t
  | GNext x : ev_guarded' e (e i x).(_observe) -> ev_guarded' e (RetF (inl x))
  .
  #[global] Arguments GHead {X Y e i}.
  #[global] Arguments GNext {X Y e i}.

  Definition ev_guarded {X Y} (e : eqn Y X X) {i} (t : itree E (X +ᵢ Y) i) := ev_guarded' e t.(_observe).
  Definition eqn_ev_guarded {X Y} (e : eqn Y X X) : Type := forall i (x : X i), ev_guarded e (e i x) .
  
  Equations evg_unroll {X Y} (e : eqn Y X X) {i} (t : itree' E (X +ᵢ Y) i) (p : ev_guarded' e t)
    : itree E (X +ᵢ Y) i :=
    evg_unroll e t (GHead _ g) := go t ;
    evg_unroll e t (GNext x p) := apply_eqn e _ (evg_unroll e (e i x).(_observe) p) .

  Equations evg_unroll_guarded {X Y} (e : eqn Y X X) {i} (t : itree' E (X +ᵢ Y) i) (p : ev_guarded' e t)
    : guarded (evg_unroll e t p) :=
    evg_unroll_guarded e t (GHead _ g) := g ;
    evg_unroll_guarded e t (GNext x p) := apply_guarded_l e _ (evg_unroll_guarded e _ p) . 

  Definition eqn_evg_unroll {X Y} (e : eqn Y X X) (H : eqn_ev_guarded e) : eqn Y X X
    := fun _ x => evg_unroll e (e _ x).(_observe) (H _ x) .

  Definition eqn_evg_unroll_guarded {X Y} (e : eqn Y X X) (H : eqn_ev_guarded e)
    : eqn_guarded (eqn_evg_unroll e H)
    := fun _ x => evg_unroll_guarded e (e _ x).(_observe) (H _ x) .

  Definition iter_ev_guarded {R X} (e : eqn R X X) (H : eqn_ev_guarded e) : X ⇒ᵢ itree E R :=
    iter_guarded _ (eqn_evg_unroll_guarded e H) .

  Lemma iter_evg_unfold_aux {X Y RY} {_ : Reflexiveᵢ RY} (f : eqn Y X X) (H : eqn_ev_guarded f) {i}
                  (t : itree E (X +ᵢ Y) i)
                  
    : it_eq RY
        (iter_guarded_aux (eqn_evg_unroll f H) (eqn_evg_unroll_guarded f H) i t)
        (t >>= fun (i0 : I) (r : (X +ᵢ Y) i0) =>
             match r with
             | inl x => iter_guarded (eqn_evg_unroll f H) (eqn_evg_unroll_guarded f H) i0 x
             | inr y => Ret' y
             end) .
    revert i t; unfold it_eq; coinduction R CIH; intros i t.
    cbn; destruct (_observe t) as [ [] | | ]; try econstructor; auto.
    clear t; cbn; unfold eqn_evg_unroll_guarded at 1, eqn_evg_unroll at 3.
    remember (H i x) as q; unfold ev_guarded in q.
    pose (u := (f i x).(_observe)); fold u in q |- *.
    clear Heqq; remember u as z ; clear Heqz u.
    induction q; cbn.
    * destruct g; auto.
    * unfold apply_guarded_l.
      pose (z := _observe (f i x0)).
      fold z in q ,IHq |- *; remember z as z'; clear Heqz' z.
      pose (tg := evg_unroll_guarded f z' q); fold tg in IHq |- *; unfold guarded in tg.
      destruct tg; cbn; auto.
  Qed.

  Lemma iter_evg_unfold {X Y RY} {_ : Reflexiveᵢ RY} (f : eqn Y X X) (H : eqn_ev_guarded f) {i x}
    : it_eq RY
        (iter_ev_guarded f H i x)
        (bind (f i x) (fun _ r => match r with
                                | inl x => iter_ev_guarded f H _ x
                                | inr y => Ret' y end)).
    unfold iter_ev_guarded at 1, iter_guarded, eqn_evg_unroll at 2.
    pose (t' := f i x); change (f i x >>= ?a) with (t' >>= a).
    remember t' as t; unfold t' in Heqt; clear t'.
    (* AHHHHHHHHHH
    revert Heqt; induction (H i x); intro Heqt; cbn
    - now apply it_eq_unstep.
    unfold eqn_evg_unroll at 1.
    pose (u := f i x).
    remember (H i x) as p. fold u in p.
    change (it_eqF E RY (it_eq RY) i _ _)
      with (it_eqF E RY (it_eq RY) i
              (_observe (iter_guarded_aux (eqn_evg_unroll f H) (eqn_evg_unroll_guarded f H) i (evg_unroll f (_observe u) p)))
              (_observe (bind (go (_observe u)) (fun _ r => match r with
                                          | inl x => iter_guarded (eqn_evg_unroll f H)
                                                      (eqn_evg_unroll_guarded f H) _ x
                                          | inr y => Ret' y end)))).
    *)
    Admitted.


End stuff.
