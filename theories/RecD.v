From OGS Require Import Utils EventD ITreeD CatD.
Check esum.

Definition iter {I} {E : event I} {X Y : I -> Type} (body : X ⇒ᵢ itree E (X +ᵢ Y))
  : X ⇒ᵢ itree E Y :=
  cofix _iter i x :=
    body i x ?>= fun _ y => match y with
                            | inl x' => Tau (_iter _ x')
                            | inr y => Ret y
                            end.

Instance ITreeMonadIter {I} (E : event I) : MonadIter (itree E) :=
  Build_MonadIter _ (fun X Y => @iter I E X Y).

Definition translate {I} {E F : event I} (f : E ⇒ₑ F) : itree E ⟹ itree F :=
  fun X => cofix _translate _ u :=
    match (observe u) with
    | RetF x => Ret x
    | TauF t => Tau (_translate _ t)
    | VisF e k => let (e1, k1) := f _ e in
                 Vis e1 (fun r => match k1 r with Fib a => _translate _ (k a) end)
     end.

Definition interp {I} {E : event I}
           {M : psh I -> psh I} {MF : Functor M} {MM : Monad M} {MI : MonadIter M}
           (h : E ₑ⇒ M) X
  : itree E X ⇒ᵢ M X :=
  CatD.iter (fun i x => match (observe x) with
            | RetF x => CatD.ret _ (inr x)
            | TauF t => CatD.ret _ (inl t)
            | VisF e k => CatD.fmap (fun _ => inl) _ (e_arrow_eval h _ _ (existT _ e k))
            end).


Definition interp_mrec {I} {E F : event I}
           (body : E ₑ⇒ itree (esum E F))
           : itree (esum E F) ⟹ itree F :=
  fun _ => iter (fun _ (t : itree (esum E F) _ _) => match (observe t) with
              | RetF r => Ret (inr r)
              | TauF t => Ret (inl t)
              | VisF (inl q) k => Ret (inl (body _ q ?>= fiber_into _ k))
              | VisF (inr q) k => Vis q (fun r => Ret (inl (k r)))
              end).

Definition mrec {I} {E F : event I} (body : E ₑ⇒ itree (esum E F)) : E ₑ⇒ itree F :=
  fun _ q => interp_mrec body _ _ (body _ q).

Definition ecall (A : Type) (B : A -> Type) : event T1 :=
  Event (fun _ => A) (fun _ => B) (fun i _ _ => i).

(* WIP
Definition rec {A B} (body : forall a, itree (ecall A B) (fun _ => B a) t1_0) : forall a, itree evoid (fun _ => B a) t1_0.
  refine (fun a => _).
  refine (@mrec T1 (ecall A B) evoid _ t1_0 _ ?>= _).
  intros [] q.
  cbn in *.
  refine (translate (einl) _ _ (body a)).
  cbn in q.
  cbn in body.
  cbn.
  refine (_ <$> body a).
  refine (((fun _ => inl) <$> body a)).
*)
