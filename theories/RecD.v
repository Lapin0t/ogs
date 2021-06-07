From OGS Require Import Utils EventD ITreeD CatD AngelicD.
Check esum.

Definition iter {I} {E : event I I} {X Y : I -> Type} (body : X ⇒ᵢ itree E (X +ᵢ Y))
  : X ⇒ᵢ itree E Y :=
  cofix _iter i x :=
    bind (body i x) (fun _ y => match y with
                            | inl x' => Tau (_iter _ x')
                            | inr y => Ret y
                            end).

Instance ITreeMonadIter {I} (E : event I I) : MonadIter (itree E) :=
  Build_MonadIter _ (fun X Y => @iter I E X Y).

Definition translate {I} {E F : event I I} (f : E ⇒ₑ F) : itree E ⟹ itree F :=
  fun _ => cofix _translate _ u :=
    match (observe u) with
    | RetF x => Ret x
    | TauF t => Tau (_translate _ t)
    | VisF e k => let (e1, k1) := f _ e in
                 Vis e1 (fun r => match k1 r with Fib a => _translate _ (k a) end)
     end.

Definition translate_fwd {I J} {E : event I I} {F : event J J} (f0 : I -> J)
           (f : (f0 >ₑ E) ⇒ₑ (F <ₑ f0))
           X : (itree E (X ∘ f0)) ⇒ᵢ (itree F X ∘ f0) :=
  cofix _translate i u :=
    match (observe u) with
    | RetF x => @ITreeD.ret _ _ _ (f0 i) x
    | TauF t => @ITreeD.tau _ _ _ (f0 i) (_translate _ t)
    | VisF e k => let (e1, k1) := f _ e in
                 Vis e1 (fun r => fiber_rect _ _ _ (fun i _ => itree _ _ i)
                                 (fun a => _translate _ (k a)) _ (k1 r))
    end.

Definition translate_bwd {I J} {E : event I I} {F : event J J} (f0 : J -> I)
           (f : (E <ₑ f0) ⇒ₑ (f0 >ₑ F))
           X : (itree E X ∘ f0) ⇒ᵢ (itree F (X ∘ f0)) :=
  cofix _translate i u :=
    match (observe u) with
    | RetF x => Ret x
    | TauF t => Tau (_translate _ t)
    | VisF e k => let (e1, k1) := f _ e in
                 Vis e1 (fun r => _translate _ (fiber_rect _ _ _ (fun i _ => itree _ _ i)
                                                        k _ (k1 r)))
    end.

Definition comp (X : Type) : Type := itree₀ ∅ₑ X.
Definition emb_comp {I} {E : event I I} X i : comp X -> itree E (X @ i) i.
  refine (fun t => translate_fwd (fun _ => i) (fun _ (i : qry (_ >ₑ ∅ₑ) _) => ex_falso i)
                              (X @ i) t1_0 (t >>= _)).
  refine (fun 't1_0 '(Fib a) => Ret (Fib a)).
Defined.

Definition interp {I} {E : event I I}
           {M : psh I -> psh I} {MF : Functor M} {MM : Monad M} {MI : MonadIter M}
           (h : E ₑ⇒ M)
           : itree E ⟹ M :=
  fun _ => CatD.iter (fun i x => match (observe x) with
            | RetF x => CatD.ret _ (inr x)
            | TauF t => CatD.ret _ (inl t)
            | VisF e k => CatD.fmap (fun _ => inl) _ (e_arrow_eval h _ _ (existT _ e k))
            end).


Definition interp_mrec {I} {E F : event I I}
           (body : E ₑ⇒ itree (esum E F))
           : itree (esum E F) ⟹ itree F :=
  fun _ => iter (fun _ (t : itree (esum E F) _ _) => match (observe t) with
              | RetF r => Ret (inr r)
              | TauF t => Ret (inl t)
              | VisF (inl q) k => Ret (inl (body _ q >>= fiber_into _ k))
              | VisF (inr q) k => Vis q (fun r => Ret (inl (k r)))
              end).

Definition mrec {I} {E F : event I I} (body : E ₑ⇒ itree (esum E F)) : E ₑ⇒ itree F :=
  fun _ q => interp_mrec body _ _ (body _ q).

Definition trigger {I} {E : event I I} : E ₑ⇒ itree E :=
  fun _ q => Vis q (fun r => Ret (Fib r)).

Definition trigger₀ {E : event₀} (q : qry₀ E) : itree₀ E (rsp₀ E q) := vis₀ q ret₀.

Definition ecall (A : Type) (B : A -> Type) : event₀ := Event₀ A B.
Definition call {A B} : forall a, itree₀ (ecall A B) (B a) := @trigger₀ (ecall A B).
Definition rec {A B} (body : forall a, itree₀ (ecall A B) (B a)) : forall a, itree₀ ∅ₑ (B a) :=
  mrec (fun 't1_0 (a : qry₀ (ecall A B)) => translate inlₑ (B a @ _) _ (body a)) _.
