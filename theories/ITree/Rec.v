(** Recursion combinators for itrees: iteration, mutual recursion. *)
From OGS Require Import Utils.
From OGS.ITree Require Import Cat Event ITree Angelic.

Definition iter {I} {E : event I I} {X Y : I -> Type} (body : X ⇒ᵢ itree E (X +ᵢ Y))
  : X ⇒ᵢ itree E Y :=
  cofix _iter i x :=
    bind (body i x) (fun _ y => match y with
                            | inl x' => Tau (_iter _ x')
                            | inr y => Ret y
                            end).

Instance ITreeMonadIter {I} (E : event I I) : MonadIter (itree E) :=
  Build_MonadIter _ (fun X Y => @iter I E X Y).

Definition translate {I} {E F : event I I} (f : E ⇒ₑ F) : itree E ⇒ₙ itree F :=
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
    | RetF x => @ITree.ret _ _ _ (f0 i) x
    | TauF t => @ITree.tau _ _ _ (f0 i) (_translate _ t)
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

(** Possibly non-terminating computation, ie an itree null event. *)
Definition comp (X : Type) : Type := NonDep.itree ∅ₑ X.

(** Embedding a computation into any index-preserving itree. *)
Definition emb_comp {I} {E : event I I} X i : comp X -> itree E (X @ i) i.
  refine (fun t => translate_fwd (fun _ => i) (fun _ (i : qry (_ >ₑ ∅ₑ) _) => ex_falso i)
                              (X @ i) T1_0 (t >>= _)).
  refine (fun 't1_0 '(Fib a) => Ret (Fib a)).
Defined.

(** If we know how to interpret operations from event `E` in an monad
    `M`, and that monad is iterative, then we can interpret `itree E`
    in `M`.
*)
Definition interp {I} {E : event I I}
           {M : psh I -> psh I} {MF : Functor M} {MM : Monad M} {MI : MonadIter M}
           : E ⤳ₑ M -> itree E ⇒ₙ M :=
  fun h _ => Cat.iter (fun i x => match (observe x) with
            | RetF x => Cat.ret _ (inr x)
            | TauF t => Cat.ret _ (inl t)
            | VisF e k => Cat.fmap (fun _ => inl) _ (evalₑ_arrow h _ _ (e ,' k))
            end).


(** Given recursive effectful interpretation of event `E`, we can remove it from
    the itree. This is the core lemma for interpreting mutual general recursion.
*)
Definition interp_mrec {I} {E F : event I I}
           : E ⤳ₑ itree (E +ₑ F) -> itree (E +ₑ F) ⇒ₙ itree F :=
  fun body _ => iter (fun _ (t : itree (E +ₑ F) _ _) => match (observe t) with
              | RetF r => Ret (inr r)
              | TauF t => Ret (inl t)
              | VisF (inl q) k => Ret (inl (body _ q >>= fib_into _ k))
              | VisF (inr q) k => Vis q (fun r => Ret (inl (k r)))
              end).

Definition mrec {I} {E F : event I I} : E ⤳ₑ itree (E +ₑ F) -> E ⤳ₑ itree F :=
  fun body _ q => interp_mrec body _ _ (body _ q).

Definition trigger {I} {E : event I I} : E ⤳ₑ itree E :=
  fun _ q => Vis q (fun r => Ret (Fib r)).

(*
Definition trigger₀ {E : event₀} (q : qry₀ E) : itree₀ E (rsp₀ E q) := vis₀ q ret₀.

Definition ecall (A : Type) (B : A -> Type) : NonDep.event := NonDep.Event A B.
Definition call {A B} : forall a, NonDep.itree (ecall A B) (B a) := @trigger₀ (ecall A B).
Definition rec {A B} (body : forall a, itree₀ (ecall A B) (B a)) : forall a, itree₀ ∅ₑ (B a) :=
  mrec (fun 't1_0 (a : qry₀ (ecall A B)) => translate inlₑ (B a @ _) _ (body a)) _.

*)
