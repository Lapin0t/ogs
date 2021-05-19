From OGS Require Import Utils EventD ITreeD CatD.
Check esum.

Definition iter {I} {E : event I} {X Y : I -> Type} (body : X ==> itree E (X +i Y))
             : X ==> itree E Y :=
  cofix _iter i x :=
    body i x ?>= fun _ y => match y with
                            | inl x' => Tau (_iter _ x')
                            | inr y => Ret y
                            end.

Definition interp {I} {E : event I}
           {M : psh I -> psh I} {MF : Functor M} {MM : Monad M} {MI : MonadIter M}
           (h : earrow_fam E M) X
  : itree E X ==> M X.
  refine (CatD.iter _).
  refine (fun i x => _).
  refine (match (observe x) with
          | RetF x => CatD.ret _ (inr x)
          | TauF t => CatD.ret _ (inl t)
          | VisF e k => CatD.fmap (fun _ => inl) _ _
          end).
  refine (ea_eval_fam h _ _ (existT _ e k)).
Defined.

Definition interp_mrec {I} {E F : event I}
           (body : earrow_fam E (itree (esum E F)))
           {X} : itree (esum E F) X ==> itree F X.
  refine (iter (fun _ t => match (observe t) with
                | RetF r => Ret (inr r)
                | TauF t => Ret (inl t)
                | VisF q k => _
                end)).
  destruct q.
  - exact (Ret (inl (body _ q ?>= (fun _ o => match o with FOk _ r => k r end)))).
  - exact (Vis q (fun r => Ret (inl (k r)))).
Defined.

Definition interp_mrec' {I} {E F : event I}
           (body : forall X, ⟦ E ]] X ==> itree (esum E F) X)
           {X} : itree (esum E F) X ==> itree F X.
  refine (iter (fun _ t => match (observe t) with
                | RetF r => Ret (inr r)
                | TauF t => Ret (inl t)
                | VisF q k => _
                end)).
  destruct q.
  - exact (Ret (inl (body _ q ?>= (fun _ o => match o with FOk _ r => k r end)))).
  - exact (Vis q (fun r => Ret (inl (k r)))).
Defined.
Definition mrec {I} {E F : event I} (body : earrow_fam E (itree (esum E F)))
           : earrow_fam E (itree F) :=
  fun _ q => interp_mrec body _ (body _ q).
