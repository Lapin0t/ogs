(*|
Substitution structures (§ 4.3)
===============================

In this file we axiomatize what it means for a family to support substitution.

.. coq:: none
|*)
From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.
From OGS.Ctx Require Import All.

Open Scope ctx_scope.
(*|
Substitution Monoid (Def. 4.9)
------------------------------

The specification of an evaluator will be separated in several steps. First we will ask
for a family of values, i.e. objects that can be substituted for variables. We formalize
well-typed well-scoped substitutions in the monoidal style of Fiore et al and Allais et al.
Here we are generic over a notion of context, treating lists and DeBruijn indices in the
usual well-typed well-scoped style, but also other similar notions. See
`Ctx/Abstract.v <Abstract.html>`_ for more background on notions of variables and contexts
and for the categorical presentation of substitution.

.. coq::
   :name: submonoid
|*)
Class subst_monoid `{CC : context T C} (val : Fam₁ T C) := {
  v_var : c_var ⇒₁ val ;
  v_sub : val ⇒₁ ⟦ val , val ⟧₁ ;
}.
(*|
.. coq:: none
|*)
#[global] Arguments v_var {T _ _ val _ Γ} [x].
#[global] Arguments v_sub {T _ _ val _} [Γ x] v {Δ} a.
(*|
|*)
#[global] Notation "v ᵥ⊛ a" := (v_sub v a%asgn) (at level 30).
Notation a_id := v_var.
(*|
By pointwise lifting of substitution we can define composition of assignments.
|*)
Definition a_comp `{subst_monoid T C val} {Γ1 Γ2 Γ3}
  : Γ1 =[val]> Γ2 -> Γ2 =[val]> Γ3 -> Γ1 =[val]> Γ3
  := fun u v _ i => u _ i ᵥ⊛ v.
#[global] Infix "⊛" := a_comp (at level 14) : asgn_scope.
(*|
.. coq:: none
|*)
#[global] Arguments a_comp _ _ _ _ _ _ _ _ _ _ _ /.
(*|
The laws for monoids and modules are pretty straightforward. A specificity is that
assignments are represented by functions from variables to values, as such their
well-behaved equality is pointwise equality and we require substitution to respect it.
|*)
Class subst_monoid_laws `{CC : context T C} (val : Fam₁ T C) {VM : subst_monoid val} := {
  v_sub_proper :: Proper (∀ₕ Γ, ∀ₕ _, eq ==> ∀ₕ Δ, asgn_eq Γ Δ ==> eq) v_sub ;
  v_sub_var {Γ1 Γ2 x} (i : Γ1 ∋ x) (p : Γ1 =[val]> Γ2)
    : v_var i ᵥ⊛ p = p _ i ;
  v_var_sub {Γ x} (v : val Γ x)
    : v ᵥ⊛ a_id = v ;
  v_sub_sub {Γ1 Γ2 Γ3 x} (v : val Γ1 x) (a : Γ1 =[val]> Γ2) (b : Γ2 =[val]> Γ3)
   : v ᵥ⊛ (a ⊛ b) = (v ᵥ⊛ a) ᵥ⊛ b ;
} .
(*|
.. coq:: none
|*)
#[global] Arguments subst_monoid_laws {T C CC} val {VM}.
(*|
|*)
#[global] Instance v_sub_proper_a `{subst_monoid_laws T C val}
          {Γ1 Γ2 x} {v : val Γ1 x} : Proper (asgn_eq Γ1 Γ2 ==> eq) (v_sub v).
Proof. now apply v_sub_proper. Qed.
(*|
Substitution Module (Def. 4.11)
-------------------------------

Next, we ask for a module over the monoid of values, to represent the configurations
of the machine.

.. coq::
   :name: submodule
|*)
Class subst_module `{CC : context T C} (val : Fam₁ T C) (conf : Fam₀ T C) := {
  c_sub : conf ⇒₀ ⟦ val , conf ⟧₀ ;
}.
(*|
.. coq:: none
|*)
#[global] Arguments c_sub {T C CC val conf _} [Γ] c {Δ} a.
(*|
|*)
#[global] Notation "c ₜ⊛ a" := (c_sub c a%asgn) (at level 30).
(*|
Again the laws should not be surprising.
|*)
Class subst_module_laws `{CC : context T C} (val : Fam₁ T C) (conf : Fam₀ T C)
      {VM : subst_monoid val} {CM : subst_module val conf} := {
  c_sub_proper :: Proper (∀ₕ Γ, eq ==> ∀ₕ Δ, asgn_eq Γ Δ ==> eq) c_sub ;
  c_var_sub {Γ} (c : conf Γ) : c ₜ⊛ a_id = c ;
  c_sub_sub {Γ1 Γ2 Γ3} (c : conf Γ1) (a : Γ1 =[val]> Γ2) (b : Γ2 =[val]> Γ3)
    : c ₜ⊛ (a ⊛ b) = (c ₜ⊛ a) ₜ⊛ b ;
} .

#[global] Instance c_sub_proper_a `{subst_module_laws T C val conf}
          {Γ1 Γ2 c} : Proper (asgn_eq Γ1 Γ2 ==> eq) (c_sub c).
Proof. now apply c_sub_proper. Qed.
(*|
Now that we know that our families have a substitution operation and variables, we
can readily derive a renaming operation. While we could have axiomatized it, together with
its compatibility with substitution, allowing for possibly more efficient implementations,
we prefer simplicity and work with this generic implementation in terms of substitution.
|*)
Section renaming.
  Context `{CC : context T C} {val : Fam₁ T C} {conf : Fam₀ T C}.
  Context {VM : subst_monoid val} {VML : subst_monoid_laws val}.
  Context {CM : subst_module val conf} {CML : subst_module_laws val conf}.
(*|
By post-composing with the substitution identity, we can embed renamings into assignments.
|*)
  Definition r_emb {Γ Δ} (r : Γ ⊆ Δ) : Γ =[val]> Δ
    := fun _ i => v_var (r _ i).
  #[global] Arguments r_emb {_ _} _ _ /.

(*|
Renaming is now simply a matter of substituting by the embedded renaming. We could have
gone full on category theory and defined them respectively as
``v_sub ⦿₁ hom_precomp₁ v_var`` and ``c_sub ⦿₀ hom_precomp₀ v_var`` but on top of being a
bit pedantic, this would not behave nicely with unfolding.
|*)
  Definition v_ren : val ⇒₁ ⟦ c_var , val ⟧₁
    := fun _ _ v _ r => v ᵥ⊛ r_emb r.
  Definition c_ren : conf ⇒₀ ⟦ c_var , conf ⟧₀
    := fun _ c _ r => c ₜ⊛ r_emb r.
  #[global] Arguments v_ren [Γ x] v [Δ] r /.
  #[global] Arguments c_ren [Γ] v [Δ] r /.
(*|
Finally we can rename assignments on the right.
|*)
  Definition a_ren_r {Γ1 Γ2 Γ3} : Γ1 =[val]> Γ2 -> Γ2 ⊆ Γ3 -> Γ1 =[val]> Γ3
    := fun a r => (a ⊛ (r_emb r))%asgn.
  #[global] Arguments a_ren_r _ _ _ _ _ _ /.
End renaming.
#[global] Notation "v ᵥ⊛ᵣ r" := (v_ren v r%asgn) (at level 14).
#[global] Notation "c ₜ⊛ᵣ r" := (c_ren c r%asgn) (at level 14).
#[global] Notation "a ⊛ᵣ r" := (a_ren_r a r) (at level 14) : asgn_scope.
(*|
Something which we have absolutely pushed under the rug in the paper is a couple more
mild technical hypotheses on the substitution monoid of values: since in the
`eventual guardedness proof <CompGuarded.html>`_ we need to case split on whether
or not a value is a variable, we need to ask for that to be possible! As such,
we need the following additional assumptions:

- ``v_var`` has decidable fibers
- ``v_var`` is injective
- the fibers of ``v_var`` pull back along renamings

We first define the fibers of ``v_var``.
|*)
Variant is_var `{VM : subst_monoid T C val} {Γ x} : val Γ x -> Type :=
| Vvar (i : Γ ∋ x) : is_var (v_var i)
.

Equations is_var_get `{VM : subst_monoid T C val} {Γ x} {v : val Γ x} : is_var v -> Γ ∋ x :=
  is_var_get (Vvar i) := i .
(*|
Which are obviously stable under renamings.
|*)
Lemma ren_is_var `{VM : subst_monoid_laws T C val} {Γ1 Γ2} (r : Γ1 ⊆ Γ2) {x} {v : val Γ1 x} 
      : is_var v -> is_var (v ᵥ⊛ᵣ r).
Proof.
  intro p; dependent elimination p.
  cbn; rewrite v_sub_var.
  econstructor.
Qed.
(*|
At last we define our last assumptions on variables.
|*)
Class var_assumptions `{CC : context T C} (val : Fam₁ T C) {VM : subst_monoid val} := {
  v_var_inj {Γ x} : injective (@v_var _ _ _ _ _ Γ x) ;
  is_var_dec {Γ x} (v : val Γ x) : decidable (is_var v) ;
  is_var_ren {Γ1 Γ2 x} (v : val Γ1 x) (r : Γ1 ⊆ Γ2) : is_var (v ᵥ⊛ᵣ r) -> is_var v ;
}.
(*|
Here we derive a couple helpers around these new assumptions.
|*)
Section variables.
  Context `{CC : context T C} {val : Fam₁ T C}.
  Context {VM : subst_monoid val} {VML : subst_monoid_laws val}.
  Context {VA : var_assumptions val}.

  Lemma is_var_irr {Γ x} {v : val Γ x} (p q : is_var v) : p = q.
  Proof.
    refine (match p as i in is_var v
            return forall w (H : w = v) (q : is_var w), i = rew [is_var] H in q
            with Vvar i => fun w H q => _
            end v eq_refl q).
    dependent elimination q.
    pose proof (v_var_inj _ _ H) as H'.
    now dependent elimination H'; dependent elimination H.
  Qed.

  Lemma is_var_simpl {Γ x} {i : Γ ∋ x} (p : is_var (v_var i)) : p = Vvar i.
  Proof. apply is_var_irr. Qed.

  Variant is_var_ren_view {Γ1 Γ2 x}
    (v : val Γ1 x) (r : Γ1 ⊆ Γ2) : is_var (v ᵥ⊛ᵣ r) -> Type :=
  | Vvren (H : is_var v) : is_var_ren_view v r (ren_is_var r H) .

  Lemma view_is_var_ren {Γ1 Γ2 x} (v : val Γ1 x) (r : Γ1 ⊆ Γ2) (H : is_var (v ᵥ⊛ᵣ r))
    : is_var_ren_view v r H .
  Proof.
    rewrite (is_var_irr H (ren_is_var r (is_var_ren v r H))); econstructor.
  Qed.

  Lemma ren_is_var_get {Γ1 Γ2} {r : Γ1 ⊆ Γ2}
    {x v} (H : is_var v) : is_var_get (ren_is_var r H) = r x (is_var_get H) .
  Proof.
    destruct H; cbn.
    generalize (ren_is_var r (Vvar i)).
    unfold v_ren; rewrite v_sub_var; unfold r_emb; intro H.
    now rewrite (is_var_irr H (Vvar (r _ i))).
  Qed.

  Lemma is_var_get_eq {Γ x} {v : val Γ x} (H : is_var v) : v = v_var (is_var_get H) .
  Proof. now destruct H. Qed.
End variables.
(*|
Finally we end with a couple derived property on assignments.
|*)
Section properties.
  Context {T C} {CC : context T C} (val : Fam₁ T C).
  Context {VM : subst_monoid val} {VML : subst_monoid_laws val}.

  #[global] Instance a_comp_proper {Γ1 Γ2 Γ3} :
    Proper (asgn_eq Γ1 Γ2 ==> asgn_eq Γ2 Γ3 ==> asgn_eq Γ1 Γ3) a_comp.
  Proof. intros ?? H1 ?? H2 ??; cbn; now rewrite H1, H2. Qed.

  #[global] Instance r_emb_proper {Γ1 Γ2} : Proper (asgn_eq Γ1 Γ2 ==> asgn_eq Γ1 Γ2) r_emb.
  Proof. intros ?? H ??; cbn; now rewrite H. Qed.

  #[global] Instance a_ren_proper {Γ1 Γ2 Γ3} :
    Proper (asgn_eq Γ1 Γ2 ==> asgn_eq Γ2 Γ3 ==> asgn_eq Γ1 Γ3) a_ren_r.
  Proof. intros ?? H1 ?? H2 ??; cbn; now rewrite H1, H2. Qed.

  Lemma a_ren_r_simpl {Γ1 Γ2 Γ3} (r : Γ1 ⊆ Γ2) (a : Γ2 =[val]> Γ3) 
        : r_emb r ⊛ a ≡ₐ r ᵣ⊛ a .
  Proof. intros ??; cbn; now rewrite v_sub_var. Qed.

  Lemma a_ren_id {Γ} : r_emb r_id ≡ₐ a_id (Γ:=Γ) .
  Proof. reflexivity. Qed.

  Lemma a_comp_ren {Γ1 Γ2 Γ3 Γ4} (a : Γ1 =[val]> Γ2) (b : Γ2 =[val]> Γ3) (r : Γ3 ⊆ Γ4)
    : (a ⊛ b) ⊛ᵣ r ≡ₐ a ⊛ (b ⊛ᵣ r).
  Proof. intros ??; cbn; now rewrite <-v_sub_sub. Qed.

  Lemma a_ren_comp {Γ1 Γ2 Γ3 Γ4} (a : Γ1 =[val]> Γ2) (r : Γ2 ⊆ Γ3) (b : Γ3 =[val]> Γ4)
    : (a ⊛ᵣ r) ⊛ b ≡ₐ a ⊛ (r ᵣ⊛ b).
  Proof. intros ??; cbn; now rewrite <-v_sub_sub, a_ren_r_simpl. Qed.

  Lemma a_comp_comp {Γ1 Γ2 Γ3 Γ4} (a : Γ1 =[val]> Γ2) (b : Γ2 =[val]> Γ3)
                    (c : Γ3 =[val]> Γ4)
    : (a ⊛ b) ⊛ c ≡ₐ a ⊛ (b ⊛ c).
  Proof. intros ??; cbn; now rewrite v_sub_sub. Qed.

  Lemma a_comp_id {Γ1 Γ2} (a : Γ1 =[val]> Γ2) : a ⊛ a_id ≡ₐ a .
  Proof. intros ??; cbn; now rewrite v_var_sub. Qed.

  Lemma a_id_comp {Γ1 Γ2} (a : Γ1 =[val]> Γ2) : a_id ⊛ a ≡ₐ a .
  Proof. intros ??; cbn. now rewrite v_sub_var. Qed.
End properties.
