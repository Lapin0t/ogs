(*|
The Machine Strategy (§ 5.3)
============================

Having defined the `OGS game <Game.html>`_ and axiomatized the
`language machine <Machine.v>`_, we are now ready to construct the *machine strategy*.

.. coq:: none
|*)
From OGS Require Import Prelude.
From OGS.Utils Require Import Psh Rel.
From OGS.Ctx Require Import All Ctx.
From OGS.OGS Require Import Subst Obs Machine Game.
From OGS.ITree Require Import Event ITree Eq Structure Delay.

Reserved Notation "'ε⁺'".
Reserved Notation "'ε⁻'".
Reserved Notation "u ;⁺" (at level 40).
Reserved Notation "u ;⁻ e" (at level 40).
Reserved Notation "ₐ↓ γ" (at level 3).
Reserved Notation "u ∥ v" (at level 40).
Reserved Notation "x ≈ₐ y" (at level 50).
Reserved Notation "x ≈ₚ y" (at level 50).
Reserved Notation "x ≈⟦ogs Δ ⟧≈ y" (at level 50).

Section with_param.
(*|
We consider a language abstractly captured as a machine.
|*)
  Context `{CC : context T C} {CL : context_laws T C}.
  Context {val} {VM : subst_monoid val} {VML : subst_monoid_laws val}.
  Context {conf} {CM : subst_module val conf} {CML : subst_module_laws val conf}.
  Context {obs : obs_struct T C} {M : machine val conf obs}.
(*|
We start off by defining active and passive OGS assignments (Def 5.16). This datastructure
will hold the memory part of a strategy state, remembering the values which we have
hidden from Opponent and given as fresh variables.

.. coq::
   :name: ogsenv
|*)
  Inductive ogs_env (Δ : C) : polarity -> ogs_ctx -> Type :=
  | ENilA : ogs_env Δ Act ∅ₓ
  | ENilP : ogs_env Δ Pas ∅ₓ
  | EConA {Φ Γ} : ogs_env Δ Pas Φ -> ogs_env Δ Act (Φ ▶ₓ Γ)
  | EConP {Φ Γ} : ogs_env Δ Act Φ -> Γ =[val]> (Δ +▶ ↓⁺Φ) -> ogs_env Δ Pas (Φ ▶ₓ Γ)
  .
(*|
.. coq:: none
|*)
  #[global] Arguments ENilA {Δ}.
  #[global] Arguments ENilP {Δ}.
  #[global] Arguments EConA {Δ Φ Γ} u.
  #[global] Arguments EConP {Δ Φ Γ} u γ.
  Derive Signature NoConfusion NoConfusionHom for ogs_env.
(*|
|*)
  Notation "'ε⁺'" := (ENilA).
  Notation "'ε⁻'" := (ENilP).
  Notation "u ;⁺" := (EConA u).
  Notation "u ;⁻ e" := (EConP u e).
(*|
Next we define the collapsing function on OGS assignments (Def 5.18).

.. coq::
   :name: envcollapse
|*)
  Equations collapse {Δ p Φ} : ogs_env Δ p Φ -> ↓[p^]Φ =[val]> (Δ +▶ ↓[p]Φ) :=
    collapse ε⁺       := ! ;
    collapse ε⁻       := ! ;
    collapse (u ;⁺)   := collapse u ⊛ᵣ r_cat3_1 ;
    collapse (u ;⁻ e) := [ collapse u , e ] .
  Notation "ₐ↓ γ" := (collapse γ).
(*|
We readily define the zipping function (Def 6.10).

.. coq::
   :name: zip
|*)
  #[derive(eliminator=no)]
  Equations bicollapse {Δ} Φ : ogs_env Δ Act Φ -> ogs_env Δ Pas Φ -> forall p, ↓[p]Φ =[val]> Δ :=
    bicollapse ∅ₓ       (ε⁺)     (ε⁻)     Act   := ! ;
    bicollapse ∅ₓ       (ε⁺)     (ε⁻)     Pas   := ! ;
    bicollapse (Φ ▶ₓ _) (u ;⁺)   (v ;⁻ γ) Act :=
          [ bicollapse Φ v u Pas , γ ⊛ [ a_id , bicollapse Φ v u Act ] ] ;
    bicollapse (Φ ▶ₓ _) (v ;⁺)   (u ;⁻ e) Pas := bicollapse Φ u v Act .
  #[global] Arguments bicollapse {Δ Φ} u v {p}.
(*|
And the fixpoint property linking collapsing and zipping (Prop 6.13).

.. coq::
   :name: collapsezip
|*)
  Lemma collapse_fix_aux {Δ Φ} (u : ogs_env Δ Act Φ) (v : ogs_env Δ Pas Φ)
    :  ₐ↓u ⊛ [ a_id , bicollapse u v ] ≡ₐ bicollapse u v
     /\ ₐ↓v ⊛ [ a_id , bicollapse u v ] ≡ₐ bicollapse u v .
  Proof.
    induction Φ; dependent destruction u; dependent destruction v.
    - split; intros ? i; now destruct (c_view_emp i).
    - split; cbn; simp collapse; simp bicollapse.
      + intros ? i; cbn; rewrite <- v_sub_sub, a_ren_r_simpl, r_cat3_1_simpl.
        now apply IHΦ.
        exact _. (* wtf typeclass?? *)
      + intros ? i; cbn; destruct (c_view_cat i); eauto.
        now apply IHΦ.
  Qed.

  Lemma collapse_fix_act {Δ Φ} (u : ogs_env Δ Act Φ) (v : ogs_env Δ Pas Φ)
    : ₐ↓u ⊛ [ a_id , bicollapse u v ] ≡ₐ bicollapse u v .
  Proof. now apply collapse_fix_aux. Qed.

  Lemma collapse_fix_pas {Δ Φ} (u : ogs_env Δ Act Φ) (v : ogs_env Δ Pas Φ)
    : ₐ↓v ⊛ [ a_id , bicollapse u v ] ≡ₐ bicollapse u v .
  Proof. now apply collapse_fix_aux. Qed.
(*|
Here we provide an alternative definition to the collapsing functions, using a more
precisely typed lookup function. This is more practical to use when reasoning about
the height of a variable, in the `eventual guardedness proof <CompGuarded.html>`_.

First we compute actual useful subset of the context used by a particular variable.
|*)
  Equations ctx_dom Φ p {x} : ↓[p^]Φ ∋ x -> C :=
    ctx_dom ∅ₓ       Act i with c_view_emp i := { | ! } ;
    ctx_dom ∅ₓ       Pas i with c_view_emp i := { | ! } ;
    ctx_dom (Φ ▶ₓ Γ) Act i := ctx_dom Φ Pas i ;
    ctx_dom (Φ ▶ₓ Γ) Pas i with c_view_cat i := {
      | Vcat_l j := ctx_dom Φ Act j ;
      | Vcat_r j := ↓[Act]Φ } .
  #[global] Arguments ctx_dom {Φ p x} i.
(*|
Next we provide a renaming from this precise domain to the actual current allowed context.
|*)
  Equations r_ctx_dom Φ p {x} (i : ↓[p^]Φ ∋ x) : ctx_dom i ⊆ ↓[p]Φ :=
    r_ctx_dom ∅ₓ       Act i with c_view_emp i := { | ! } ;
    r_ctx_dom ∅ₓ       Pas i with c_view_emp i := { | ! } ;
    r_ctx_dom (Φ ▶ₓ Γ) Act i := r_ctx_dom Φ Pas i ᵣ⊛ r_cat_l ;
    r_ctx_dom (Φ ▶ₓ Γ) Pas i with c_view_cat i := {
      | Vcat_l j := r_ctx_dom Φ Act j ;
      | Vcat_r j := r_id } .
  #[global] Arguments r_ctx_dom {Φ p x} i.
(*|
We can write this more precise lookup function, returning a value in just the necessary
context.
|*)
  Equations lookup {Δ p Φ} (γ : ogs_env Δ p Φ) [x] (i : ↓[p^]Φ ∋ x)
            : val (Δ +▶ ctx_dom i) x :=
    lookup ε⁺       i with c_view_emp i := { | ! } ;
    lookup ε⁻       i with c_view_emp i := { | ! } ;
    lookup (γ ;⁺)   i := lookup γ i ;
    lookup (γ ;⁻ e) i with c_view_cat i := {
      | Vcat_l j := lookup γ j ;
      | Vcat_r j := e _ j } .
(*|
We relate the precise lookup with the previously defined collapse.
|*)
  Lemma lookup_collapse {Δ p Φ} (γ : ogs_env Δ p Φ) :
    collapse γ ≡ₐ (fun x i => lookup γ i ᵥ⊛ᵣ [ r_cat_l , r_ctx_dom i ᵣ⊛ r_cat_r ]).
  Proof.
    intros ? i; funelim (lookup γ i).
    - cbn; rewrite H.
      unfold v_ren; rewrite <- v_sub_sub.
      apply v_sub_proper; eauto.
      intros ? j; cbn; rewrite v_sub_var; cbn; f_equal.
      unfold r_cat3_1; destruct (c_view_cat j); cbn.
      + now rewrite c_view_cat_simpl_l.
      + now rewrite c_view_cat_simpl_r.
    - cbn; rewrite 2 c_view_cat_simpl_l; exact H.
    - cbn; rewrite 2 c_view_cat_simpl_r.
      cbn; rewrite a_ren_l_id, a_cat_id.
      symmetry; apply v_var_sub.
  Qed.
(*|
Machine Strategy (Def 5.19)
===========================

We define active and passive states of the machine strategy. Active states consist of
the pair of a language configuration and an active OGS assignement. Passive states consist
solely of a passive OGS assignement.

.. coq::
   :name: machinestate
|*)
  Record m_strat_act Δ (Φ : ogs_ctx) : Type := MS {
    ms_conf : conf (Δ +▶ ↓⁺Φ) ;
    ms_env : ogs_env Δ Act Φ ;
  }.
  #[global] Arguments MS {Δ Φ}.
  #[global] Arguments ms_conf {Δ Φ}.
  #[global] Arguments ms_env {Δ Φ}.

  Definition m_strat_pas Δ : psh ogs_ctx := ogs_env Δ Pas.
(*|
Next we define the action and reaction morphisms of the machine strategy. First
``m_strat_wrap`` provides the active transition given an already evaluated normal form,
such that the action morphism ``m_strat_play`` only has to evaluate the active part
of the state. ``m_strat_resp`` mostly is a wrapper around ``oapp``, our analogue to
the embedding from normal forms to language configurations present in the paper.

.. coq::
   :name: machineplay
|*)
  Definition m_strat_wrap {Δ Φ} (γ : ogs_env Δ Act Φ)
     : nf _ _ (Δ +▶ ↓⁺ Φ) -> (obs∙ Δ + h_actv ogs_hg (m_strat_pas Δ) Φ) :=
      fun n =>
        match c_view_cat (nf_var n) with
        | Vcat_l i => inl (i ⋅ nf_obs n)
        | Vcat_r j => inr ((j ⋅ nf_obs n) ,' (γ ;⁻ nf_args n))
        end .

  Definition m_strat_play {Δ Φ} (ms : m_strat_act Δ Φ)
    : delay (obs∙ Δ + h_actv ogs_hg (m_strat_pas Δ) Φ)
    := fmap_delay (m_strat_wrap ms.(ms_env)) (eval ms.(ms_conf)).

  Definition m_strat_resp {Δ Φ} (γ : m_strat_pas Δ Φ)
    : h_pasv ogs_hg (m_strat_act Δ) Φ
    := fun m =>
         {| ms_conf := (ₐ↓γ _ (m_var m) ᵥ⊛ᵣ r_cat3_1) ⊙ (m_obs m)⦗r_cat_rr ᵣ⊛ a_id⦘ ;
            ms_env := γ ;⁺ |} .
(*|
These action and reaction morphisms define a coalgebra, which we now embed into the
final coalgebra by looping them coinductively. This constructs the indexed interaction
tree arising from starting the machine strategy at a given state.
|*)
   Definition m_strat {Δ} : m_strat_act Δ ⇒ᵢ ogs_act Δ :=
    cofix _m_strat Φ e :=
       subst_delay
         (fun r => go match r with
          | inl m        => RetF m
          | inr (x ,' p) => VisF x (fun r : ogs_e.(e_rsp) _ => _m_strat _ (m_strat_resp p r))
          end)
         (m_strat_play e).
(*|
We also provide a wrapper for the passive version of the above map.
|*)
  Definition m_stratp {Δ} : m_strat_pas Δ ⇒ᵢ ogs_pas Δ :=
    fun _ x m => m_strat _ (m_strat_resp x m).
(*|
We define the notion of equivalence on machine-strategy states given by the weak
bisimilarity of the induced infinite trees. There is an active version, and a passive
version, working pointwise.
|*)
  Definition m_strat_act_eqv {Δ} : relᵢ (m_strat_act Δ) (m_strat_act Δ) :=
    fun i x y => m_strat i x ≈ m_strat i y.
  Notation "x ≈ₐ y" := (m_strat_act_eqv _ x y).

  Definition m_strat_pas_eqv {Δ} : relᵢ (m_strat_pas Δ) (m_strat_pas Δ) :=
    fun i x y => forall m, m_strat_resp x m ≈ₐ m_strat_resp y m .
  Notation "x ≈ₚ y" := (m_strat_pas_eqv _ x y).
(*|
A technical lemma explaining how the infinite strategy unfolds.
|*)
  Lemma unfold_mstrat {Δ a} (x : m_strat_act Δ a) :
    m_strat a x
    ≊ subst_delay
         (fun r => go match r with
          | inl m        => RetF m
          | inr (x ,' p) => VisF x (fun r : ogs_e.(e_rsp) _ => m_strat _ (m_strat_resp p r))
          end)
         (m_strat_play x).
  Proof.
    apply it_eq_unstep; cbn.
    destruct (_observe (eval (ms_conf x))); cbn.
    - destruct (m_strat_wrap (ms_env x) r); cbn.
      now econstructor.
      destruct h; econstructor; intro.
      apply it_eq_t_equiv.
    - econstructor; apply (subst_delay_eq (RX := eq)).
      intros ? ? <-; apply it_eq_unstep; cbn.
      destruct x0; cbn.
      + now econstructor.
      + destruct s; econstructor; intro; now apply it_eq_t_equiv.
      + now apply it_eq_t_equiv.
    - destruct q.
  Qed.
(*|
Next we construct the initial states. The active initial state is given by simply a
configuration from the language machine while a passive initial state is given by
an assignment into the final context Δ.

.. coq::
   :name: initstate
|*)
   Definition inj_init_act Δ {Γ} (c : conf Γ) : m_strat_act Δ (∅ₓ ▶ₓ Γ) :=
    {| ms_conf := c ₜ⊛ᵣ (r_cat_r ᵣ⊛ r_cat_r) ; ms_env := ε⁻ ;⁺ |}.

  Definition inj_init_pas {Δ Γ} (γ : Γ =[val]> Δ) : m_strat_pas Δ (∅ₓ ▶ₓ Γ) :=
    ε⁺ ;⁻ (γ ⊛ᵣ r_cat_l).
(*|
This defines a notion of equivalence on the configurations of the language: bisimilarity
of the induced strategies.
|*)
  Definition m_conf_eqv Δ : relᵢ conf conf :=
    fun Γ u v => inj_init_act Δ u ≈ₐ inj_init_act Δ v .
(*|
Finally we define composition of two matching machine-strategy states.
|*)
  Record reduce_t (Δ : C) : Type := RedT {
    red_ctx : ogs_ctx ;
    red_act : m_strat_act Δ red_ctx ;
    red_pas : m_strat_pas Δ red_ctx
  } .
  #[global] Arguments RedT {Δ Φ} u v : rename.
  #[global] Arguments red_ctx {Δ}.
  #[global] Arguments red_act {Δ}.
  #[global] Arguments red_pas {Δ}.
(*|
First the composition equation.

.. coq::
   :name: compeqn
|*)
  Definition compo_body {Δ} (x : reduce_t Δ)
    : delay (reduce_t Δ + obs∙ Δ)
    := fmap_delay (fun r => match r with
                  | inl r => inr r
                  | inr e => inl (RedT (m_strat_resp x.(red_pas) (projT1 e)) (projT2 e))
                  end)
                  (m_strat_play x.(red_act)).
  
(*|
Then its naive fixpoint.

.. coq::
   :name: componaive
|*)
  Definition compo {Δ a} (u : m_strat_act Δ a) (v : m_strat_pas Δ a)
    : delay (obs∙ Δ)
    := iter_delay compo_body (RedT u v).
End with_param.
(*|
Finally we expose a bunch of notations to make everything more readable.
|*)
#[global] Notation "'ε⁺'" := (ENilA).
#[global] Notation "'ε⁻'" := (ENilP).
#[global] Notation "u ;⁺" := (EConA u).
#[global] Notation "u ;⁻ e" := (EConP u e).
#[global] Notation "ₐ↓ γ" := (collapse γ).
#[global] Notation "u ∥ v" := (compo u v).
#[global] Notation "x ≈ₐ y" := (m_strat_act_eqv _ x y).
#[global] Notation "x ≈ₚ y" := (m_strat_pas_eqv _ x y).
#[global] Notation "x ≈⟦ogs Δ ⟧≈ y" := (m_conf_eqv Δ _ x y).
