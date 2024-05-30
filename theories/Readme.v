(*|
============================================================
An abstract, certified account of operational game semantics
============================================================

This is the companion artifact to the paper. The main contributions of this
library are:

- an independent implementation of an indexed counterpart to the itree library
  with support for guarded and eventually guarded recursion
- an abstract OGS model of an axiomatised language proven sound w.r.t.
  substitution equivalence
- several instantiations of this abstract result to concrete languages:
  simply-typed lambda-calculus with recursive functions, untyped lambda
  calculus, Downen and Ariola's polarized system D and system L.

Meta
----

- Author(s): ANONYMISED
- License:  GPLv3
- Compatible Coq versions: 8.17
- Additional dependencies:
  - dune
  - `Equations <https://github.com/mattam82/Coq-Equations>`_
  - `Coinduction <https://github.com/damien-pous/coinduction>`_
  - `Alectryon <https://github.com/cpitclaudel/alectryon>`_
- Coq namespace: ``OGS``
- Documentation: TODO

Building instructions
---------------------

Installing dependencies
^^^^^^^^^^^^^^^^^^^^^^^

Download the project with

.. code:: shell

   git clone TODO
   cd ogs

We stress that the development has been only checked to compile against these specific dependencies.
In particular, it does not compiled at the moment against latest version of coq-coinduction due to major changes in the interface.

Installing the opam dependencies automatically:

.. code:: shell

   opam install --deps-only .

or manually:

.. code:: shell

   opam pin coq 8.17
   opam pin coq-equations 1.3
   opam pin coq-coinduction 1.6

Building the project
^^^^^^^^^^^^^^^^^^^^

... code:: shell

    dune build

Alectryon documentation
^^^^^^^^^^^^^^^^^^^^^^^

To build the html documentation, first install Alectryon:

.. code:: shell

   opam install "coq-serapi==8.17.0+0.17.1"
   python3 -m pip install --user alectryon

The build with:

.. code:: shell

   make doc

You can start a local web server to view it with:

.. code:: shell

   make serve

Content
-------

Structure of the repository
^^^^^^^^^^^^^^^^^^^^^^^^^^^

The Coq development is contained in the theory directory, which has the following structure,
in approximate order of dependency.

- `Prelude.v <Prelude.html>`_: imports and setup
- Utils directory: general utilities

  - `Rel.v <Rel.html>`_: generalities for relations over indexed types
  - `Psh.v <Psh.html>`_: generalities for type families

- Ctx directory: general theory of contexts and variables

  - `Family.v <Family.html>`_: definition of scoped and sorted families
  - `Abstract.v <Abstract.html>`_: definition of context and variable structure
  - `Assignment.v <Assignment.html>`_: generic definition of assignments
  - `Renaming.v <Renaming.html>`_: generic definition of renamings
  - `Ctx.v <Ctx.html>`_: definition of concrete contexts and DeBruijn indices
  - `Covering.v <Covering.html>`_: concrete context structure for Ctx.v
  - `DirectSum.v <DirectSum.html>`_: direct sum of context structures
  - `Subset.v <Subset.html>`_: sub context structure

- ITree directory: implementation of a variant of interaction trees over indexed types

  - `Event.v <Event.html>`_: indexed events parameterizing the interactions of an itree
  - `ITree.v <ITree.html>`_: coinductive definition
  - `Eq.v <Eq.html>`_: strong and weak bisimilarity over interaction trees
  - `Structure.v <Structure.html>`_: combinators (definitions)
  - `Properties.v <Properties.html>`_: general theory
  - `Guarded.v <Guarded.html>`_: (eventually) guarded equations and iterations over them
  - `Delay.v <Delay.html>`_: definition of the delay monad (as a special case of trees)

- OGS directory: construction of a sound OGS model for an abstract language

  - `Subst.v <Subst.html>`_: axiomatization of substitution monoid, substitution
    module
  - `Obs.v <Obs.html>`_: axiomatization of observation structure, normal forms
  - `Machine.v <Machine.html>`_: axiomatization of evaluation structures,
    language machine
  - `Game.v <Game.html>`_: abstract game and OGS game definition
  - `Strategy.v <Strategy.html>`_: machine strategy and composition
  - `CompGuarded.v <CompGuarded.html>`_: proof of eventual guardedness of the
    composition of strategies
  - `Adequacy.v <Adequacy.html>`_: proof of adequacy of composition
  - `Congruence.v <Congruence.html>`_: proof of congruence of composition
  - `Soundness.v <Soundness.html>`_: proof of soundness of the OGS

- Examples directory: concrete instances of the generic construction

  - `STLC_CBV.v <STLC_CBV.html>`_: simply typed, call by value, lambda calculus
  - `ULC_CBV.v <ULC_CBV.html>`_: untyped, call by value, lambda calculus
  - `SystemL_CBV.v <SystemL_CBV.html>`_: mu-mu-tilde calculus variant System L,
    in call by value
  - `SystemD.v <SystemD.html>`_: mu-mu-tilde calculus variant System D, polarized

Axioms
^^^^^^

The whole development relies only on axiom K, a conventional and sound axiom
from Coq's standard library (more precisely, :coqid:`Coq.Eqdep.Eq_rect_eq.eq_rect_eq`).

This can be double checked as follows:

- for the abstract result of soundness of the OGS by running ``Print
  Assumptions ogs_correction.`` at the end of OGS/Soundness.v
- for any particular example, for instance by running ``Print Assumptions
  stlc_ciu_correct.`` at the end of Example/CBVTyped.v
|*)
