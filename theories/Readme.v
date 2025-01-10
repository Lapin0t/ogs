(*|
============================================================
An abstract, certified account of operational game semantics
============================================================

This is the companion artifact to the ESOP paper. The main contributions of
this library are:

- an independent implementation of an indexed counterpart to the
  InteractionTree Coq library with support for guarded and eventually guarded
  recursion
- an abstract OGS model of an axiomatised language proven sound w.r.t.
  substitution equivalence
- several instantiations of this abstract result to concrete
  languages: simply-typed lambda-calculus with recursive functions,
  untyped lambda calculus, Downen and Ariola's polarized system D and
  system L.

Meta
----

- Author(s):

  - Peio Borthelle
  - Tom Hirschowitz
  - Guilhem Jaber
  - Yannick Zakowski

- License:  GPLv3
- Compatible Coq versions: 8.17
- Additional dependencies:

  - dune
  - `Equations <https://github.com/mattam82/Coq-Equations>`_
  - `Coinduction <https://github.com/damien-pous/coinduction>`_
  - `Alectryon <https://github.com/cpitclaudel/alectryon>`_

- Coq namespace: ``OGS``
- `Documentation <https://lapin0t.github.io/ogs/Readme.html>`_


Getting Started
---------------

To simply typecheck the Coq proofs, we provide a Docker image preloaded with
all the dependencies. The instructions to run it are given below. If instead
you want to manually install the OGS library on your own system, follow the
instructions from the section "Local Installation" at the end of the file.

First, ensure that your docker daemon is running.

We recommend building the docker image from source, by executing the following
command from the root of the repository. Note that this requires network access
and will download around 1.5GiB from ``hub.docker.com``.

.. code:: shell

   make docker-build

Alternatively, if you prefer, you can download the precompiled image
``docker_coq-ogs.tar.gz`` from the
`Zenodo archive <https://doi.org/10.5281/zenodo.14627318>`_ of this artifact,
and load it into docker with the following command.

.. code:: shell

   docker image load -i path/to/docker_coq-ogs.tar.gz

After the image is built or loaded from the file, verify that it is indeed
listed by the following command.

.. code:: shell

   docker image ls coq-ogs:latest

This image contains the full code artifact in the directory ``/home/coq/ogs``. The
default command for the image typechecks the whole repository. Run it with a
tty to see the progress with the following command. This should take around
3-5min and conclude by displaying information about several soudness theorems.

.. code:: shell

   docker run --tty coq-ogs:latest

Step-by-Step Reproduction
-------------------------

The above "Getting Started" section already describes how to typecheck the
whole repository, validating our claims of certification from the paper. The
concluding output arises from a special file which we have included,
`Checks.v <Checks.html>`_, which imports core theorems, displays their type and list
of arguments, as well as the assumptions (axioms) they depend on.

If you wish to further inspect the repository, the following command will
start an interactive shell inside the container.

.. code:: shell

   docker run --tty --interactive coq-ogs:latest

The following section details in more precision the content of each file
and their relationship to the paper. We have furthermore tried to thoroughly
comment most parts of the development. If you prefer to navigate the code
in a web browser, an HTML rendering of the whole code together with the proof
state during intermediate steps is provided at the following URL:

https://lapin0t.github.io/ogs/Readme.html

Content
-------

Structure of the repository
^^^^^^^^^^^^^^^^^^^^^^^^^^^

The Coq source code is contained in the ``theory/`` directory, which has the
following structure, in approximate order of dependency.

- `Readme.v <Readme.html>`_: This file.
- `Prelude.v <Prelude.html>`_: Imports and setup.
- ``Utils/`` directory: general utilities.

  - [Rel.v](https://lapin0t.github.io/ogs/Rel.html): Generalities for relations
    over type families.
  - [Psh.v](https://lapin0t.github.io/ogs/Psh.html): Generalities for type
    families.

- ``Ctx/`` directory: general metatheory of substitution. This material has been
  largely left untold in the paper, and as explained in the artifact report, we
  introduce a novel gadget for abstracting over scope and variable
  representations.

  - `Family.v <Family.html>`_: Definition of scoped
    and sorted families (Def. 4).
  - `Abstract.v <Abstract.html>`_: Definition of
    scope structures. The comments make this file a good entry-point to the
    understand the constructions from this directory.
  - `Assignment.v <Assignment.html>`_: Generic
    definition of assignments (Def. 5 and 6).
  - `Renaming.v <Renaming.html>`_: Generic
    definition of renamings as variable assignments, together with their
    important equational laws.
  - `Ctx.v <Ctx.html>`_: Definition of concrete
    contexts (lists) and dependently-typed DeBruijn indices.
  - `Covering.v <Covering.html>`_: Instanciation of
    the scope structure for concrete contexts from
    `Ctx.v <Ctx.html>`_.
  - `DirectSum.v <DirectSum.html>`_: Direct sum of
    scope structures.
  - `Subset.v <Subset.html>`_: Sub-scope structure.
  - `Subst.v <Subst.html>`_: Axiomatization of
    substitution monoid and substitution module (Def. 7 and 8), axiomatization of
    clear-cut variables (Def. 27).

- ``ITree/`` directory: implementation of a variant of interaction trees
  over indexed types.

  - `Event.v <Event.html>`_: Indexed events (i.e.,
    indexed containers) parameterizing the interactions of an itree.
  - `ITree.v <ITree.html>`_: Coinductive definition.
  - `Eq.v <Eq.html>`_: Strong and weak bisimilarity
    over interaction trees.
  - `Structure.v <Structure.html>`_: Combinators
    (definitions) for the monadic structure and unguarded iteration (Def. 31).
  - `Properties.v <Properties.html>`_: General
    properties of the combinators (Prop. 3).
  - `Guarded.v <Guarded.html>`_: (Eventually)
    guarded equations and iterations over them, together with their unicity
    property (Def. 30, 33 and 34 and Prop. 5).
  - `Delay.v <Delay.html>`_: Definition of the
    delay monad (as a special case of interaction trees over the empty event)
    (Def. 9 and 10).
- ``OGS/`` directory: construction of a sound OGS model for an abstract language
  machine.

  - `Obs.v <Obs.html>`_: Axiomatization of
    observation structure (Def. 12) and normal forms (part of Def. 13).
  - `Machine.v <Machine.html>`_: Axiomatization of
    evaluation structures (Def. 11), language machines (Def. 13) and focused
    redexes (Def. 28).
  - `Game.v <Game.html>`_: Abstract games (Def. 16
    and 18) and OGS game definition (Def. 21--23).
  - `Strategy.v <Strategy.html>`_: Machine strategy
    (Def. 24--26) and composition.
  - `CompGuarded.v <CompGuarded.html>`_: Proof of
    eventual guardedness of the equation defining the composition of strategies
    (Prop. 6).
  - `Adequacy.v <Adequacy.html>`_: Proof of
    adequacy of composition (Prop. 7).
  - `Congruence.v <Congruence.html>`_: Proof of
    congruence of composition (Prop. 4).
  - `Soundness.v <Soundness.html>`_: Proof of
    soundness of the OGS (Thm. 8).

- ``Examples/`` directory: concrete language machines instanciating the generic
  construction and soundness theorem.

  - `STLC_CBV.v <STLC_CBV.html>`_: Simply typed,
    call-by-value, lambda calculus, with a unit type and recursive functions.
    This example is the most commented, with a complete walk-through of the
    instanciation.
  - `ULC_CBV.v <ULC_CBV.html>`_: Pure, untyped,
    call-by-value, lambda calculus. This example demonstrate that the
    intrinsically typed and scoped approach still handles untyped calculi, by
    treating them as "unityped".
  - `SystemD.v <SystemD.html>`_: Mu-mu-tilde
    calculus variant System D from Downen and Ariola, polarized. This is
    our "flagship" example, as it is a very expressive calculus. We have
    dropped existential and universal type quantifier as our framework only
    captures simple types. We have added a slightly ad-hoc construction to
    enable general recursion, making the calculus non-normalizing.
  - `SystemL_CBV.v <SystemL_CBV.html>`_:
    mu-mu-tilde calculus variant System L, in call by value
    (i.e., lambda-bar-mu-mu-tilde-Q calculus from Herbelin and Curien).
- `Checks.v <Checks.html>`_: Interactively display
  information about the most important theorems.

Axioms
------

The whole development relies only on axiom K, a conventional and sound axiom
from Coq's standard library (more precisely, :coqid:`Coq.Logic.Eqdep#Eq_rect_eq.eq_rect_eq`).
It is used by ``Equations`` to perform some dependent pattern matching.

This fact can be verified from the output of typechecking `Checks.v <Checks.html>`_. It can
also be double checked in an interactive mode.

- For the abstract result of soundness of the OGS by running
  ``Print Assumptions ogs_correction.`` at the end of
  `Soundness.v <Soundness.html>`_.
- For any particular example, for instance by running
  ``Print Assumptions stlc_ciu_correct.`` at the end of
  `STLC_CBV.v <STLC_CBV.html>`_.

Local Installation
------------------

The most convenient way to experiment and develop with this library is to
install Coq locally and use some IDE such as emacs. To do so, first ensure you
have the source code for the project or download it with the following command.

.. code:: shell

   git clone -b esop25 https://github.com/lapin0t/ogs.git
   cd ogs

To install the Coq dependencies, first ensure you have a working opam
installation. This should usually be obtained from your systems package
distribution, see https://opam.ocaml.org/doc/Install.html for further
information.

Check if you have added the ``coq-released`` package repository with the command
``opam repo``. If it does not appear, add it with the following command.

.. code:: shell

   opam repo add coq-released https://coq.inria.fr/opam/released

Then, from the root of the repository, install the dependencies with
the following command

.. code:: shell

   opam install --deps-only .

We stress that the development has been only checked to compile against these
specific dependencies. In particular, it does not compiled at the moment
against latest version of ``coq-coinduction`` due to major changes in the API.

Finally, typecheck the code with the following command, again from the root of
the repository. This should take around 3-5min.

.. code:: shell

   dune build

Generating the Alectryon documentation
--------------------------------------

To build the html documentation, first install Alectryon:

.. code:: shell

   opam install "coq-serapi==8.17.0+0.17.3"
   python3 -m pip install --user alectryon

Then build the documentation with the following command.

.. code:: shell

   make doc

The html should now be generated in the ``docs`` folder. You can start a
local web server to view it with:

.. code:: shell

   make serve
|*)
