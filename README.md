# An abstract, certified account of operational game semantics

This is the companion artifact to the ESOP paper. The main contributions of
this library are:

- an independent implementation of an indexed counterpart to the
  InteractionTree Coq library with support for guarded and eventually guarded
  recursion
- an abstract OGS model of an axiomatised language proven sound w.r.t.
  substitution equivalence
- several instantiations of this abstract result to concrete
  languages: simply-typed lambda-calculus with recursive functions,
  untyped lambda calculus, Downen and Ariola\'s polarized system D and
  system L.

## Meta

- Author(s):
  - Peio Borthelle
  - Tom Hirschowitz
  - Guilhem Jaber
  - Yannick Zakowski
- License: GPLv3
- Compatible Coq versions: 8.17
- Additional dependencies:
  - dune
  - [Equations](https://github.com/mattam82/Coq-Equations)
  - [Coinduction](https://github.com/damien-pous/coinduction)
  - [Alectryon](https://github.com/cpitclaudel/alectryon)
- Coq namespace: `OGS`
- [Documentation](https://lapin0t.github.io/ogs/Readme.html)

## Getting Started

### Installing the dependencies

Download the project with

``` shell
git clone -b esop25 https://github.com/lapin0t/ogs.git
cd ogs
```

We stress that the development has been only checked to compile against
these specific dependencies. In particular, it does not compiled at the
moment against latest version of `coq-coinduction` due to major changes in
the interface.

Installing the opam dependencies automatically:

``` shell
opam install --deps-only .
```

or manually:

``` shell
opam pin coq 8.17
opam pin coq-equations 1.3
opam pin coq-coinduction 1.6
```

### Typechecking the Coq code

``` shell
dune build
```

### Generating the Alectryon documentation

To build the html documentation, first install Alectryon:

``` shell
opam install "coq-serapi==8.17.0+0.17.1"
python3 -m pip install --user alectryon
```

Then build with:

``` shell
make doc
```

You can start a local web server to view it with:

``` shell
make serve
```

## Content

### Structure of the repository

The Coq development is contained in the theory directory, which has the
following structure, in approximate order of dependency.

- [Readme.v](https://lapin0t.github.io/ogs/Readme.html): this file
- [Prelude.v](https://lapin0t.github.io/ogs/Prelude.html): imports and setup
- Utils directory: general utilities
  - [Rel.v](https://lapin0t.github.io/ogs/Rel.html): generalities for relations over indexed types
  - [Psh.v](https://lapin0t.github.io/ogs/Psh.html): generalities for type families
- Ctx directory: general theory of contexts and variables
  - [Family.v](https://lapin0t.github.io/ogs/Family.html): definition of scoped and sorted
    families
  - [Abstract.v](https://lapin0t.github.io/ogs/Abstract.html): definition of context and variable
    structure
  - [Assignment.v](https://lapin0t.github.io/ogs/Assignment.html): generic definition of
    assignments
  - [Renaming.v](https://lapin0t.github.io/ogs/Renaming.html): generic definition of renamings
  - [Ctx.v](https://lapin0t.github.io/ogs/Ctx.html): definition of concrete contexts and DeBruijn
    indices
  - [Covering.v](https://lapin0t.github.io/ogs/Covering.html): concrete context structure for
    Ctx.v
  - [DirectSum.v](https://lapin0t.github.io/ogs/DirectSum.html): direct sum of context structures
  - [Subset.v](https://lapin0t.github.io/ogs/Subset.html): sub context structure
- ITree directory: implementation of a variant of interaction trees
  over indexed types
  - [Event.v](https://lapin0t.github.io/ogs/Event.html): indexed events parameterizing the
    interactions of an itree
  - [ITree.v](https://lapin0t.github.io/ogs/ITree.html): coinductive definition
  - [Eq.v](https://lapin0t.github.io/ogs/Eq.html): strong and weak bisimilarity over interaction
    trees
  - [Structure.v](https://lapin0t.github.io/ogs/Structure.html): combinators (definitions)
  - [Properties.v](https://lapin0t.github.io/ogs/Properties.html): general theory
  - [Guarded.v](https://lapin0t.github.io/ogs/Guarded.html): (eventually) guarded equations and
    iterations over them
  - [Delay.v](https://lapin0t.github.io/ogs/Delay.html): definition of the delay monad (as a
    special case of trees)
- OGS directory: construction of a sound OGS model for an abstract
  language
  - [Subst.v](https://lapin0t.github.io/ogs/Subst.html): axiomatization of substitution monoid,
    substitution module
  - [Obs.v](https://lapin0t.github.io/ogs/Obs.html): axiomatization of observation structure,
    normal forms
  - [Machine.v](https://lapin0t.github.io/ogs/Machine.html): axiomatization of evaluation
    structures, language machine
  - [Game.v](https://lapin0t.github.io/ogs/Game.html): abstract game and OGS game definition
  - [Strategy.v](https://lapin0t.github.io/ogs/Strategy.html): machine strategy and composition
  - [CompGuarded.v](https://lapin0t.github.io/ogs/CompGuarded.html): proof of eventual guardedness
    of the composition of strategies
  - [Adequacy.v](https://lapin0t.github.io/ogs/Adequacy.html): proof of adequacy of composition
  - [Congruence.v](https://lapin0t.github.io/ogs/Congruence.html): proof of congruence of
    composition
  - [Soundness.v](https://lapin0t.github.io/ogs/Soundness.html): proof of soundness of the OGS
- Examples directory: concrete instances of the generic construction
  - [STLC_CBV.v](https://lapin0t.github.io/ogs/STLC_CBV.html): simply typed, call by value, lambda
    calculus
  - [ULC_CBV.v](https://lapin0t.github.io/ogs/ULC_CBV.html): untyped, call by value, lambda
    calculus
  - [SystemL_CBV.v](https://lapin0t.github.io/ogs/SystemL_CBV.html): mu-mu-tilde calculus variant
    System L, in call by value
  - [SystemD.v](https://lapin0t.github.io/ogs/SystemD.html): mu-mu-tilde calculus variant System
    D, polarized

### Axioms

The whole development relies only on axiom K, a conventional and sound
axiom from Coq\'s standard library (more precisely,
[`Eq_rect_eq.rect_eq`](https://coq.inria.fr/doc/V8.19.0/stdlib/Coq.Logic.Eqdep.html#Eq_rect_eq.eq_rect_eq).

This can be double checked as follows:

-   for the abstract result of soundness of the OGS by running
    `Print Assumptions ogs_correction.` at the end of OGS/Soundness.v
-   for any particular example, for instance by running
    `Print Assumptions stlc_ciu_correct.` at the end of
    Example/CBVTyped.v
