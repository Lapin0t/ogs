# An abstract, certified account of operational game semantics

This development is a companion to the LICS'24 submission "An abstract, certified account of operational game semantics"

## Meta

- Author(s): REDACTED
- License:  GPLv3
- Compatible Coq versions: 8.17
- Additional dependencies:
  - dune
  - [Equations](https://github.com/mattam82/Coq-Equations)
  - [Coinduction](https://github.com/damien-pous/coinduction)
  - [Alectryon (optional)](https://github.com/cpitclaudel/alectryon)
- Coq namespace: `OGS`

## Building instructions

### Obtaining the project

```shell
git clone TODO
cd ogs
```

### Installing dependencies

Installing the opam dependencies automatically:
```shell
opam install --deps-only .
```
or manually:
```shell
opam pin coq 8.17
opam pin coq-equations 1.3
opam pin coq-coinduction 1.6
```

### Building the project

```shell
dune build
```

## Paper to artifact correspondence

### Structure of the repository

- [Utils](./theories/Utils/) : General utilities
  + [Ctx](./theories/Utils/Ctx.v) : Well-scoped contexts (Section 5.1)
  + [Psh](./theories/Utils/Psh.v) : Generalities for type families
  + [Rel](./theories/Utils/Rel.v) : Generalities for relations over indexed types
- [ITree](./theories/ITree/) : Implementation of a variant of Interaction Trees over indexed types.
  + [ITree](./theories/ITree/ITree.v) : Data-structure
  + [Structure](./theories/ITree/Structure.v) : Combinators (definitions)
  + [Eq](./theories/ITree/Eq.v) : Strong (≅) and weak bisimilarity (≈) over trees.
  + [Properties](./theories/ITree/Properties.v) : General theory
  + [Guarded](./theories/ITree/Guarded.v) : (Eventually) Guarded equations and iterations over them (Section 7.4)
  + [Delay](./theories/ITree/Delay.v) : The Delay Monad (Section 1, Remark 1) is taken as the type of trees over the empty signature in the development.


Note: this repository contains the version of our development restricting internal branching to finite indexes,
and bisimilarity to the homogeneous case, as described in the paper.
As mentioned (footnotes 7, 10 and 11), the theory straightforwardly extends at the cost of a heavier parameterization.
We refer the interested reader to our main active repository for details: https://github.com/vellvm/ctrees/


- theories/: the [ctree] library, containing all of core theory described in Sections 1 to 5
- examples/: our case studies and illustrative examples:
  + examples/Coffee: an encoding of the standard coffee machine example to illustrate the distinction between bisimilarity and trace equivalence (not mentioned in the paper)
  + examples/ImpBr: Imp extended with non-deterministic branching, the motivating example used in Section 2 and 3.
  + examples/ccs: our ccs case study, described in Section 6
  + examples/Yield: our cooperative scheduling case study, described in Section 7

### Correspondence

Every definition and result presented in the paper is annotated with an hyperlink to its formal counter
part on our dedicated branch ( https://github.com/vellvm/ctrees/tree/popl23 ). The Zenodo artifact is an
exact copy of this branch.
We hence recommend the reviewers to favor these hyperlinks as an easy way to track the faithfulness
of our artifact.

As mentioned before, the only exception to this is the one result strictly relying on the
generalized development, i.e. the right hand-side of Lemma 5.2.
This result can be currently found here ( https://github.com/vellvm/ctrees/blob/choice-gen-hsim/theories/Interp/Sched.v#L227 ), but we do not guarantee the long term stability of this exact link.

### Universe issue

Importing simultaneously some parts of the [Interaction Tree] library and of the
[RelationAlgebra] library currently triggers a universe inconsistency. We hence
disable at the moment universe checks in the [theories/Interp/ITree],
[examples/Yield/Lang], and [examples/Yield/Par] files via the [Unset Universe
Checking] option.

This is a purely technical issue that affects in no way the soundness of our results.
We are planning to synchronize with the authors of the respective libraries at play to
find a patch to this issue.
# Dependencies

- coq-equations
- coq-coinduction

To install them with opam, first ensure the coq repository for opam is installed:
```shell
opam repo add coq-released https://coq.inria.fr/opam/released
```

Then install the packages:
```shell
opam install coq coq-equations coq-coinduction
```

# Build

```shell
dune build
```
