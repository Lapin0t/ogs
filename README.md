# An abstract, certified account of operational game semantics

This development is a companion to the LICS'24 submission "An abstract, certified account of operational game semantics".
It has been rendered anonymous for the purpose of submission.

The main contribution of this library are:
- an independent implementation of an indexed counterpart to the itree library with support for guarded and eventually guarded recursion
- an abstract OGS model of an axiomatized language proven sound
- several instantiating of the abstract result to concrete languages

## Meta

- Author(s): REDACTED
- License:  GPLv3
- Compatible Coq versions: 8.17
- Additional dependencies:
  - dune
  - [Equations](https://github.com/mattam82/Coq-Equations)
  - [Coinduction](https://github.com/damien-pous/coinduction)
- Coq namespace: `OGS`

## Building instructions

### Obtaining the project

```shell
git clone TODO
cd ogs
```

### Installing dependencies

We stress that the development has been only checked to compile against these specific dependencies.
In particular, it does not compiled at the moment against latest version of coq-coinduction due to major changes in the interface.

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
  + [Rel](./theories/Utils/Rel.v) : Generalities for relations over indexed types
  + [Psh](./theories/Utils/Psh.v) : Generalities for type families
  + [Ctx](./theories/Utils/Ctx.v) : Well-scoped contexts
- [ITree](./theories/ITree/) : Implementation of a variant of Interaction Trees over indexed types
  + [Event](./theories/ITree/EVent.v) : Indexed events parameterizing the interactions of an itree
  + [ITree](./theories/ITree/ITree.v) : Data-structure
  + [Structure](./theories/ITree/Structure.v) : Combinators (definitions)
  + [Eq](./theories/ITree/Eq.v) : Strong (≅) and weak bisimilarity (≈) over trees
  + [Properties](./theories/ITree/Properties.v) : General theory
  + [Guarded](./theories/ITree/Guarded.v) : (Eventually) Guarded equations and iterations over them (Section 7.4)
  + [Delay](./theories/ITree/Delay.v) : The Delay Monad (Section 1, Remark 1) is taken as the type of trees over the empty signature in the development.
- [OGS](./theories/OGS/) : Construction of a sound OGS for an abstract language
  + [Subst](./theories/OGS/Subst.v) : Substitution monoid, substitution module
  + [Obs](./theories/OGS/Obs.v) : Observation Structure
  + [Machine](./theories/Machine.v) : Evaluation Structure, finishing the definition of the abstract machine
  + [Game](./theories/OGS/Game.v) : OGS game
  + [Strategy](./theories/OGS/Strategy.v) : OGS strategies and composition of strategies
  + [CompGuarded](./theories/OGS/CompGuarded.v) : Proof of eventual guardedness of the composition of strategies
  + [Adequacy](./theories/OGS/Adequacy.v) : Proof of adequacy of the composition
  + [Congruence](./theories/OGS/Congruence.v) : Proof that weak bismilarity is a congruence for composition
  + [Soundness](./theories/OGS/Soundness.v) : Proof of soundness of the OGS
- [Examples](./theories/Examples/) : Concrete instances of the abstract construction
  + [CBVTyped](./theories/Examples/Lambda/CBVTyped.v) : Typed, call by value, lambda calculus
  + [CBVUntyped](./theories/Examples/Lambda/CBVUntyped.v) : Untyped, call by value, lambda calculus
  + [CBVSystemL](./theories/Examples/Lambda/CBVUntyped.v) : Untyped, call by value, lambda calculus
  + [CBVSystemL](./theories/Examples/Mu/CBVSystemL.v) : SystemL, call by value
  + [PolarizedSystemD](./theories/Examples/Mu/PolarizedSystemD.v) : SystemD, polarized
  + [PolarizedSystemL](./theories/Examples/Mu/PolyrizedSystemL.v) : SystemL, polarized

### Axioms

The whole development relies only on axiom K, a conventional and sound axiom from Coq's standard library (more precisely, [Eqdep.Eq_rect_eq.eq_rect_eq]).
This can be double checked as follows:
- for the abstract result of soundness of the OGS by running [Print Assumptions ogs_correction.] at the end of [OGS/Soundness.v]
- for any particular example, for instance by running [Print Assumptions stlc_ciu_correct.] at the end of [Example/CBVTyped.v]

