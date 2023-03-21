# Operational Game Semantics

We investigate the formalization of Coq of Operational Game Semantics.
We aim to encode the approach using the itree library.

## Meta

- Author(s):
  - Peio Borthelle
  - Tom Hirschowitz
  - Guilhem Jaber
  - Yannick Zakowski
- License: TODO
- Compatible Coq versions: 8.16 or later
- Additional dependencies:
  - dune (>= 3.6)
  - coq-coinduction (>= 1.6)
  - coq-equations (>= 1.3)
- Coq namespace: `OGS`

## Building instructions

### Installing dependencies

Installing the opam dependencies
```shell
opam install dune
opam install coq-coinduction
opam install coq-equations
```

### Obtaining the project

```shell
git clone https://gitlab.inria.fr/yzakowsk/ogs-coq
cd ogc-coq
```

### Building the project using dune

```shell
cd coq
dune build
```

### Building the html documentation

TODO UPDATE

This depends on [alectryon](https://github.com/cpitclaudel/alectryon). First install it with:

```shell
opam install coq-serapi
python3 -m pip install --user alectryon
```

Build with:

```shell
mkdir html-doc
alectryon --output-directory html-doc -Q theories OGS -R ./lib/InteractionTrees/theories ITree theories/{LCD.v,OGSD.v}
```

You should see some html files in the html-doc directory.
