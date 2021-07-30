# Operational Game Semantics

We investigate the formalization of Coq of Operational Game Semantics.
We aim to encode the approach using the itree library.

## Meta

- Author(s):
  - Peio Borthelle
  - Guilhem Jaber
  - Yannick Zakowski
- License: TODO
- Compatible Coq versions: 8.12 or later
- Additional dependencies:
  - [InteractionTrees](https://github.com/DeepSpec/InteractionTrees) master
- Coq namespace: `OGS`

## Building instructions

### Installing dependencies

The current only dependency, Interaction Trees, is provided as a git submodule
in order to stay more easily in synchronization with its master branch.
We will eventually move this dependency to Opam.

### Obtaining the project

```shell
git clone --recurse-submodule https://gitlab.inria.fr/yzakowsk/ogs-coq
cd ogc-coq
```

### Building the project using coq_makefile

```shell
coq_makefile -f _CoqProject -o Makefile  # in case you want to regenerate it
make                                     # or make -j <number-of-cores-on-your-machine>
```

### Building the html documentation

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
