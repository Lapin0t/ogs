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
coq_makefile -f _CoqProject -o Makefile
make
```
