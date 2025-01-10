FROM coqorg/coq:8.17.1

RUN set -x \
  && opam --yes update \
  && opam --yes pin add coq-equations 1.3+8.17 \
  && opam --yes pin add coq-coinduction 1.6

COPY --chown=coq:coq . /home/coq/ogs

WORKDIR /home/coq/ogs
CMD dune build
