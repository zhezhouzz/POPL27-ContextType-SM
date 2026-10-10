FROM ocaml/opam:ubuntu-22.04-ocaml-4.14@sha256:27a7fbd73a13f2d733442a7ce2ee615599baef66cf4799384596f85af0ae08a9

ARG ROCQ_VERSION=9.1.0
ARG ROCQ_STDLIB_VERSION=9.0.0
ARG STDPP_VERSION=dev.2026-01-23.0.217a887d

USER root
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
      ca-certificates git less libgmp-dev make pkg-config ripgrep vim && \
    rm -rf /var/lib/apt/lists/*
USER opam

RUN opam repo add rocq-released \
      https://rocq-prover.github.io/opam/released/ && \
    opam repo add iris-dev \
      https://gitlab.mpi-sws.org/iris/opam.git && \
    opam update && \
    opam install -y \
      "rocq-core.${ROCQ_VERSION}" \
      "rocq-stdlib.${ROCQ_STDLIB_VERSION}" \
      "rocq-stdpp.${STDPP_VERSION}" && \
    opam clean -a -c -s --logs

WORKDIR /home/opam/context-types
COPY --chown=opam:opam . .

# Building the image checks every proof, including SoundnessAssumptions.v.
RUN opam exec -- make -j"$(nproc)"

ENTRYPOINT ["opam", "exec", "--"]
CMD ["bash"]
