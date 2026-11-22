FROM ocaml/opam:debian-12-ocaml-5.3

USER root
RUN apt-get update \
    && apt-get install -y --no-install-recommends libgmp-dev pkg-config python3 \
    && rm -rf /var/lib/apt/lists/*

USER opam
WORKDIR /home/opam
ARG OPAM_JOBS=4
# BINSEC detects these optional libraries at build time.
RUN opam install --yes --jobs="$OPAM_JOBS" 'bitwuzla>=1.0.5' 'unisim_archisec>=0.0.10'

COPY --chown=opam:opam outside_tools/binsec_no_simplification/ /opt/greysynth-deps/binsec/
COPY --chown=opam:opam outside_tools/xyntia/ /opt/greysynth-deps/xyntia/
RUN opam pin add --yes --no-action --kind=path binsec /opt/greysynth-deps/binsec \
    && opam pin add --yes --no-action --kind=path xyntiasampler /opt/greysynth-deps/xyntia \
    && opam pin add --yes --no-action --kind=path xyntia /opt/greysynth-deps/xyntia \
    && opam install --yes --jobs="$OPAM_JOBS" binsec xyntia xyntiasampler goblint-cil.2.0.8 yojson containers \
    && opam clean --yes

# Dev Containers can run commands without the base image's `opam exec` entrypoint.
ENV PATH="/home/opam/.opam/5.3/bin:${PATH}"
