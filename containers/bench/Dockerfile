# syntax=docker/dockerfile:1.12

ARG HASKELL_IMAGE=haskell:9.14.1-slim-bookworm@sha256:601cd4d016fa21c820deefd277b2ec94a3fb6688635ceed3573042aa2764a2d3
ARG RUNTIME_IMAGE=debian:bookworm-slim@sha256:817e6cf99d6fc127ff4ffe8580049b60deba0adfbbb2bd65ddc3ef8fbb7aade0

FROM ${HASKELL_IMAGE} AS build

ARG ELAN_VERSION=v4.2.3
ARG ELAN_SHA256=cb69af0803b04157bc30201c29c12fca882bb3ad8b43476b8d2d3064810bc3ac
ARG LARA_GIT_REV

ENV DEBIAN_FRONTEND=noninteractive \
    PATH=/root/.elan/bin:${PATH}

RUN apt-get update \
    && apt-get install -y --no-install-recommends ca-certificates curl git make zstd \
    && rm -rf /var/lib/apt/lists/*

RUN curl --fail --location --silent --show-error \
      "https://github.com/leanprover/elan/releases/download/${ELAN_VERSION}/elan-aarch64-unknown-linux-gnu.tar.gz" \
      --output /tmp/elan.tar.gz \
    && echo "${ELAN_SHA256}  /tmp/elan.tar.gz" | sha256sum --check --strict \
    && tar -xzf /tmp/elan.tar.gz -C /tmp \
    && /tmp/elan-init -y --default-toolchain none \
    && rm -f /tmp/elan.tar.gz /tmp/elan-init

WORKDIR /src

COPY lean/lean-toolchain lean/lean-toolchain
RUN elan toolchain install "$(cat lean/lean-toolchain)"

COPY lara.cabal README.md LICENSE ./
COPY containers/bench/cabal.project containers/bench/cabal.project.freeze containers/bench/
COPY src src
COPY app app
COPY scripts/bench.hs scripts/bench.hs
COPY test test
RUN cabal update \
    && cabal build --project-file=containers/bench/cabal.project \
      --only-dependencies exe:lara exe:lara-bench

COPY lean lean
COPY fixtures fixtures
COPY corpus-units corpus-units

RUN test -n "${LARA_GIT_REV}" \
    && cabal build --project-file=containers/bench/cabal.project exe:lara exe:lara-bench \
    && (cd lean && lake build) \
    && install -D "$(cabal list-bin --project-file=containers/bench/cabal.project exe:lara-bench)" /opt/lara/bin/lara-bench \
    && install -D lean/.lake/build/bin/lara-driver /opt/lara/lean/.lake/build/bin/lara-driver

FROM ${RUNTIME_IMAGE} AS runtime

ARG LARA_GIT_REV
LABEL org.opencontainers.image.revision="${LARA_GIT_REV}"

ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8 \
    TZ=UTC \
    LARA_BENCH_GIT_REV=${LARA_GIT_REV} \
    LARA_BENCH_GHC_VERSION=9.14.1 \
    LARA_BENCH_LEAN_VERSION="Lean 4.32.0"

RUN apt-get update \
    && apt-get install -y --no-install-recommends libffi8 libgmp10 libstdc++6 \
    && rm -rf /var/lib/apt/lists/* \
    && groupadd --gid 10001 lara \
    && useradd --uid 10001 --gid 10001 --create-home lara

WORKDIR /workspace

COPY --from=build /opt/lara/bin/lara-bench /usr/local/bin/lara-bench
COPY --from=build /opt/lara/lean lean
COPY --from=build /src/fixtures fixtures
COPY --from=build /src/corpus-units corpus-units

USER lara
ENTRYPOINT ["/usr/local/bin/lara-bench", "--prebuilt", "--output-dir", "/out"]
