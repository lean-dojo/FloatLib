#!/usr/bin/env bash

set -euo pipefail

campaign=/efs/robert/floatlean-results/332491fd0acb7702b5730aa96bf5927063583d92/20260910T150728Z/ecosystem
suite=${SUITE:?SUITE must name the retry suite}
result_dir="$campaign/results/$suite"
work_dir="/work/$suite"

mkdir -p "$result_dir" "$work_dir"
exec > >(tee "$result_dir/run.log") 2>&1

started=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf 'suite=%s\nstarted=%s\nnode=%s\n' \
  "$suite" "$started" "${NODE_NAME:-unknown}" > "$result_dir/metadata.env"

finish() {
  status=$?
  finished=$(date -u +%Y-%m-%dT%H:%M:%SZ)
  printf 'status=%s\nfinished=%s\n' "$status" "$finished" \
    | tee "$result_dir/status.env"
  exit "$status"
}
trap finish EXIT

install_common() {
  export DEBIAN_FRONTEND=noninteractive
  apt-get update
  apt-get install -y --no-install-recommends \
    bash build-essential ca-certificates curl git make pkg-config \
    python3 python3-pip python3-venv time
}

install_racket() {
  local version=$1
  local installer="/tmp/racket-$version.sh"
  curl -fsSL \
    "https://download.racket-lang.org/installers/$version/racket-$version-x86_64-linux-cs.sh" \
    -o "$installer"
  bash "$installer" --unix-style --dest /opt/racket --create-dir
  export PATH="/opt/racket/bin:$PATH"
  racket --version
}

run_fptaylor() {
  install_common
  apt-get install -y --no-install-recommends \
    bison flex gcc g++ m4 opam python3-yaml
  git clone --no-tags https://github.com/soarlab/FPTaylor.git "$work_dir/src"
  git -C "$work_dir/src" checkout --detach \
    b5a77cae348400f21f83512210d9f43c4bffb381
  git -C "$work_dir/src" rev-parse HEAD
  cd "$work_dir/src"
  export OPAMROOT="$work_dir/opam"
  opam init -y --disable-sandboxing
  opam switch create fptaylor-4.14.2 ocaml-base-compiler.4.14.2
  eval "$(opam env --switch=fptaylor-4.14.2)"
  opam install -y num
  num_dir=$(opam var lib)/num

  # The upstream Makefile allows the main OCaml objects to race the INTERVAL
  # sub-build. A serial build follows its intended dependency order.
  make ML="ocamlc -I $num_dir" OPT_ML="ocamlopt -I $num_dir"
  make test
  (
    cd scripts
    python3 run_tests.py ../tests/basic
    python3 run_tests.py ../tests/micro
    python3 run_tests.py ../tests/core
    python3 run_tests.py -r ../tests
  )
}

run_herbie() {
  install_common
  apt-get install -y --no-install-recommends libmpfr6 libmpfr-dev nodejs
  install_racket 8.18
  curl --proto '=https' --tlsv1.2 -fsSL https://sh.rustup.rs \
    | sh -s -- -y --profile minimal --default-toolchain 1.88.0
  export PATH="/root/.cargo/bin:$PATH"
  rustup component add rustfmt
  git clone --no-tags https://github.com/herbie-fp/herbie.git "$work_dir/src"
  git -C "$work_dir/src" checkout --detach \
    52cba77bdd002d6a71feecc2e57631c8d462b4b2
  git -C "$work_dir/src" rev-parse HEAD
  cd "$work_dir/src"
  export PLTUSERHOME="$work_dir/racket-home"
  export RUST_BACKTRACE=full
  make install
  raco pkg install --auto --skip-installed softposit-rkt
  raco test src/ infra/ egg-herbie/
  (
    cd egg-herbie
    cargo test --locked
    cargo fmt -- --check
    raco test ./
  )
  racket -y infra/ci.rkt --precision binary32 --seed 0 bench/hamming/
  racket -y infra/ci.rkt --precision binary64 --seed 0 bench/hamming/
  racket infra/ci.rkt --rival2 --platform infra/softposit.rkt \
    --precision posit16 --seed 0 infra/bench/posits.fpcore
}

case "$suite" in
  fptaylor-rerun1) run_fptaylor ;;
  herbie-rerun1) run_herbie ;;
  *)
    printf 'unknown retry suite: %s\n' "$suite" >&2
    exit 2
    ;;
esac
