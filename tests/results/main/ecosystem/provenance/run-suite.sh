#!/usr/bin/env bash

set -u

campaign=/efs/robert/floatlean-results/332491fd0acb7702b5730aa96bf5927063583d92/20260910T150728Z/ecosystem
suite=${SUITE:?SUITE must name the suite to run}
result_dir="$campaign/results/$suite"
work_dir="/work/$suite"

mkdir -p "$result_dir" "$work_dir"
exec > >(tee "$result_dir/run.log") 2>&1

started=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf 'suite=%s\nstarted=%s\nnode=%s\n' "$suite" "$started" "${NODE_NAME:-unknown}" \
  > "$result_dir/metadata.env"

install_common() {
  export DEBIAN_FRONTEND=noninteractive
  apt-get update
  apt-get install -y --no-install-recommends \
    bash build-essential ca-certificates cmake curl git make ninja-build \
    pkg-config python3 python3-pip python3-venv time
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

install_jdk25() {
  mkdir -p /opt/java
  curl -fsSL \
    'https://api.adoptium.net/v3/binary/latest/25/ga/linux/x64/jdk/hotspot/normal/eclipse' \
    -o /tmp/jdk25.tar.gz
  tar -xzf /tmp/jdk25.tar.gz -C /opt/java --strip-components=1
  export JAVA_HOME=/opt/java
  export PATH="$JAVA_HOME/bin:$PATH"
  java -version
}

install_sbt_1_9_9() {
  curl -fsSL \
    'https://github.com/sbt/sbt/releases/download/v1.9.9/sbt-1.9.9.tgz' \
    -o /tmp/sbt.tgz
  mkdir -p /opt/sbt
  tar -xzf /tmp/sbt.tgz -C /opt/sbt --strip-components=1
  export PATH="/opt/sbt/bin:$PATH"
  sbt --script-version
}

clone_pinned() {
  local url=$1
  local revision=$2
  git clone --no-tags "$url" "$work_dir/src"
  git -C "$work_dir/src" checkout --detach "$revision"
  git -C "$work_dir/src" rev-parse HEAD
}

run_fpbench() {
  install_common
  apt-get install -y --no-install-recommends \
    gcc g++ gfortran libmpfr6 libmpfr-dev nodejs ocaml-nox z3
  install_racket 9.3
  clone_pinned https://github.com/FPBench/FPBench.git \
    a6621d5f86276859bc01cc7b9c238dee73ff5dbe
  cd "$work_dir/src"
  export PLTUSERHOME="$work_dir/racket-home"
  make setup
  make testsetup
  make raco-test
  make export-test transform-test toolserver-test evaluate-test tensor-test
  tests/scripts/test-filter.sh
  make c-sanity c-test
  make smtlib2-sanity smtlib2-test
  make python-sanity python-test
  find benchmarks -maxdepth 1 -type f -name '*.fpcore' | wc -l \
    > "$result_dir/fpcore-benchmark-count.txt"
}

run_daisy() {
  install_common
  apt-get install -y --no-install-recommends \
    gcc g++ libmpfr6 libmpfr-dev locales z3
  install_jdk25
  install_sbt_1_9_9
  clone_pinned https://github.com/malyzajko/daisy.git \
    6a6f47abdd231d3009444e9e1b8ce9febc28c27e
  cd "$work_dir/src"
  export LC_NUMERIC=C.UTF-8
  export SBT_OPTS='-Xms1G -Xmx16G -Xss8M'
  export JAVA_TOOL_OPTIONS='-Xss8M'
  sbt -v -batch compile Test/compile
  sbt -v -batch test
  sbt -v -batch script
  ./regression/scripts/run_all.sh
}

run_fptaylor() {
  install_common
  apt-get install -y --no-install-recommends \
    bison flex gcc g++ m4 opam python3-yaml
  clone_pinned https://github.com/soarlab/FPTaylor.git \
    b5a77cae348400f21f83512210d9f43c4bffb381
  cd "$work_dir/src"
  export OPAMROOT="$work_dir/opam"
  opam init -y --disable-sandboxing
  opam switch create fptaylor-4.14.2 ocaml-base-compiler.4.14.2
  eval "$(opam env --switch=fptaylor-4.14.2)"
  opam install -y num
  num_dir=$(opam var lib)/num
  make -j"$(nproc)" ML="ocamlc -I $num_dir" OPT_ML="ocamlopt -I $num_dir"
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
  clone_pinned https://github.com/herbie-fp/herbie.git \
    52cba77bdd002d6a71feecc2e57631c8d462b4b2
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

run_core_math() {
  install_common
  apt-get install -y --no-install-recommends \
    clang gcc g++ libgmp-dev libmpfr-dev libomp-dev
  clone_pinned https://gitlab.inria.fr/core-math/core-math.git \
    68b034fbe9512781352d28f2dc9795c1686fe8e9
  cd "$work_dir/src"
  export OMP_NUM_THREADS="${CPU_LIMIT:-180}"
  : > "$result_dir/functions.tsv"
  local failures=0
  local makefile function family
  while IFS= read -r makefile; do
    function=$(awk -F':=' \
      '/^FUNCTION_UNDER_TEST[[:space:]]*:=[[:space:]]*/ {
        gsub(/[[:space:]]/, "", $2); print $2; exit
      }' "$makefile")
    [ -n "$function" ] || continue
    family=${makefile#src/}
    family=${family%%/*}
    if timeout 90m ./check.sh "$function"; then
      printf '%s\t%s\tPASS\n' "$family" "$function" \
        | tee -a "$result_dir/functions.tsv"
    else
      code=$?
      printf '%s\t%s\tFAIL(%s)\n' "$family" "$function" "$code" \
        | tee -a "$result_dir/functions.tsv"
      failures=$((failures + 1))
    fi
  done < <(
    find src/binary16 src/binaryb16 src/binary32 src/binary64 \
      -mindepth 2 -maxdepth 2 -name Makefile -type f | sort
  )
  printf 'failures=%s\n' "$failures" > "$result_dir/summary.env"
  [ "$failures" -eq 0 ]
}

run_rlibm_all() {
  install_common
  apt-get install -y --no-install-recommends \
    gcc g++ libgmp-dev libmpfr-dev python3-matplotlib
  clone_pinned https://github.com/rutgers-apl/rlibm-all.git \
    90431a000071e415abf0f403b6125c385551e346
  cd "$work_dir/src"
  make -j"$(nproc)"
  ./CorrTestRLibmAll.sh
  ./CorrTestMlibs.sh
}

run_openlibm() {
  install_common
  apt-get install -y --no-install-recommends gcc g++ gfortran
  clone_pinned https://github.com/JuliaMath/openlibm.git \
    5fe399749f9276eaa0b8403e507470da05cbbb3f
  cd "$work_dir/src"
  make -j"$(nproc)"
  make test
}

run_flit() {
  install_common
  apt-get install -y --no-install-recommends clang g++ python3-dev sqlite3
  clone_pinned https://github.com/PRUNERS/FLiT.git \
    27b6061b9d2302fa8c3252fe770287bb4d07905b
  cd "$work_dir/src"
  make -j"$(nproc)" check
  make install PREFIX="$work_dir/install"
  export PATH="$work_dir/install/bin:$PATH"
  flit --version
  mkdir -p "$work_dir/litmus"
  cd "$work_dir/litmus"
  flit init --litmus-tests
  make -j"$(nproc)"
  make run
}

run_verificarlo() {
  install_common
  apt-get install -y --no-install-recommends \
    autoconf automake autogen autotools-dev binutils bison bzip2 clang-18 \
    cython3 flex gcc-13 g++-13 libclang-rt-18-dev libedit-dev libmpfr-dev \
    libomp-18-dev libtool libz-dev llvm-18 llvm-18-dev npm parallel
  npm install -g @bazel/bazelisk
  python3 -m venv "$work_dir/venv"
  source "$work_dir/venv/bin/activate"
  python -m pip install --upgrade pip uv
  clone_pinned https://github.com/verificarlo/verificarlo.git \
    c5d1bf798a5ec617c138aa5e6629e1923411d3c8
  cd "$work_dir/src"
  git submodule update --init --recursive
  ./autogen.sh
  CC=gcc-13 CXX=g++-13 ./configure \
    --with-llvm="$(llvm-config-18 --prefix)" --without-flang
  make -j"$(nproc)" install-interflop-stdlib
  make -j"$(nproc)"
  make install
  make installcheck
}

run_reductions() {
  install_common
  apt-get install -y --no-install-recommends \
    gcc g++ gfortran libgmp-dev libmpfr-dev libtbb-dev python3-numpy
  local failures=0

  (
    exblas="$work_dir/exblas"
    git clone --no-tags https://github.com/riakymch/exblas.git "$exblas"
    git -C "$exblas" checkout --detach 856130ebcfe906f519a623d57d1359e744e29042
    cmake -S "$exblas" -B "$exblas/build" \
      -DCMAKE_BUILD_TYPE=Release -DEXBLAS_VS_MPFR=ON
    cmake --build "$exblas/build" --parallel "$(nproc)"
    ctest --test-dir "$exblas/build" --output-on-failure -j"$(nproc)"
  ) > >(tee "$result_dir/exblas.log") 2>&1 || failures=$((failures + 1))

  (
    reproblas="$work_dir/reproblas"
    git clone --no-tags https://github.com/peterahrens/ReproBLAS.git "$reproblas"
    git -C "$reproblas" checkout --detach dfb815058dd34b88caba2513cce63bc2e89f951f
    cd "$reproblas"
    make update
    make -j"$(nproc)"
    make check
    make acc
    make bench
  ) > >(tee "$result_dir/reproblas.log") 2>&1 || failures=$((failures + 1))

  printf 'component_failures=%s\n' "$failures" > "$result_dir/summary.env"
  [ "$failures" -eq 0 ]
}

run_selected_suite() {
  case "$suite" in
    fpbench) run_fpbench ;;
    daisy) run_daisy ;;
    fptaylor) run_fptaylor ;;
    herbie) run_herbie ;;
    core-math) run_core_math ;;
    rlibm-all) run_rlibm_all ;;
    openlibm) run_openlibm ;;
    flit) run_flit ;;
    verificarlo) run_verificarlo ;;
    reductions) run_reductions ;;
    *) printf 'unknown suite: %s\n' "$suite" >&2; return 2 ;;
  esac
}

set +e
(
  set -euo pipefail
  run_selected_suite
)
status=$?
finished=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf 'status=%s\nfinished=%s\n' "$status" "$finished" \
  | tee "$result_dir/status.env"
exit "$status"
