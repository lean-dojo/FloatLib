#!/usr/bin/env bash

# One runner serves both halves of the release campaign. The source archive,
# repository bundle, file manifest, and this script are authenticated before
# we trust them. Results are copied to EFS through a checked temporary tree and
# renamed only after every listed byte has been verified.

set -euo pipefail

require_env() {
  local name="${1:?environment variable name is required}"
  if [[ -z "${!name:-}" ]]; then
    printf 'missing required environment variable: %s\n' "$name" >&2
    exit 2
  fi
}

for required in \
  CAMPAIGN_ROOT CAMPAIGN_ID RUN_MODE RUNNER_SHA256 SOURCE_ARCHIVE_SHA256 \
  REPOSITORY_BUNDLE_SHA256 SOURCE_FILE_HASHES_SHA256 SOURCE_FILE_LIST_SHA256 \
  WORKTREE_STATUS_SHA256 WORKTREE_PATCH_SHA256 POD_NAME NODE_NAME; do
  require_env "$required"
done

case "$RUN_MODE" in
  benchmark|conformance) ;;
  *)
    printf 'unsupported RUN_MODE: %s\n' "$RUN_MODE" >&2
    exit 2
    ;;
esac

source_root="$CAMPAIGN_ROOT/source"
job_root="$CAMPAIGN_ROOT/jobs"
log_root="$CAMPAIGN_ROOT/logs"
staging_root="$CAMPAIGN_ROOT/staging"
entrypoint="$job_root/run-entrypoint.sh"
job_yaml="$job_root/$RUN_MODE-job.yaml"
work_root="/work/floatlean-$RUN_MODE"
checkout="$work_root/FloatLibrary"
local_results="$work_root/results"
live_log="$log_root/$RUN_MODE.log"
status_file="$log_root/$RUN_MODE.status"

mkdir -p "$work_root" "$local_results/provenance" "$log_root" "$staging_root"
exec > >(tee -a "$live_log") 2>&1

verify_sha256() {
  local expected="${1:?expected digest is required}"
  local path="${2:?path is required}"
  local actual
  actual="$(sha256sum "$path" | awk '{print $1}')"
  if [[ "$actual" != "$expected" ]]; then
    printf 'SHA-256 mismatch for %s: expected %s, found %s\n' \
      "$path" "$expected" "$actual" >&2
    return 1
  fi
}

write_manifest() {
  local root="${1:?result root is required}"
  python3 - "$root" <<'PY'
import hashlib
import sys
from pathlib import Path

root = Path(sys.argv[1])
manifest = root / "MANIFEST.tsv"
rows = []
for path in sorted(candidate for candidate in root.rglob("*") if candidate.is_file()):
    if path == manifest:
        continue
    rows.append(
        (
            path.relative_to(root).as_posix(),
            path.stat().st_size,
            hashlib.sha256(path.read_bytes()).hexdigest(),
        )
    )
with manifest.open("w", encoding="utf-8", newline="") as stream:
    stream.write("path\tbytes\tsha256\n")
    for relative, size, digest in rows:
        stream.write(f"{relative}\t{size}\t{digest}\n")
PY
}

verify_manifest() {
  local root="${1:?result root is required}"
  python3 - "$root" <<'PY'
import csv
import hashlib
import sys
from pathlib import Path

root = Path(sys.argv[1])
manifest = root / "MANIFEST.tsv"
if not manifest.is_file():
    raise SystemExit(f"missing manifest: {manifest}")

with manifest.open(newline="", encoding="utf-8") as stream:
    reader = csv.DictReader(stream, delimiter="\t")
    if reader.fieldnames != ["path", "bytes", "sha256"]:
        raise SystemExit(f"unexpected manifest header: {reader.fieldnames!r}")
    listed = {}
    for row in reader:
        relative = row["path"]
        if relative in listed:
            raise SystemExit(f"duplicate manifest path: {relative}")
        listed[relative] = (int(row["bytes"]), row["sha256"])

actual = {
    path.relative_to(root).as_posix()
    for path in root.rglob("*")
    if path.is_file() and path != manifest
}
if actual != set(listed):
    missing = sorted(set(listed) - actual)
    extra = sorted(actual - set(listed))
    raise SystemExit(f"manifest tree mismatch: missing={missing}, extra={extra}")

for relative, (expected_size, expected_digest) in sorted(listed.items()):
    path = root / relative
    size = path.stat().st_size
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    if size != expected_size or digest != expected_digest:
        raise SystemExit(
            f"manifest mismatch for {relative}: "
            f"size {size}/{expected_size}, sha256 {digest}/{expected_digest}"
        )
PY
}

record_machine_state() {
  local label="${1:?state label is required}"
  local output="$local_results/provenance"
  date -u +%Y-%m-%dT%H:%M:%SZ >"$output/$label-time-utc.txt"
  cp /proc/loadavg "$output/$label-loadavg.txt"
  cp /proc/self/status "$output/$label-process-status.txt"
  ps -eo pid,ppid,psr,stat,etime,pcpu,pmem,args \
    >"$output/$label-processes.txt"
  lscpu >"$output/$label-lscpu.txt"
  lscpu -e >"$output/$label-lscpu-extended.txt"
  for path in \
    /sys/fs/cgroup/cpuset.cpus \
    /sys/fs/cgroup/cpuset.cpus.effective \
    /sys/fs/cgroup/cpuset/cpuset.cpus \
    /sys/fs/cgroup/cpuset/cpuset.effective_cpus; do
    if [[ -r "$path" ]]; then
      name="$(printf '%s' "$path" | tr '/' '_')"
      cp "$path" "$output/$label-$name.txt"
    fi
  done
}

atomic_stage() {
  local final="$staging_root/$RUN_MODE"
  local temporary="$staging_root/.$RUN_MODE.$POD_NAME.tmp"
  if [[ -e "$final" || -e "$temporary" ]]; then
    printf 'refusing to overlay an existing staging path: %s or %s\n' \
      "$final" "$temporary" >&2
    return 1
  fi
  mkdir "$temporary"
  # The container runs as root, while EFS root squashing rejects attempts to
  # recreate root ownership. Preserve the benchmark files and their metadata,
  # but let EFS assign ownership to the writer.
  cp -a --no-preserve=ownership "$local_results/." "$temporary/"
  verify_manifest "$temporary"
  mv "$temporary" "$final"
}

check_staging_copy() {
  local source="$work_root/staging-copy-check"
  local destination="$staging_root/.copy-check.$POD_NAME"
  if [[ -e "$source" || -e "$destination" ]]; then
    printf 'staging copy check found an existing path: %s or %s\n' \
      "$source" "$destination" >&2
    return 1
  fi
  mkdir "$source" "$destination"
  printf 'FloatLean staging copy check\n' >"$source/payload.txt"
  cp -a --no-preserve=ownership "$source/." "$destination/"
  cmp "$source/payload.txt" "$destination/payload.txt"
  rm -r "$source" "$destination"
}

finalize_results() {
  local run_code="${1:?run exit code is required}"
  mkdir -p "$local_results/provenance"
  record_machine_state finish
  {
    printf 'campaign_id=%s\n' "$CAMPAIGN_ID"
    printf 'run_mode=%s\n' "$RUN_MODE"
    printf 'run_exit_code=%s\n' "$run_code"
    printf 'finished_utc=%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
    printf 'pod_name=%s\n' "$POD_NAME"
    printf 'node_name=%s\n' "$NODE_NAME"
  } >"$local_results/provenance/cluster-status.txt"
  cp "$source_root/SNAPSHOT.txt" \
    "$local_results/provenance/source-snapshot.txt"
  cp "$source_root/source-files.sha256" \
    "$local_results/provenance/source-files.sha256"
  cp "$source_root/source-files.nul" \
    "$local_results/provenance/source-files.nul"
  cp "$source_root/worktree-status.txt" \
    "$local_results/provenance/worktree-status.txt"
  cp "$source_root/worktree.patch" \
    "$local_results/provenance/worktree.patch"
  cp "$entrypoint" "$local_results/provenance/"
  cp "$job_yaml" "$local_results/provenance/"
  verify_sha256 "$RUNNER_SHA256" \
    "$local_results/provenance/run-entrypoint.sh"
  write_manifest "$local_results"
  verify_manifest "$local_results"
  atomic_stage
}

finish() {
  local run_code=$?
  local packaging_code=0
  local final_code="$run_code"
  local status_tmp="$status_file.$POD_NAME.tmp"
  trap - EXIT
  set +e
  (
    set -euo pipefail
    finalize_results "$run_code"
  )
  packaging_code=$?
  if ((packaging_code != 0 && final_code == 0)); then
    final_code=97
  fi
  {
    printf 'campaign_id=%s\n' "$CAMPAIGN_ID"
    printf 'run_mode=%s\n' "$RUN_MODE"
    printf 'run_exit_code=%s\n' "$run_code"
    printf 'packaging_exit_code=%s\n' "$packaging_code"
    printf 'final_exit_code=%s\n' "$final_code"
    printf 'pod_name=%s\n' "$POD_NAME"
    printf 'node_name=%s\n' "$NODE_NAME"
    printf 'finished_utc=%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  } >"$status_tmp"
  mv "$status_tmp" "$status_file"
  exit "$final_code"
}
trap finish EXIT

printf 'FloatLean %s campaign %s\n' "$RUN_MODE" "$CAMPAIGN_ID"
printf 'Pod: %s\nNode: %s\nStarted: %s\n' \
  "$POD_NAME" "$NODE_NAME" "$(date -u +%Y-%m-%dT%H:%M:%SZ)"

verify_sha256 "$RUNNER_SHA256" "$entrypoint"
verify_sha256 "$SOURCE_ARCHIVE_SHA256" \
  "$source_root/FloatLibrary-source.tar.gz"
verify_sha256 "$REPOSITORY_BUNDLE_SHA256" \
  "$source_root/FloatLibrary-repository.bundle"
verify_sha256 "$SOURCE_FILE_HASHES_SHA256" \
  "$source_root/source-files.sha256"
verify_sha256 "$SOURCE_FILE_LIST_SHA256" \
  "$source_root/source-files.nul"
verify_sha256 "$WORKTREE_STATUS_SHA256" \
  "$source_root/worktree-status.txt"
verify_sha256 "$WORKTREE_PATCH_SHA256" \
  "$source_root/worktree.patch"
check_staging_copy

if [[ "$RUN_MODE" == conformance ]]; then
  dnf install -y \
    ca-certificates cmake curl diffutils file findutils gcc gcc-c++ git \
    gmp-devel gzip jq make mpfr-devel patch pkgconf-pkg-config procps-ng \
    python3.11 python3.11-devel python3.11-pip tar time util-linux which \
    xz zlib-devel
  python3.11 -m venv "$work_root/venv"
  source "$work_root/venv/bin/activate"
  python -m pip install --no-cache-dir \
    matplotlib==3.11.0 \
    numpy==2.4.6 \
    onnx==1.22.0 \
    python-flint==0.9.0 \
    z3-solver==4.16.0.0
else
  export DEBIAN_FRONTEND=noninteractive
  apt-get update
  apt-get install -y --no-install-recommends \
    build-essential ca-certificates curl git gzip jq libgmp-dev libmpfr-dev \
    make pkg-config procps python3 python3-pip python3-venv tar time \
    util-linux xz-utils
  python3 -m venv "$work_root/venv"
  source "$work_root/venv/bin/activate"
  python -m pip install --no-cache-dir matplotlib==3.11.0
fi

elan_archive="$work_root/elan-x86_64-unknown-linux-gnu.tar.gz"
elan_url="https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz"
elan_sha256="42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63"
curl --proto '=https' --tlsv1.2 --fail --location --silent --show-error \
  "$elan_url" -o "$elan_archive"
verify_sha256 "$elan_sha256" "$elan_archive"
mkdir -p "$work_root/elan-installer"
tar -xzf "$elan_archive" -C "$work_root/elan-installer"
export ELAN_HOME="$work_root/elan"
export PATH="$ELAN_HOME/bin:$PATH"
"$work_root/elan-installer/elan-init" -y --default-toolchain none

git clone "$source_root/FloatLibrary-repository.bundle" "$checkout"
git -C "$checkout" bundle verify \
  "$source_root/FloatLibrary-repository.bundle" \
  >"$local_results/provenance/repository-bundle-verify.txt" 2>&1

# The archive contains every file that existed in the captured worktree, but
# an archive cannot say that a tracked file was deleted. Apply the recorded Git
# patch first so deletions and mode changes survive reconstruction, then let
# the archive restore the exact bytes of all remaining tracked and untracked
# files.
if [[ -s "$source_root/worktree.patch" ]]; then
  git -C "$checkout" apply --binary "$source_root/worktree.patch"
fi
tar -xzf "$source_root/FloatLibrary-source.tar.gz" -C "$checkout"
(
  cd "$checkout"
  git ls-files --cached --others --exclude-standard -z |
    while IFS= read -r -d '' path; do
      if [[ -L "$path" ]]; then
        printf 'source capture contains a symbolic link: %s\n' "$path" >&2
        exit 1
      elif [[ -f "$path" ]]; then
        printf '%s\0' "$path"
      elif [[ -e "$path" ]]; then
        printf 'source capture contains a non-regular file: %s\n' "$path" >&2
        exit 1
      fi
    done >"$work_root/reconstructed-files.nul"
  cmp "$source_root/source-files.nul" "$work_root/reconstructed-files.nul"
  sha256sum -c "$source_root/source-files.sha256" \
    >"$local_results/provenance/source-file-verification.txt"
  git status --short --branch >"$work_root/reconstructed-status.txt"
  cmp "$source_root/worktree-status.txt" "$work_root/reconstructed-status.txt"
  git diff --binary HEAD >"$work_root/reconstructed.patch"
  cmp "$source_root/worktree.patch" "$work_root/reconstructed.patch"
)

export TMPDIR="$work_root/tmp"
export LEANFLOAT_BUILD_DIR="$work_root/build"
mkdir -p "$TMPDIR"
cd "$checkout"

record_machine_state start
uname -a >"$local_results/provenance/uname.txt"
cp /etc/os-release "$local_results/provenance/os-release.txt"
python -m pip freeze >"$local_results/provenance/python-packages.txt"
if command -v rpm >/dev/null 2>&1; then
  rpm -qa | sort >"$local_results/provenance/system-packages.txt"
elif command -v dpkg-query >/dev/null 2>&1; then
  dpkg-query -W >"$local_results/provenance/system-packages.txt"
fi
elan --version >"$local_results/provenance/elan-version.txt"

lake exe cache get
lean --version >"$local_results/provenance/lean-version.txt"
lake --version >"$local_results/provenance/lake-version.txt"

if [[ "$RUN_MODE" == conformance ]]; then
  export FLOATLEAN_EXTERNAL_CACHE_ROOT="$work_root/upstream"
  tests/oracles/check.sh \
    --profile release \
    --workers 90 \
    --cpu-set none \
    --results "$local_results/external"
else
  export OPAMROOTISOK=1
  export OPAMROOT=/home/coq/.opam
  export OPAMSWITCH=4.13.1+flambda
  eval "$(opam env --root="$OPAMROOT" --switch="$OPAMSWITCH" --set-root --set-switch)"
  opam install -y coq-flocq.4.2.2 zarith
  flocq_build="$work_root/flocq"
  mkdir -p "$flocq_build"
  cp benchmarks/rocq/FlocqKernel.v "$flocq_build/"
  cp benchmarks/rocq/flocq_format_bench.ml "$flocq_build/"
  cp benchmarks/rocq/monotonic_clock.c "$flocq_build/"
  (
    cd "$flocq_build"
    opam exec -- coqc FlocqKernel.v
    opam exec -- ocamlfind ocamlopt \
      -O3 -linkpkg -package zarith,unix \
      monotonic_clock.c flocq_kernel.mli flocq_kernel.ml \
      flocq_format_bench.ml -cclib -lrt \
      -o flocq_format_bench
  )

  benchmark_cpu="$(
    python3 - <<'PY'
from pathlib import Path

allowed = next(
    line.split(":", 1)[1].strip()
    for line in Path("/proc/self/status").read_text().splitlines()
    if line.startswith("Cpus_allowed_list:")
)
cpus = []
for part in allowed.split(","):
    bounds = [int(value) for value in part.split("-")]
    cpus.extend(range(bounds[0], bounds[-1] + 1))
print(cpus[len(cpus) // 4])
PY
  )"
  printf '%s\n' "$benchmark_cpu" \
    >"$local_results/provenance/pinned-cpu.txt"
  sibling_path="/sys/devices/system/cpu/cpu$benchmark_cpu/topology/thread_siblings_list"
  if [[ -r "$sibling_path" ]]; then
    cp "$sibling_path" \
      "$local_results/provenance/pinned-cpu-thread-siblings.txt"
  fi
  taskset --cpu-list "$benchmark_cpu" true

  export FORMAT_COMPARE_CPU="$benchmark_cpu"
  export FORMAT_COMPARE_DEVELOPMENT_ONLY=0
  export FORMAT_COMPARE_INCLUDE_FLOCQ=1
  export FLOCQ_BENCH_BINARY="$flocq_build/flocq_format_bench"
  export FORMAT_COMPARE_TMPDIR="$TMPDIR"
  # The node exposes 191.45 allocatable CPUs after Kubernetes services. Leave
  # one reserved CPU for the runner while the untimed build uses the rest.
  export FORMAT_COMPARE_BUILD_JOBS=188
  export OMP_NUM_THREADS=1
  export OPENBLAS_NUM_THREADS=1
  export MKL_NUM_THREADS=1
  benchmarks/scripts/format-comparison.sh 9 "$local_results/benchmark"
  opam list --installed >"$local_results/provenance/opam-packages.txt"
fi

git status --short --branch \
  >"$local_results/provenance/post-run-worktree-status.txt"
