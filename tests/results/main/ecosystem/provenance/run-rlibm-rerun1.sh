#!/usr/bin/env bash

set -euo pipefail

campaign=/efs/robert/floatlean-results/332491fd0acb7702b5730aa96bf5927063583d92/20260910T150728Z/ecosystem
result_dir="$campaign/results/rlibm-all-rerun1"
work_dir=/work/rlibm-all-rerun1
source_dir="$work_dir/src"
output_dir="$result_dir/outputs"
jobs="${JOBS:-10}"

mkdir -p "$result_dir" "$output_dir"
exec > >(tee "$result_dir/run.log") 2>&1

started=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf 'suite=rlibm-all\nattempt=2\nstarted=%s\nnode=%s\njobs=%s\n' \
  "$started" "${NODE_NAME:-unknown}" "$jobs" > "$result_dir/metadata.env"

finish() {
  status=$?
  finished=$(date -u +%Y-%m-%dT%H:%M:%SZ)
  printf 'status=%s\nfinished=%s\n' "$status" "$finished" \
    | tee "$result_dir/status.env"
  exit "$status"
}
trap finish EXIT

export DEBIAN_FRONTEND=noninteractive
apt-get update
apt-get install -y --no-install-recommends \
  build-essential ca-certificates gcc-10 g++-10 git libgmp3-dev \
  libmpfr-dev parallel python3

git clone --no-tags https://github.com/rutgers-apl/rlibm-all.git "$source_dir"
git -C "$source_dir" checkout --detach \
  90431a000071e415abf0f403b6125c385551e346
test "$(git -C "$source_dir" rev-parse HEAD)" = \
  90431a000071e415abf0f403b6125c385551e346

make -C "$source_dir" -j"$jobs" CC=gcc-10
allrep="$source_dir/correct_test/rlibmOFA_float/allrep"
make -C "$allrep" -j"$jobs" CC=gcc-10

mkdir -p "$output_dir/rlibm-all"
export allrep output_dir
parallel --halt now,fail=1 --jobs "$jobs" \
  '"$allrep/{}" "$output_dir/rlibm-all/{}.txt" >"$output_dir/rlibm-all/{}.stdout" 2>&1' \
  ::: Log Log2 Log10 Exp Exp2 Exp10 Sinh Cosh Sinpi Cospi

python3 - "$output_dir/rlibm-all" <<'PY'
import pathlib
import re
import sys

root = pathlib.Path(sys.argv[1])
functions = [
    "Log", "Log2", "Log10", "Exp", "Exp2",
    "Exp10", "Sinh", "Cosh", "Sinpi", "Cospi",
]
ansi = re.compile(r"\x1b\[[0-9;]*m")
expected_details = [
    (str(bits), str(exponent))
    for exponent in range(2, 9)
    for bits in range(exponent + 2, exponent + 25)
]

errors = []
for function in functions:
    path = root / f"{function}.txt"
    if not path.is_file():
        errors.append(f"{function}: missing result")
        continue
    text = ansi.sub("", path.read_text(errors="replace")).replace("\r", "\n")
    details = re.findall(
        r"^Testing FP(\d+)\((\d+) exp bit\): check[ \t]*$", text, re.M
    )
    summaries = re.findall(
        r"^FP reps with ([2-8]) exp bits: check[ \t]*$", text, re.M
    )
    if "incorrect" in text.lower():
        errors.append(f"{function}: numerical mismatch")
    if details != expected_details:
        errors.append(f"{function}: incomplete format coverage")
    if summaries != list("2345678"):
        errors.append(f"{function}: incomplete exponent summaries")

if errors:
    raise SystemExit("\n".join(errors))

print("PASS: 10 functions, 161 formats/function, 5 rounding modes")
PY

float_dir="$source_dir/correct_test/testFloatResults"
tf32_dir="$source_dir/correct_test/testTensorFloat32Results"

make -C "$float_dir/glibc_double" -j"$jobs" CC=gcc-10
make -C "$float_dir/rlibm32" -j"$jobs" CC=gcc-10
make -C "$tf32_dir/rlibm_Ofa" -j"$jobs" CC=gcc-10
make -C "$tf32_dir/glibc_double" -j"$jobs" CC=gcc-10
make -C "$tf32_dir/rlibm32" -j"$jobs" CC=gcc-10

run_group() {
  local format=$1
  local library=$2
  local directory=$3
  shift 3
  local destination="$output_dir/$format/$library"
  mkdir -p "$destination"
  export directory destination
  parallel --halt now,fail=1 --jobs "$jobs" \
    '"$directory/{}" >"$destination/{}.raw" 2>&1' ::: "$@"
}

all_functions=(Log Log2 Log10 Exp Exp2 Exp10 Sinh Cosh Sinpi Cospi)
standard_functions=(Log Log2 Log10 Exp Exp2 Exp10 Sinh Cosh)
run_group float glibc "$float_dir/glibc_double" "${standard_functions[@]}"
run_group float rlibm32 "$float_dir/rlibm32" "${all_functions[@]}"
run_group tf32 rlibm-all "$tf32_dir/rlibm_Ofa" "${all_functions[@]}"
run_group tf32 glibc "$tf32_dir/glibc_double" "${standard_functions[@]}"
run_group tf32 rlibm32 "$tf32_dir/rlibm32" "${all_functions[@]}"

printf '%s\n' \
  $'baseline\tstatus\treason' \
  $'intel\tUNAVAILABLE\tclassic ICC and libimf absent' \
  $'crlibm\tUNAVAILABLE\theader and static archive absent from pinned revision' \
  $'glibc-sinpi-cospi\tUNSUPPORTED\tno upstream harness' \
  $'crlibm-exp2-exp10\tUNSUPPORTED\tno upstream Makefile targets' \
  > "$result_dir/baseline-availability.tsv"

python3 - "$output_dir" "$result_dir/mainstream-summary.tsv" <<'PY'
import pathlib
import re
import sys

root = pathlib.Path(sys.argv[1])
summary_path = pathlib.Path(sys.argv[2])
ansi = re.compile(r"\x1b\[[0-9;]*m")
rows = ["format\tlibrary\tfunction\tmodes"]
errors = []

for path in sorted(root.glob("*/*/*.raw")):
    text = ansi.sub("", path.read_text(errors="replace"))
    final_line = next(
        (line for line in reversed(text.splitlines()) if line.strip()),
        text,
    )
    markers = re.findall(r"(?<![A-Za-z])[ox](?![A-Za-z])", final_line)
    if len(markers) != 5:
        errors.append(f"{path}: expected five mode markers, got {markers!r}")
        continue
    format_name, library = path.parts[-3:-1]
    rows.append(
        f"{format_name}\t{library}\t{path.stem}\t{''.join(markers)}"
    )

summary_path.write_text("\n".join(rows) + "\n")
if errors:
    raise SystemExit("\n".join(errors))

rlibm_tf32 = [
    row.rsplit("\t", 1)[-1]
    for row in rows[1:]
    if row.startswith("tf32\trlibm-all\t")
]
if len(rlibm_tf32) != 10 or any(markers != "ooooo" for markers in rlibm_tf32):
    raise SystemExit("RLIBM-ALL TF32 correctness markers were not all green")
PY
