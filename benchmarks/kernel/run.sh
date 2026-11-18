#!/usr/bin/env bash
# Kernel time per operation for the binary formats, as a Markdown table.
#
# usage: benchmarks/kernel/run.sh PATHNAME [TRIPLES] [REPS] [FORMAT...]
#
#   PATHNAME  `public`: the public operations (`+`, `-`, `*`, `/`, `ExecFloat.sqrt`,
#             `ExecFloat.fma`), which the kernel reduces through the selected backend.
#             `spec`: the reference operations `ExecFloat.Spec.*`.
#             `kernel`: the kernel operations `KernelPath.Value.*`, which `float_decide` rewrites
#             the public operations to, with the encodings read and stored by
#             `KernelPath.toNat` and `KernelPath.ofNat`.
#   TRIPLES   operand triples per cell (default 8)
#   REPS      repetitions, the fastest is reported (default 3)
#   FORMAT    any of binary16 bfloat16 binary32 binary64 binary128 e4m3 e5m2 (default all),
#             the wide formats binary256 binary512 binary1024 binary4096 (the IEEE interchange
#             parameters of these widths), a custom layout `eEfF` with E exponent bits and F
#             fraction bits (for example `e8f15`, 24 bits, or `e15f64`, 80 bits),
#             or e4m3-binary and e5m2-binary: the two FP8 formats on the general binary carrier
#             `ExecFloat.Binary`, where `e4m3` and `e5m2` are the one-byte types `E4M3` and
#             `E5M2`, whose public operations look their answers up in exhaustive tables
#
# Each cell is (time of the operation over the table - time of a no-operation over the same
# table) / TRIPLES, measured by `Lean.Kernel.whnf` in `Harness.lean`. The square root is taken of
# positive operands in the normal and subnormal classes. KERNEL_BENCH_OPS selects operations
# (default "add sub mul div sqrt fma"). KERNEL_BENCH_MODE selects the rounding direction of the
# `kernel` path (default `nearest`). The `kernel` path rewrites each term as `float_decide`
# rewrites a goal before the kernel reduces it, so a cell is the operation that a proof by
# `float_decide` checks. The `public` and `spec` paths read and store encodings with the
# format's public conversions; KERNEL_BENCH_CONVERSIONS=kernel makes them use `KernelPath.ofNat`
# and `KernelPath.toNat` like the `kernel` path, which isolates the operation. Results go to
# `benchmarks/results/kernel/PATHNAME.{log,md}` unless KERNEL_BENCH_OUT names another directory.
# KERNEL_BENCH_TIMEOUT (seconds, default 600) bounds each format, and a format that does not
# finish is reported as a failure line in the log and as `n/a` in the table.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/../.." && pwd)"
source "$root/tests/lib/lake.sh"

path_name="${1:?public, spec or kernel}"
rewriting=""
triples="${2:-8}"
reps="${3:-3}"
shift $(( $# < 3 ? $# : 3 ))
formats=("$@")
if [[ ${#formats[@]} -eq 0 ]]; then
  formats=(binary16 bfloat16 binary32 binary64 binary128 e4m3 e5m2)
fi
out="${KERNEL_BENCH_OUT:-$root/benchmarks/results/kernel}"
work="$(mktemp -d "${TMPDIR:-/tmp}/kernel-bench.XXXXXX")"
trap 'rm -rf "$work"' EXIT
mkdir -p "$out"
log="$out/$path_name.log"
: > "$log"

# name type expWidth fracWidth bias hasInfinity hasNaN family
layout() {
  case "$1" in
    binary16)  echo "Binary16 5 10 15 true true binary" ;;
    bfloat16)  echo "BFloat16 8 7 127 true true binary" ;;
    binary32)  echo "Binary32 8 23 127 true true binary" ;;
    binary64)  echo "Binary64 11 52 1023 true true binary" ;;
    binary128) echo "Binary128 15 112 16383 true true binary" ;;
    e4m3)    echo "E4M3 4 3 7 false true byte" ;;
    e5m2)      echo "E5M2 5 2 15 true true byte" ;;
    e4m3-binary) echo "FP8Binary 4 3 7 false true binary" ;;
    e5m2-binary)   echo "FP8Binary 5 2 15 true true binary" ;;
    binary256)  echo "Binary256 19 236 262143 true true binary" ;;
    binary512)  echo "WideBinary 23 488 4194303 true true binary" ;;
    binary1024) echo "WideBinary 27 996 67108863 true true binary" ;;
    binary4096) echo "WideBinary 35 4060 17179869183 true true binary" ;;
    *)
      # A custom layout `eEfF`: E exponent bits and F fraction bits, with the IEEE bias.
      if [[ "$1" =~ ^e([0-9]+)f([0-9]+)$ ]]; then
        echo "WideBinary ${BASH_REMATCH[1]} ${BASH_REMATCH[2]} $(( (1 << (BASH_REMATCH[1] - 1)) - 1 )) true true binary"
      else
        echo "unknown format $1" >&2; exit 2
      fi ;;
  esac
}

case "$path_name" in
  public)
    imports=""
    add='fun x y _ => x + y'; sub='fun x y _ => x - y'; mul='fun x y _ => x * y'
    div='fun x y _ => x / y'; sqrt='fun x _ _ => ExecFloat.sqrt x'
    fma='fun x y z => ExecFloat.fma x y z' ;;
  spec)
    imports=""
    add='fun x y _ => ExecFloat.Spec.add x y'; sub='fun x y _ => ExecFloat.Spec.sub x y'
    mul='fun x y _ => ExecFloat.Spec.mul x y'; div='fun x y _ => ExecFloat.Spec.div x y'
    sqrt='fun x _ _ => ExecFloat.Spec.sqrt x'
    fma='fun x y z => ExecFloat.Spec.fma x y z' ;;
  kernel)
    imports="import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Value
import FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath
import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.KernelPath"
    mode="${KERNEL_BENCH_MODE:-nearest}"
    rewriting=" rewriting [run, ofB, toB]"
    add="fun x y _ => KernelPath.Value.add .$mode x y"
    sub="fun x y _ => KernelPath.Value.sub .$mode x y"
    mul="fun x y _ => KernelPath.Value.mul .$mode x y"
    div="fun x y _ => KernelPath.Value.div .$mode x y"
    sqrt="fun x _ _ => KernelPath.Value.sqrt .$mode x"
    fma="fun x y z => KernelPath.Value.fma .$mode x y z" ;;
  *) echo "unknown path $path_name" >&2; exit 2 ;;
esac

cd "$root"
floatlib_lake env lean -o "$work/Harness.olean" "$here/Harness.lean"

for format in "${formats[@]}"; do
  read -r type ew fw bias inf nan family <<<"$(layout "$format")"
  if [[ "$path_name" == kernel || "${KERNEL_BENCH_CONVERSIONS:-}" == kernel ]]; then
    of_bits="KernelPath.ofNat bits"; to_bits="KernelPath.toNat value"
  elif [[ "$family" == binary ]]; then
    of_bits="ExecFloat.Binary.ofNatBits bits"; to_bits="ExecFloat.Binary.toNatBits value"
  else
    of_bits="StaticByte.ofNatBits $type.Family bits"; to_bits="StaticByte.toNatBits value"
  fi
  cell="$work/Cell_$format.lean"
  {
    echo "import FloatLib.Floats.Formats.BinaryInterchange.Configured"
    echo "import FloatLib.Floats.Formats.OCP.FP8.E4M3"
    echo "import FloatLib.Floats.Formats.OCP.FP8.E5M2"
    echo "$imports"
    if [[ "${KERNEL_BENCH_CONVERSIONS:-}" == kernel ]]; then
      echo "import FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath"
      echo "import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.KernelPath"
    fi
    echo "import Harness"
    echo "open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange"
    echo "open FloatLibBenchmarks.KernelReduction"
    echo "set_option maxRecDepth 1000000"
    case "$format" in
      e4m3-binary)
        echo "abbrev FP8Binary := ExecFloat.Binary (exponentBits := 4) (fractionBits := 3) (encoding := .finiteMaxNaN)" ;;
      e5m2-binary)
        echo "abbrev FP8Binary := ExecFloat.Binary (exponentBits := 5) (fractionBits := 2)" ;;
      binary512)
        echo "abbrev WideBinary := ExecFloat.Binary (exponentBits := 23) (fractionBits := 488)" ;;
      binary1024)
        echo "abbrev WideBinary := ExecFloat.Binary (exponentBits := 27) (fractionBits := 996)" ;;
      binary4096)
        echo "abbrev WideBinary := ExecFloat.Binary (exponentBits := 35) (fractionBits := 4060)" ;;
      e*f*)
        if [[ "$format" =~ ^e([0-9]+)f([0-9]+)$ ]]; then
          echo "abbrev WideBinary := ExecFloat.Binary (exponentBits := $ew) (fractionBits := $fw)"
        fi ;;
    esac
    echo "def ofB (bits : Nat) : $type := $of_bits"
    echo "def toB (value : $type) : Nat := $to_bits"
    table() { echo "(operandTable% $ew $fw $bias $inf $nan $1 $2 $triples)"; }
    bench() {
      echo "#kernel_bench \"$format $1 $2\" $reps$rewriting (run ofB toB ($3) $(table "$1" "$4"))"
    }
    want() { [[ " ${KERNEL_BENCH_OPS:-add sub mul div sqrt fma} " == *" $1 "* ]]; }
    for cls in normal subnormal special; do
      if want add || want sub; then bench "$cls" noop-additive 'fun x _ _ => x' additive; fi
      if want add; then bench "$cls" add "$add" additive; fi
      if want sub; then bench "$cls" sub "$sub" additive; fi
      if want sqrt; then
        bench "$cls" noop-root 'fun x _ _ => x' root
        bench "$cls" sqrt "$sqrt" root
      fi
      if want mul || want div; then
        bench "$cls" noop-multiplicative 'fun x _ _ => x' multiplicative
      fi
      if want mul; then bench "$cls" mul "$mul" multiplicative; fi
      if want div; then bench "$cls" div "$div" multiplicative; fi
      if want fma; then
        bench "$cls" noop-fused 'fun x _ _ => x' fused
        bench "$cls" fma "$fma" fused
      fi
    done
  } > "$cell"
  echo "== $format" | tee -a "$log"
  limit="${KERNEL_BENCH_TIMEOUT:-600}"
  set +e
  floatlib_lake env bash -c \
    "LEAN_PATH=\"$work:\$LEAN_PATH\" timeout --kill-after=10 $limit lean \"$cell\"" \
    2>&1 | tee -a "$log"
  status="${PIPESTATUS[0]}"
  set -e
  if [[ "$status" -ne 0 ]]; then
    echo "KBENCH-FAILED $format: exit $status (124 means no result within $limit s)" | tee -a "$log"
  fi
done

awk -v n="$triples" '
  $1 == "KBENCH" {
    f = $2; c = $3; op = $4; t = $5
    if (op ~ /^noop-/) { base[f, c, substr(op, 6)] = t; next }
    kind = (op == "mul" || op == "div") ? "multiplicative" : (op == "fma") ? "fused" : \
      (op == "sqrt") ? "root" : "additive"
    us[f, c, op] = (t - base[f, c, kind]) / n / 1000
    if (!((f, c) in seen)) { seen[f, c] = 1; order[++rows] = f SUBSEP c }
  }
  END {
    print "| format | operands | add | sub | mul | div | sqrt | fma |"
    print "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |"
    for (i = 1; i <= rows; i++) {
      split(order[i], k, SUBSEP)
      printf "| %s | %s |", k[1], k[2]
      m = split("add sub mul div sqrt fma", ops, " ")
      for (j = 1; j <= m; j++) {
        key = k[1] SUBSEP k[2] SUBSEP ops[j]
        if (key in us) printf " %.0f |", us[key]; else printf " n/a |"
      }
      print ""
    }
  }' "$log" > "$out/$path_name.md"
echo "microseconds of kernel time per operation ($triples operand triples, fastest of $reps):"
cat "$out/$path_name.md"
