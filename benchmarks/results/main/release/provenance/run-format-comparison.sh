#!/usr/bin/env bash
# Nine-trial format comparison on the 8c88715 build: the release profile's lanes except Flocq
# (posit-software, binary-software, binary-native-c, mpfr-reference, softfloat-reference,
# cpython-float64, universal-posit). Leaving Flocq out needs FORMAT_COMPARE_DEVELOPMENT_ONLY=1;
# every other publication setting is the recorded one (9 trials, calibration toward 200 ms,
# 256-step agreement prefix, one pinned CPU). The 50 ms row minimum and the full binary
# agreement grid, which the script enforces only in publication mode, are checked afterwards
# by check-format-comparison.sh.
set -euo pipefail
E=/workspace/binary-timing
cpu="${1:?timing CPU}"
out="${2:?new output directory}"
export TMPDIR=$E/tmp
export FLOATLIB_BUILD_DIR=$E/libbuild
export PYTHONDONTWRITEBYTECODE=1
export MPLBACKEND=Agg
cd $E/src
uptime | tee "$E/logs/format-comparison-uptime-before.txt"
date -u +%FT%TZ
env \
  FORMAT_COMPARE_DEVELOPMENT_ONLY=1 \
  FORMAT_COMPARE_INCLUDE_FLOCQ=0 \
  FORMAT_COMPARE_INCLUDE_UNIVERSAL=1 \
  FORMAT_COMPARE_INCLUDE_SOFTFLOAT=1 \
  FORMAT_COMPARE_INCLUDE_PYTHON=1 \
  FORMAT_COMPARE_BUILD_JOBS=4 \
  UNIVERSAL_SOURCE=$E/tmp/universal-probe \
  FORMAT_COMPARE_CPU="$cpu" \
  benchmarks/scripts/format-comparison.sh 9 "$out"
date -u +%FT%TZ
uptime | tee "$E/logs/format-comparison-uptime-after.txt"
