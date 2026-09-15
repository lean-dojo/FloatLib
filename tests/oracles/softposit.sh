#!/usr/bin/env bash
set -euo pipefail

# Build one audited SoftPosit revision from a Git archive in a disposable
# directory. The archive cannot inherit stale object files from the supplied
# checkout, and its exact revision is carried through the binary protocol.

readonly pinned_softposit_revision="17d5628185b31828b10c1f910c9bf65737e83640"

usage() {
  echo "usage: $0 --softposit-dir DIR [--reports N] EMITTER_ARGS..." >&2
  echo "example: $0 --softposit-dir /path/to/SoftPosit --bits 6 --op add --exhaustive" >&2
}

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "${script_dir}/../.." && pwd)"
softposit_dir="${SOFTPOSIT_DIR:-}"
reports=10
emitter_args=()

while (($#)); do
  case "$1" in
    --softposit-dir)
      (($# >= 2)) || { usage; exit 2; }
      softposit_dir="$2"
      shift 2
      ;;
    --reports)
      (($# >= 2)) || { usage; exit 2; }
      reports="$2"
      shift 2
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    *)
      emitter_args+=("$1")
      shift
      ;;
  esac
done

if [[ -z "${softposit_dir}" || ! -f "${softposit_dir}/source/include/softposit.h" ]]; then
  echo "SoftPosit source not found; pass --softposit-dir or set SOFTPOSIT_DIR" >&2
  exit 2
fi
if [[ ! -d "${softposit_dir}/.git" ]]; then
  echo "SoftPosit source must be a Git checkout at its repository root" >&2
  exit 2
fi
if ((${#emitter_args[@]} == 0)); then
  usage
  exit 2
fi
if [[ ! "${reports}" =~ ^[0-9]+$ ]]; then
  echo "invalid report count: ${reports}" >&2
  exit 2
fi
for argument in "${emitter_args[@]}"; do
  if [[ "${argument}" == "--source-revision" ||
      "${argument}" == --source-revision=* ]]; then
    echo "--source-revision is supplied by this driver after Git verification" >&2
    exit 2
  fi
done

softposit_dir="$(cd -- "${softposit_dir}" && pwd -P)"
softposit_root="$(
  git -C "${softposit_dir}" rev-parse --show-toplevel 2>/dev/null
)" || {
  echo "unable to inspect SoftPosit Git checkout: ${softposit_dir}" >&2
  exit 2
}
softposit_root="$(cd -- "${softposit_root}" && pwd -P)"
if [[ "${softposit_root}" != "${softposit_dir}" ]]; then
  echo "pass the SoftPosit repository root, not a subdirectory" >&2
  exit 2
fi

softposit_revision="$(
  git -C "${softposit_dir}" rev-parse --verify HEAD^{commit} 2>/dev/null
)" || {
  echo "unable to resolve the SoftPosit HEAD commit" >&2
  exit 2
}
if [[ "${softposit_revision}" != "${pinned_softposit_revision}" ]]; then
  echo "unexpected SoftPosit revision: ${softposit_revision}" >&2
  echo "required revision: ${pinned_softposit_revision}" >&2
  exit 2
fi

# Include ignored paths so a previously built checkout is rejected as dirty.
# The build below still starts from git archive, which contains tracked bytes
# from the verified commit and no worktree artifacts.
softposit_status="$(
  git -C "${softposit_dir}" status \
    --porcelain=v1 --untracked-files=all --ignored=matching
)"
if [[ -n "${softposit_status}" ]]; then
  echo "SoftPosit checkout is not clean, including ignored build artifacts:" >&2
  printf '%s\n' "${softposit_status}" >&2
  exit 2
fi

work_dir="$(mktemp -d "${TMPDIR:-/tmp}/floatlib-softposit.XXXXXXXX")"
cleanup() {
  rm -rf -- "${work_dir}"
}
trap cleanup EXIT

mkdir -p -- "${work_dir}/SoftPosit"
git -C "${softposit_dir}" archive --format=tar "${softposit_revision}" |
  tar -xf - -C "${work_dir}/SoftPosit"
softposit_build="${work_dir}/SoftPosit/build/Linux-x86_64-GCC"
softposit_objects=(
  s_addMagsPX2.o s_subMagsPX2.o s_mulAddPX2.o
  pX2_add.o pX2_sub.o pX2_mul.o pX2_div.o pX2_mulAdd.o
  pX2_roundToInt.o pX2_sqrt.o pX2_eq.o pX2_le.o pX2_lt.o
  s_addMagsP32.o s_subMagsP32.o s_mulAddP32.o
  p32_add.o p32_sub.o p32_mul.o p32_div.o p32_mulAdd.o
  p32_roundToInt.o p32_sqrt.o p32_eq.o p32_le.o p32_lt.o
)
# This SoftPosit revision's type header contains C++ default member
# initializers, while its legacy Makefile still defaults to gcc. Build only
# the independent operations used by this checker with the C++ driver; this
# also avoids unrelated historical targets that do not compile on modern C++.
make -C "${softposit_build}" --no-print-directory \
  -j"${SOFTPOSIT_BUILD_JOBS:-$(nproc)}" COMPILER="${CXX:-c++}" \
  "${softposit_objects[@]}"
"${CC:-cc}" -O2 -DSOFTPOSIT_FAST_INT64 \
  -I"${softposit_build}" \
  -I"${work_dir}/SoftPosit/source/8086-SSE" \
  -I"${work_dir}/SoftPosit/source/include" \
  -c "${work_dir}/SoftPosit/source/s_approxRecipSqrt_1Ks.c" \
  -o "${softposit_build}/s_approxRecipSqrt_1Ks.o"
softposit_objects+=(s_approxRecipSqrt_1Ks.o)
ar crs "${softposit_build}/softposit-oracle.a" \
  "${softposit_objects[@]/#/${softposit_build}/}"

"${CXX:-c++}" -x c++ -O3 -std=c++20 -Wall -Wextra -Werror \
  -I"${work_dir}/SoftPosit/source/include" \
  -c "${script_dir}/softposit_emitter.c" \
  -o "${work_dir}/softposit-emitter.o"

"${CXX:-c++}" \
  "${work_dir}/softposit-emitter.o" \
  "${softposit_build}/softposit-oracle.a" -lm \
  -o "${work_dir}/softposit-emitter"

source "${repo_root}/tests/lib/lake.sh"
floatlib_test_lake build oracle
oracle_binary="$(floatlib_build_path bin/oracle)"
if [[ ! -x "${oracle_binary}" ]]; then
  echo "built oracle executable not found: ${oracle_binary}" >&2
  exit 1
fi

emitter_log="${work_dir}/emitter.log"
oracle_stdout="${work_dir}/oracle.stdout"
oracle_stderr="${work_dir}/oracle.stderr"

set +e
"${work_dir}/softposit-emitter" "${emitter_args[@]}" \
    --source-revision "${softposit_revision}" 2>"${emitter_log}" |
  "${oracle_binary}" posit "${reports}" >"${oracle_stdout}" 2>"${oracle_stderr}"
pipeline_status=("${PIPESTATUS[@]}")
set -e

cat "${emitter_log}" >&2
cat "${oracle_stderr}" >&2
cat "${oracle_stdout}"

emitter_status="${pipeline_status[0]}"
oracle_status="${pipeline_status[1]}"
metadata_failed=0

emitter_result_count="$(
  awk '/^RESULT emitter=softposit / { count += 1 } END { print count + 0 }' \
    "${emitter_log}"
)"
oracle_result_count="$(
  awk '/^RESULT oracle=softposit / { count += 1 } END { print count + 0 }' \
    "${oracle_stdout}"
)"
if [[ "${emitter_result_count}" != 1 ]]; then
  echo "expected exactly one emitter RESULT line, found ${emitter_result_count}" >&2
  metadata_failed=1
fi
if [[ "${oracle_result_count}" != 1 ]]; then
  echo "expected exactly one oracle RESULT line, found ${oracle_result_count}" >&2
  metadata_failed=1
fi

result_field() {
  local line="${1:?result line is required}"
  local key="${2:?field name is required}"
  local field
  local fields=()
  IFS=' ' read -r -a fields <<<"${line}"
  for field in "${fields[@]}"; do
    if [[ "${field}" == "${key}="* ]]; then
      printf '%s\n' "${field#*=}"
      return 0
    fi
  done
  return 1
}

emitter_result=""
oracle_result=""
if [[ "${emitter_result_count}" == 1 ]]; then
  emitter_result="$(
    awk '/^RESULT emitter=softposit / { print }' "${emitter_log}"
  )"
fi
if [[ "${oracle_result_count}" == 1 ]]; then
  oracle_result="$(
    awk '/^RESULT oracle=softposit / { print }' "${oracle_stdout}"
  )"
fi

compare_metadata_field() {
  local key="${1:?field name is required}"
  local emitted=""
  local received=""
  if ! emitted="$(result_field "${emitter_result}" "${key}")"; then
    echo "emitter RESULT is missing ${key}" >&2
    metadata_failed=1
    return
  fi
  if ! received="$(result_field "${oracle_result}" "${key}")"; then
    echo "oracle RESULT is missing ${key}" >&2
    metadata_failed=1
    return
  fi
  if [[ "${emitted}" != "${received}" ]]; then
    echo "metadata mismatch for ${key}: emitter=${emitted} oracle=${received}" >&2
    metadata_failed=1
  fi
}

requested_cases="unknown"
received_cases="unknown"
if [[ -n "${emitter_result}" && -n "${oracle_result}" ]]; then
  for key in family bits operation mode source_cases expected_cases \
      first_case stride seed revision; do
    compare_metadata_field "${key}"
  done

  emitter_revision="$(result_field "${emitter_result}" revision || true)"
  oracle_revision="$(result_field "${oracle_result}" revision || true)"
  if [[ "${emitter_revision}" != "${softposit_revision}" ||
      "${oracle_revision}" != "${softposit_revision}" ]]; then
    echo "RESULT revision does not match verified Git revision ${softposit_revision}" >&2
    metadata_failed=1
  fi

  requested_cases="$(result_field "${emitter_result}" expected_cases || true)"
  emitted_cases="$(result_field "${emitter_result}" cases || true)"
  received_cases="$(result_field "${oracle_result}" cases || true)"
  oracle_expected="$(result_field "${oracle_result}" expected_cases || true)"
  if [[ -z "${requested_cases}" || -z "${emitted_cases}" ||
      -z "${received_cases}" || -z "${oracle_expected}" ]]; then
    echo "RESULT lines do not contain complete case counts" >&2
    metadata_failed=1
  elif [[ "${emitted_cases}" != "${requested_cases}" ||
      "${received_cases}" != "${requested_cases}" ||
      "${oracle_expected}" != "${requested_cases}" ]]; then
    echo "requested/received case-count mismatch: requested=${requested_cases} " \
      "emitted=${emitted_cases} received=${received_cases} " \
      "oracle_expected=${oracle_expected}" >&2
    metadata_failed=1
  fi

  padding_errors="$(result_field "${emitter_result}" padding_errors || true)"
  protocol_errors="$(result_field "${oracle_result}" protocol_errors || true)"
  if [[ "${padding_errors}" != 0 ]]; then
    echo "emitter reported padding_errors=${padding_errors:-missing}" >&2
    metadata_failed=1
  fi
  if [[ "${protocol_errors}" != 0 ]]; then
    echo "oracle reported protocol_errors=${protocol_errors:-missing}" >&2
    metadata_failed=1
  fi
fi

overall_status=0
metadata_status=pass
if [[ "${emitter_status}" != 0 || "${oracle_status}" != 0 ||
    "${metadata_failed}" != 0 ]]; then
  overall_status=1
fi
if [[ "${metadata_failed}" != 0 ]]; then
  metadata_status=fail
fi

printf 'RESULT driver=softposit revision=%s requested_cases=%s received_cases=%s metadata=%s emitter_status=%s oracle_status=%s\n' \
  "${softposit_revision}" "${requested_cases}" "${received_cases}" \
  "${metadata_status}" "${emitter_status}" "${oracle_status}"
exit "${overall_status}"
