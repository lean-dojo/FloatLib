#!/usr/bin/env bash

# Repository source discovery shared by the structural checks.
#
# Use Git's tracked and untracked file lists with explicit exclusions for generated output,
# then discard paths that no longer exist.

floatlib_lean_files() {
  git ls-files --cached --others --exclude-standard -- \
      "$@" ':(exclude)**/.lake/**' ':(exclude)**/results/**' |
    while IFS= read -r source; do
      if [[ "$source" == *.lean && "$source" != */lakefile.lean && -f "$source" ]]; then
        printf '%s\n' "$source"
      fi
    done |
    LC_ALL=C sort -u
}

floatlib_source_files() {
  # checks/ contains standalone audit commands, rather than importable test modules.
  floatlib_lean_files FloatLib.lean FloatLib tests ':(exclude)tests/checks/**'
}

# Tests and benchmarks have their own package namespaces and source roots.
floatlib_source_module() {
  local source="${1:?a Lean source file is required}"
  source="${source#tests/}"
  source="${source#benchmarks/lean/}"
  source="${source%.lean}"
  printf '%s\n' "${source//\//.}"
}

floatlib_module_source() {
  local module="${1:?a Lean module is required}"
  case "$module" in
    FloatLibTests|FloatLibTests.*) printf 'tests/' ;;
    FloatLibBenchmarks|FloatLibBenchmarks.*) printf 'benchmarks/lean/' ;;
  esac
  printf '%s.lean\n' "${module//.//}"
}

# Parse the Lean modules imported in one source file's header. Imports after the first declaration
# are intentionally ignored: Lean accepts imports only at the module boundary, and stopping there
# avoids mistaking examples or documentation for dependencies.
#
# Header comments may nest or precede `module`, including architecture annotations. Strip them
# before recognizing imports so an annotation cannot hide a dependency.
floatlib_header_imports_impl() {
  local source="${1:?a Lean source file is required}"
  local include_channel="${2:-0}"

  awk -v include_channel="$include_channel" '
    function without_comments(line,    result, pos, pair) {
      result = ""
      for (pos = 1; pos <= length(line); pos++) {
        pair = substr(line, pos, 2)
        if (pair == "/-") {
          comment_depth++
          result = result " "
          pos++
        } else if (comment_depth && pair == "-/") {
          comment_depth--
          pos++
        } else if (!comment_depth) {
          if (pair == "--")
            break
          result = result substr(line, pos, 1)
        }
      }
      return result
    }

    {
      $0 = without_comments($0)
      sub(/^[[:space:]]+/, "")
      sub(/[[:space:]]+$/, "")
    }

    /^$/ || /^module$/ || /^prelude$/ { next }

    /^((public|private)[[:space:]]+)?(meta[[:space:]]+)?import([[:space:]]+all)?[[:space:]]+/ {
      line = $0
      channel = (line ~ /^((public|private)[[:space:]]+)?meta[[:space:]]+import/ ? "meta" : "normal")
      sub(/^((public|private)[[:space:]]+)?(meta[[:space:]]+)?import([[:space:]]+all)?[[:space:]]+/, "", line)
      sub(/[[:space:]].*$/, "", line)
      if (include_channel)
        print channel "\t" line
      else
        print line
      next
    }

    { exit }
  ' "$source"
}

# Print only module names, for dependency and reachability checks.
floatlib_header_imports() {
  floatlib_header_imports_impl "${1:?a Lean source file is required}" 0
}

# Print the elaboration channel and module name. A normal import and a meta import of the same
# module are distinct edges in Lean's environment and may both be required.
floatlib_header_import_edges() {
  floatlib_header_imports_impl "${1:?a Lean source file is required}" 1
}

# Read source paths on stdin and traverse their import graph from the module names in "$@".
# An incoming edge alone is insufficient: a disconnected cycle has no maintained entry point.
floatlib_reachable_modules() {
  local root source module imported
  {
    for root in "$@"; do
      printf 'root\t%s\n' "$root"
    done
    while IFS= read -r source; do
      module="$(floatlib_source_module "$source")"
      while IFS= read -r imported; do
        printf 'edge\t%s\t%s\n' "$module" "$imported"
      done < <(floatlib_header_imports "$source")
    done
  } |
    awk -F '\t' '
      $1 == "root" { pending[++count] = $2 }
      $1 == "edge" { imports[$2, ++degree[$2]] = $3 }
      END {
        while (count > 0) {
          module = pending[count--]
          if (module in reached)
            continue
          reached[module] = 1
          for (edge = 1; edge <= degree[module]; edge++)
            pending[++count] = imports[module, edge]
        }
        for (module in reached)
          print module
      }
    ' |
    LC_ALL=C sort -u
}
