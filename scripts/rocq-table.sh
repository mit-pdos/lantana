#!/usr/bin/env bash
# Generate the Rocq↔Lean correspondence table (scripts/RocqTable.lean) into
# docs/rocq-correspondence.md.
# Usage: scripts/rocq-table.sh [rocq-checkout] [output]
#   rocq-checkout  the Rocq development of Lantana (with lantana/ and lantana_heap_lang/);
#                  default: $ROCQ_LANTANA, else ../rocq/liveness next to the package if it
#                  exists. With it, the tables are grouped by Rocq file and a coverage report
#                  is added; without it ("" or missing), they are grouped by Lean module.
#   output         default: docs/rocq-correspondence.md; "-" prints to stdout.
# The library must be built (`lake build`); this script builds it if needed.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
rocq=${1-${ROCQ_LANTANA-}}
if [ $# -eq 0 ] && [ -z "${ROCQ_LANTANA+x}" ] && [ -d "$root/../rocq/liveness/lantana" ]; then
  rocq=$root/../rocq/liveness
fi
out=${2:-$root/docs/rocq-correspondence.md}
if [ "$out" != - ]; then out=$(realpath -m "$out"); fi
rev=""
if [ -n "$rocq" ]; then
  if [ ! -d "$rocq/lantana" ] || [ ! -d "$rocq/lantana_heap_lang" ]; then
    echo "rocq-table: $rocq is not a checkout of the Rocq development" >&2; exit 1
  fi
  rocq=$(cd "$rocq" && pwd)
  if git -C "$rocq" rev-parse --git-dir > /dev/null 2>&1; then
    branch=$(git -C "$rocq" rev-parse --abbrev-ref HEAD)
    commit=$(git -C "$rocq" rev-parse --short HEAD)
    rev="branch \`$branch\`, commit \`$commit\`"
    if [ -n "$(git -C "$rocq" status --porcelain -- lantana lantana_heap_lang)" ]; then
      rev="$rev (with uncommitted changes)"
    fi
  fi
fi
cd "$root"
lake build Lantana > /dev/null
tmp=$(mktemp)
trap 'rm -f "$tmp"' EXIT
ROCQ_LANTANA=$rocq ROCQ_LANTANA_REV=$rev lake env lean scripts/RocqTable.lean > "$tmp"
if [ "$out" = - ]; then
  cat "$tmp"
else
  mkdir -p "$(dirname "$out")"
  cp "$tmp" "$out"
  echo "rocq-table: wrote $out"
fi
