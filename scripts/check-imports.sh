#!/usr/bin/env bash
# Check the layering of the library: a module of Lantana/ imports only modules of its own layer
# or of earlier ones, in the order
#   Std, Init < Prelude < Algebra < BaseLogic < ProgramLogic < Trace < HeapLang < Examples
# (the layer of Lantana.L.… and of the aggregator Lantana.L is L; the root module Lantana
# imports everything and is not checked).
# Usage: scripts/check-imports.sh [dir]   (default: the package root)
set -euo pipefail
root=${1:-$(dirname "$0")/..}
layers=(Std Init Prelude Algebra BaseLogic ProgramLogic Trace HeapLang Examples)
# Allowed exceptions, as "Importer Imported" pairs (module names); none at present.
allowed=()

# The layer index of a module name Lantana.L or Lantana.L.…; empty if it is not in a layer.
layer_of() {
  local comp=${1#Lantana.}
  comp=${comp%%.*}
  local i
  for i in "${!layers[@]}"; do
    if [ "${layers[$i]}" = "$comp" ]; then
      # Std and Init form one layer
      if [ "$i" -le 1 ]; then echo 0; else echo $((i - 1)); fi
      return
    fi
  done
}

status=0
count=0
while IFS= read -r file; do
  rel=${file#"$root"/}
  mod=${rel%.lean}
  mod=${mod//\//.}
  [ "$mod" = Lantana ] && continue
  own=$(layer_of "$mod")
  if [ -z "$own" ]; then
    echo "check-imports: $rel: module $mod is in no layer"; status=1; continue
  fi
  # the imports of Lantana modules (`public`/`private`, `meta`, `all` modifiers allowed)
  while IFS= read -r imp; do
    count=$((count + 1))
    dep=$(layer_of "$imp")
    if [ -z "$dep" ]; then
      echo "check-imports: $rel: imports $imp, which is in no layer"; status=1; continue
    fi
    if [ "$dep" -gt "$own" ]; then
      ok=0
      for pair in ${allowed[@]+"${allowed[@]}"}; do
        [ "$pair" = "$mod $imp" ] && ok=1
      done
      if [ $ok = 0 ]; then
        echo "check-imports: $rel: $mod imports $imp, from a later layer"; status=1
      fi
    fi
  done < <(sed -nE 's/^[[:space:]]*((public|private)[[:space:]]+)?(meta[[:space:]]+)?import[[:space:]]+(all[[:space:]]+)?(Lantana(\.[A-Za-z0-9_]+)*)[[:space:]]*$/\5/p' "$file")
done < <(find "$root/Lantana" -name '*.lean' | sort)

if [ $status = 0 ]; then echo "check-imports: ok ($count imports of Lantana modules checked)"; fi
exit $status
