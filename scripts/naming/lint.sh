#!/usr/bin/env bash
# Copyright (c) The Lantana-Lean Contributors
# Released under Apache 2.0 license as described in the file LICENSE.
#
# The naming lint (docs/naming.md): dumps the declarations of Lantana and of every LantanaTest
# module (scripts/naming/Dump.lean, on the built tree) and checks them (scripts/naming/lint.py).
# Usage: scripts/naming/lint.sh   (from the package root, after `lake build` and `lake test`)
# Exit code: 0 if no violation, 1 otherwise.
set -euo pipefail
cd "$(dirname "$0")/../.."
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
lake env lean --run scripts/naming/Dump.lean Lantana | awk -F'\t' '$3 ~ /^Lantana/' > "$tmp/lantana.tsv"
# The test modules one at a time: they are independent programs and may reuse names.
for f in $(find LantanaTest -name '*.lean' | sort); do
  m=${f%.lean}; m=${m//\//.}
  lake env lean --run scripts/naming/Dump.lean "$m" | awk -F'\t' '$3 ~ /^LantanaTest/' >> "$tmp/test.tsv"
done
python3 scripts/naming/lint.py "$tmp/lantana.tsv" "$tmp/test.tsv"
