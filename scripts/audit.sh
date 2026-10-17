#!/usr/bin/env bash
# Copyright (c) The Lantana-Lean Contributors
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Audit the Lean sources: no sorry/admit/axiom/native_decide and no disabled checks.
# Usage: scripts/audit.sh [dir]   (default: the package root)
set -euo pipefail
root=${1:-$(dirname "$0")/..}
status=0
# During the statement skeleton (M1), ALLOW_SORRY=1 reports the sorries instead of failing.
if [ "${ALLOW_SORRY:-0}" = 1 ]; then
  echo "audit: sorries (allowed during the skeleton phase):"
  grep -rncE --include='*.lean' '\bsorry\b' "$root/Lantana" | grep -v ':0$' || true
  pat='\badmit\b|^\s*axiom\b|\bnative_decide\b|set_option\s+debug\.skipKernelTC|set_option\s+maxHeartbeats\s+0\b'
else
  pat='\bsorry\b|\badmit\b|^\s*axiom\b|\bnative_decide\b|set_option\s+debug\.skipKernelTC|set_option\s+maxHeartbeats\s+0\b'
fi
if grep -rnE --include='*.lean' "$pat" "$root/Lantana" "$root/Lantana.lean" 2>/dev/null; then
  echo "audit: forbidden construct found (see above)"; status=1
fi
# The adequacy theorems' axioms are checked by LantanaTest/Axioms.lean (#print axioms with
# #guard_msgs) once they exist.
if [ $status = 0 ]; then echo "audit: ok"; fi
exit $status
