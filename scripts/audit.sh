#!/usr/bin/env bash
# Audit the Lean sources: no sorry/admit/axiom/native_decide and no disabled checks.
# Usage: scripts/audit.sh [dir]   (default: the package root)
set -euo pipefail
root=${1:-$(dirname "$0")/..}
status=0
pat='\bsorry\b|\badmit\b|^\s*axiom\b|\bnative_decide\b|set_option\s+debug\.skipKernelTC|set_option\s+maxHeartbeats\s+0\b'
if grep -rnE --include='*.lean' "$pat" "$root/Lantana" "$root/Lantana.lean" 2>/dev/null; then
  echo "audit: forbidden construct found (see above)"; status=1
fi
# The adequacy theorems' axioms are checked by LantanaTest/Axioms.lean (#print axioms with
# #guard_msgs) once they exist.
if [ $status = 0 ]; then echo "audit: ok"; fi
exit $status
