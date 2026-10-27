#!/usr/bin/env bash
# Full build and proof-dependency audit. Usage: scripts/audit.sh
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
echo "== forbidden tokens in SparseIrred/ (sorry/admit/axiom/native_decide/implemented_by/extern/unsafe)"
scan_status=0
rg -n '\bsorry\b|\badmit\b|^[[:space:]]*axiom |native_decide|implemented_by|@\[extern|\bunsafe\b' \
  SparseIrred SparseIrred.lean || scan_status=$?
if [ "$scan_status" -eq 0 ]; then
  echo "Forbidden token found; audit failed." >&2
  exit 1
elif [ "$scan_status" -ne 1 ]; then
  echo "Source scan failed." >&2
  exit "$scan_status"
fi
echo "(none)"
echo "== lake build"
lake build
echo "== #print axioms"
lake env lean scripts/Axioms.lean 2>&1 | tee docs/AXIOMS.txt
echo "== transitive dependency audit"
lake env lean scripts/DepAudit.lean 2>&1 | sed "s/^scripts\/DepAudit.lean:[0-9]*:[0-9]*: info: //" | tee docs/DEP_AUDIT.txt
echo "== vendor provenance"
scripts/check_vendor.sh
echo "== audit passed"
