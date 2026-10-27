#!/usr/bin/env bash
# Verify the published vendor snapshot without a sibling checkout.
# Optional argument: compare additionally with the original source Git checkout.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 - <<'PY'
from pathlib import Path
import hashlib
import sys

expected = {'Vendor/' + m.replace('.', '/') + '.lean'
            for m in Path('Vendor/MODULES.txt').read_text().splitlines() if m}
entries = {}
for line in Path('Vendor/SHA256SUMS').read_text().splitlines():
    digest, name = line.split('  ', 1)
    if name in entries:
        sys.exit(f'duplicate vendor manifest entry: {name}')
    entries[name] = digest
if set(entries) != expected:
    sys.exit('vendor hash manifest does not match Vendor/MODULES.txt')
for name, digest in entries.items():
    path = Path(name)
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
        sys.exit(f'vendor check failed: {name}')
print(f'vendor check: all {len(entries)} modules match the published SHA-256 manifest')
PY

if [ "$#" -gt 0 ]; then
  vendor_source=$1
  vendor_revision=c76c0d4575171bf8131f7487649e565d40530f6e
  git -C "$vendor_source" cat-file -e "$vendor_revision^{commit}"
  while IFS= read -r module; do
    file=${module//.//}.lean
    if ! git -C "$vendor_source" show "$vendor_revision:$file" | cmp -s - "Vendor/$file"; then
      echo "vendor source mismatch: $file" >&2
      exit 1
    fi
  done < Vendor/MODULES.txt
  echo "vendor source comparison: identical to $vendor_revision"
fi
