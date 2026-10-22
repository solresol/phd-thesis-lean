#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
export LEAN_NUM_THREADS=2
export MALLOC_ARENA_MAX=2
ulimit -t 1200
available_kib=$(awk '/^MemAvailable:/ {print $2}' /proc/meminfo)
if (( available_kib < 4194304 )); then
  echo 'Need at least 4 GiB available RAM before building.' >&2
  exit 1
fi
free_kib=$(df -Pk . | awk 'NR == 2 {print $4}')
if (( free_kib < 2097152 )); then
  echo 'Need at least 2 GiB free disk before building.' >&2
  exit 1
fi
python3 - <<'PY'
from pathlib import Path
import re
for p in [Path('ThesisComplexityAdapter.lean'), *Path('ThesisComplexityAdapter').glob('*.lean')]:
    if re.search(r'\b(sorry|admit|axiom|unsafe)\b', p.read_text()):
        raise SystemExit(f'Forbidden proof placeholder or declaration in {p}')
PY
timeout 1200 lake build --wfail
log=$(mktemp)
trap 'rm -f "$log"' EXIT
timeout 1200 lake env lean Audit.lean | tee "$log"
python3 - "$log" <<'PY'
from pathlib import Path
import re, sys
text = Path(sys.argv[1]).read_text()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
entries = re.findall(r"'ThesisComplexityAdapter\.[^']+' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text)
if len(entries) != 7:
    raise SystemExit(f'Expected 7 axiom audit entries, got {len(entries)}')
for entry in entries:
    names = {s.strip() for s in entry.split(',') if s.strip()}
    if names - allowed:
        raise SystemExit(f'Unexpected axioms: {names - allowed}')
print('Axiom audit passed: no sorryAx or custom axioms.')
PY
