#!/bin/bash
set -euo pipefail
export THEOREM_PROVERS_STATE_DIR="${THEOREM_PROVERS_STATE_DIR:-/workspace/shared/theorem-provers}"
cd "$THEOREM_PROVERS_STATE_DIR"
# Sequential; fail before publication if any project or the complete gate fails.
python3 prepare.py thesis
python3 prepare.py littlewood
python3 prepare.py scholz
source "$THEOREM_PROVERS_STATE_DIR/env.sh"
python3 check.py
