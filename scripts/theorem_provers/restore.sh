#!/bin/bash
set -euo pipefail
# The supported Install hook can run again when a prepared snapshot is restored.
# Deploy reviewed helpers, then verify; preparation is a separate explicit step.
theorem_provers_source_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
python3 "$theorem_provers_source_dir/deploy.py"
theorem_provers_state_dir="${THEOREM_PROVERS_STATE_DIR:-/workspace/shared/theorem-provers}"
source "$theorem_provers_state_dir/env.sh"
python3 "$theorem_provers_state_dir/check.py"
