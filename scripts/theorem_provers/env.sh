unset ELAN_TOOLCHAIN LEAN_SYSROOT LEAN_PATH
export ELAN_HOME="${THEOREM_PROVERS_STATE_DIR:-/workspace/shared/theorem-provers}/runtime/elan"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS=2
export MATHLIB_CACHE_GET_URL=https://cache.mathlib.org/mathlib4
export MATHLIB_CACHE_BASE_URL=https://cache.mathlib.org
