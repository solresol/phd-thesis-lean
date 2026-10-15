import Lake
open Lake DSL

package «discrete_metric_regression» where
  version := v!"0.1.0"
  -- Lean 4.35 makes `isDefEq` respect transparency; the machine proofs rely on
  -- unfolding aliases such as `FinTM2.Cfg`. Elaboration-only switch, matching
  -- lean-np-hardness; the kernel still checks every proof.
  leanOptions := #[⟨`backward.isDefEq.respectTransparency, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

require lean_np_hardness from git
  "https://github.com/solresol/lean-np-hardness.git" @
    "21e6eb462b14c0b612895b4ff03add15eea54e70"

lean_lib «DiscreteMetricRegression» where
  -- Preserve the inherited prototype as a named library target.

@[default_target]
lean_lib «PhdThesisLean» where
  -- New statement-faithful developments live under the PhdThesisLean namespace.
