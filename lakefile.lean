import Lake
open Lake DSL

package «discrete_metric_regression» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require lean_np_hardness from git
  "https://github.com/solresol/lean-np-hardness.git" @
    "367ff9dac248488d7a7f454d41c36c0b02a7f6c6"

lean_lib «DiscreteMetricRegression» where
  -- Preserve the inherited prototype as a named library target.

@[default_target]
lean_lib «PhdThesisLean» where
  -- New statement-faithful developments live under the PhdThesisLean namespace.
