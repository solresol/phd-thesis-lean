import Lake
open Lake DSL

package «discrete_metric_regression» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «DiscreteMetricRegression» where
  -- Preserve the inherited prototype as a named library target.

@[default_target]
lean_lib «PhdThesisLean» where
  -- New statement-faithful developments live under the PhdThesisLean namespace.
