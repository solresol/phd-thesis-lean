import Lake
open Lake DSL

package «discrete_metric_regression» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «DiscreteMetricRegression» where
  -- add library configuration options here

@[default_target]
lean_exe «discrete_metric_regression» where
  root := `Main
