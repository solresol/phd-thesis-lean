import Lake
open Lake DSL

package «discrete_metric_regression» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «DiscreteMetricRegression» where
  -- The formalisation is a library. Keeping the library as the default target
  -- avoids natively recompiling all of mathlib for a trivial executable.
