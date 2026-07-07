# Discrete Metric Regression Proofs

Lean 4 formalisation of the theorems from Appendix 2 of the PhD thesis:
"Regularisation of Discrete Metric Machine Learning"

## Main Results

1. **Discrete metric is ultrametric**: `discrete_metric_ultrametric`
   - Proves d(x,z) ≤ max(d(x,y), d(y,z))

2. **Optimal loss theorem**: `optimal_loss_in_finite_set`
   - The optimal loss for regularised linear regression with discrete metric
     is one of {m - K(0), m - K(1) + r, m - K(2) + 2r, ..., m - K(n) + nr}

3. **Finite critical r values**: `finite_critical_r_values`
   - *Intended:* there are only finitely many values of r that yield different
     optimal solutions. **Not yet formalised** — the current Lean statement has a
     trivial (`True`) conclusion and is a placeholder for this result.

## Building

Requires Lean 4 and Mathlib. Install via elan:

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Then build:

```bash
cd proofs
lake update
lake build
```

Note: First build will download Mathlib which requires several GB of disk space.

## Status

- ✅ Definitions complete
- ✅ Ultrametric property (`discrete_metric_ultrametric`) proven
- ✅ Optimal-loss theorem (`optimal_loss_in_finite_set`) proven; no `sorry` placeholders remain
- ⚠️ `finite_critical_r_values` is a placeholder: its conclusion is `True`, so Result 3 is not yet formalised

This directory is supplementary and is not referenced from the thesis text; the
thesis's discrete-metric results stand on their written proofs.
