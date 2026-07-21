# Thesis theorem statement snapshot

These files copy the core theorem and corollary statements selected from the
live PhD thesis sources. Selection follows the thesis's contributions summary:
the central contact result, complexity results, medoid and coreset theory,
nearby complexity regimes, ultrametric regularisation, and finite-domain
compilers.

Source repository: <https://github.com/solresol/phd-thesis>

Source commit: `2c6418bcf9643fc6e039237f0f59ace14b2557fc`

Snapshot date: 2026-07-21

The statements retain their original LaTeX labels and notation. They are not
standalone documents: definitions, equation labels, and supporting lemmas stay
in the thesis until they are needed for a Lean module. Copying a statement here
does not assert that it has already been formalised or independently checked.

When the thesis changes, update statements intentionally and record the new
source commit. Do not silently rewrite this snapshot to make a Lean proof
easier; record any formal restatement and its correspondence status instead.
