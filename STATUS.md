# Formalization status

All six Benchmark introduction theorems are completely proved in `MainTheorems.lean`.
The conjunction `BenchmarkComparisons.all_main_comparisons` and both earlier
operator theorem entry points use only the three standard logical axioms.

Every delivered project declaration passed the complete axiom audit. Supporting
lemmas with explicit hypotheses are used as lemmas; the main conclusions have
no additional spectral-gap, category, matrix-field, or classification hypotheses.

Local proof completion and platform verification are separate records. See
`proof-submissions.json` for the latest saved Prove2Me statuses.
