import BenchmarkJumpBridge
import MeasureJumpObstruction

namespace BenchmarkComparisons

theorem measure_jump_obstruction :
    ¬ BorelReduces MeasureEquivalent (Jump BoundedDifference) := by
  rintro ⟨F, hFm, hRed⟩
  apply BenchmarkJump.measure_not_borel_reducible_to_boundedDifferenceJump
  refine ⟨F, hFm, ?_⟩
  intro μ ν
  apply (hRed μ ν).trans
  simp only [Jump, BenchmarkJump.Jump, BoundedDifference,
    ← BenchmarkJump.boundedDifference_iff_real_bound]

/-- Both exact mission statements of Theorem1.4, on the actual standard
sequence and Cantor probability spaces. -/
theorem jump_obstructions : JumpObstructions :=
  ⟨c0_jump_obstruction, measure_jump_obstruction⟩

#print axioms measure_jump_obstruction
#print axioms jump_obstructions

end BenchmarkComparisons
