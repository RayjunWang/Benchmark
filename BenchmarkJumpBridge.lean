import CircleJumpObstruction
import Definitions.Def_BenchmarkRelations

/-! Bridge from the verified obstruction to the exact mission definitions.
Only the c0 half of the paired jump statement is claimed here. -/

namespace BenchmarkComparisons

theorem c0_jump_obstruction :
    ¬ BorelReduces NullDifference (Jump BoundedDifference) := by
  rintro ⟨F, hFm, hRed⟩
  apply BenchmarkJump.c0_not_borel_reducible_to_boundedDifferenceJump
  refine ⟨F, hFm, ?_⟩
  intro x y
  apply (hRed x y).trans
  simp only [Jump, BenchmarkJump.Jump, BoundedDifference,
    ← BenchmarkJump.boundedDifference_iff_real_bound]

#print axioms c0_jump_obstruction

end BenchmarkComparisons
