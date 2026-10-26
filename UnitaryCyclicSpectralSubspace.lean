import UnitaryCyclicFunctionalCalculus
import UnitaryCyclicRieszRange

/-! The Riesz cyclic representation space is exactly the actual closed
Laurent-orbit cyclic subspace of the original unitary. -/

open MeasureTheory Set
open scoped InnerProductSpace

set_option maxHeartbeats 1500000

namespace OperatorCoding

open MeasureUnitary

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]

theorem strongUnitary_clm_pow_apply (U : StrongUnitary H) (n : ℕ) (x : H) :
    ((U : H →L[ℂ] H) ^ n) x = (U ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, pow_succ']
    exact congrArg U ih

theorem representationCyclicSubspace_unitaryCircle_eq (U : StrongUnitary H) (v : H) :
    representationCyclicSubspace (unitaryCircleRepresentation U) v = cyclicSpan U v := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal _ _ (cyclicSpan_isClosed U v)
    rintro x ⟨f,rfl⟩
    exact unitaryCircleRepresentation_cyclicSpan_invariant U v f v (cyclicSpan_contains_generator U v)
  · apply cyclicSpan_minimal U v _
      ((representationVectorLinearMap (unitaryCircleRepresentation U) v).range.isClosed_topologicalClosure)
    intro n
    cases n with
    | ofNat m =>
      have hmem : unitaryCircleRepresentation U (circleCoordinate ^ m) v ∈
          representationCyclicSubspace (unitaryCircleRepresentation U) v :=
        Submodule.le_topologicalClosure _ ⟨circleCoordinate ^ m,rfl⟩
      simpa only [unitaryCircleRepresentation_coordinate_pow, strongUnitary_clm_pow_apply,
        zpow_natCast] using hmem
    | negSucc m =>
      have hmem : unitaryCircleRepresentation U ((star circleCoordinate) ^ (m+1)) v ∈
          representationCyclicSubspace (unitaryCircleRepresentation U) v :=
        Submodule.le_topologicalClosure _ ⟨(star circleCoordinate) ^ (m+1),rfl⟩
      rw [map_pow, unitaryCircleRepresentation_star_coordinate, U.adjoint_eq_symm,
        strongUnitary_clm_pow_apply] at hmem
      change ((U⁻¹) ^ (m+1)) v ∈ representationCyclicSubspace (unitaryCircleRepresentation U) v at hmem
      simpa only [zpow_negSucc, inv_pow] using hmem

end
end OperatorCoding

#print axioms OperatorCoding.representationCyclicSubspace_unitaryCircle_eq
