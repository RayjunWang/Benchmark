import UnitaryGreedyCyclicCompleteness
import HilbertFamilyCongr

/-! The actual unitary identification of the original Hilbert space
with the countable Hilbert sum of its Borel greedy cyclic subspaces. -/

open MeasureTheory Set
open scoped InnerProductSpace

set_option maxHeartbeats 1000000

namespace OperatorCoding

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [SecondCountableTopology H]

def greedyCyclicHilbertSum (U : StrongUnitary H) :
    IsHilbertSum ℂ (fun n : ℕ => cyclicSpan U (greedyCyclicGenerator U n))
      (fun n => (cyclicSpan U (greedyCyclicGenerator U n)).subtypeₗᵢ) := by
  apply IsHilbertSum.mkInternal
  · intro i j hij x y
    exact (greedy_cyclicSpans_pairwise_isOrtho U hij).inner_eq x.property y.property
  · change ⊤ ≤ greedyCyclicAllSpan U
    rw [greedyCyclicAllSpan_eq_top]

def greedyCyclicCoordinates (U : StrongUnitary H) :
    H ≃ₗᵢ[ℂ] lp (fun n : ℕ => cyclicSpan U (greedyCyclicGenerator U n)) 2 :=
  (greedyCyclicHilbertSum U).linearIsometryEquiv

theorem greedyCyclicCoordinates_symm_single (U : StrongUnitary H) (n : ℕ)
    (x : cyclicSpan U (greedyCyclicGenerator U n)) :
    (greedyCyclicCoordinates U).symm (lp.single 2 n x) = (x : H) :=
  (greedyCyclicHilbertSum U).linearIsometryEquiv_symm_apply_single x

end
end OperatorCoding

#print axioms OperatorCoding.greedyCyclicCoordinates
