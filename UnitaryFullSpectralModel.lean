import UnitaryCyclicSpectralModel
import UnitaryGreedyHilbertSum

/-! The actual countable cyclic spectral model of an arbitrary unitary,
using its Borel greedy cyclic vector measures on one fixed circle. -/

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 2000000

namespace OperatorCoding

open MeasureUnitary

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] [SecondCountableTopology H]

def greedySpectralMeasure (U : StrongUnitary H) (n : ℕ) : Measure SpectralCircle :=
  unitaryVectorSpectralMeasure U (greedyCyclicGenerator U n)

instance greedySpectralMeasure_finite (U : StrongUnitary H) (n : ℕ) :
    IsFiniteMeasure (greedySpectralMeasure U n) := by
  unfold greedySpectralMeasure
  infer_instance

abbrev UnitarySpectralSum (U : StrongUnitary H) :=
  lp (fun n : ℕ => Lp ℂ 2 (greedySpectralMeasure U n)) 2

def unitarySpectralSumEquiv (U : StrongUnitary H) : UnitarySpectralSum U ≃ₗᵢ[ℂ] H :=
  (hilbertFamilyCongr (fun n => unitaryCyclicLpEquiv U (greedyCyclicGenerator U n))).trans
    (greedyCyclicCoordinates U).symm

def spectralSumUnitary (U : StrongUnitary H) : StrongUnitary (UnitarySpectralSum U) :=
  hilbertFamilyCongr (fun n => spectralCoordinateUnitary (greedySpectralMeasure U n))

theorem unitarySpectralSumEquiv_single (U : StrongUnitary H) (n : ℕ)
    (f : Lp ℂ 2 (greedySpectralMeasure U n)) :
    unitarySpectralSumEquiv U (lp.single 2 n f) =
      ((unitaryCyclicLpEquiv U (greedyCyclicGenerator U n) f :
        cyclicSpan U (greedyCyclicGenerator U n)) : H) := by
  change (greedyCyclicCoordinates U).symm
    (hilbertFamilyCongr (fun i => unitaryCyclicLpEquiv U (greedyCyclicGenerator U i))
      (lp.single 2 n f)) = _
  rw [hilbertFamilyCongr_single, greedyCyclicCoordinates_symm_single]

theorem spectralSumUnitary_single (U : StrongUnitary H) (n : ℕ)
    (f : Lp ℂ 2 (greedySpectralMeasure U n)) :
    spectralSumUnitary U (lp.single 2 n f) =
      lp.single 2 n (spectralCoordinateUnitary (greedySpectralMeasure U n) f) := by
  exact hilbertFamilyCongr_single
    (fun i : ℕ => spectralCoordinateUnitary (greedySpectralMeasure U i)) n f

theorem unitarySpectralSumEquiv_intertwines (U : StrongUnitary H)
    (f : UnitarySpectralSum U) :
    unitarySpectralSumEquiv U (spectralSumUnitary U f) = U (unitarySpectralSumEquiv U f) := by
  have hmaps :
      (unitarySpectralSumEquiv U).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (spectralSumUnitary U).toContinuousLinearEquiv.toContinuousLinearMap =
      (U : H →L[ℂ] H).comp (unitarySpectralSumEquiv U).toContinuousLinearEquiv.toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    intro n
    apply ContinuousLinearMap.ext
    intro g
    change unitarySpectralSumEquiv U (spectralSumUnitary U (lp.single 2 n g)) =
      U (unitarySpectralSumEquiv U (lp.single 2 n g))
    rw [spectralSumUnitary_single, unitarySpectralSumEquiv_single, unitarySpectralSumEquiv_single]
    exact congrArg (fun z : cyclicSpan U (greedyCyclicGenerator U n) => (z : H))
      (unitaryCyclicLpEquiv_intertwines U (greedyCyclicGenerator U n) g)
  exact congrArg (fun T => T f) hmaps

end
end OperatorCoding

#print axioms OperatorCoding.unitarySpectralSumEquiv_intertwines
