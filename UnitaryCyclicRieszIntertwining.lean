import UnitaryCyclicRieszRange
import MeasureContinuousMultipliers

open MeasureTheory Filter Set
open scoped ENNReal NNReal InnerProductSpace

set_option maxHeartbeats 1000000

noncomputable section

namespace MeasureUnitary

variable {K H : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem continuousMultiplierL2_toLp (μ : Measure K) [IsFiniteMeasure μ]
    (a f : C(K, ℂ)) :
    continuousMultiplierL2 μ a (ContinuousMap.toLp 2 μ ℂ f) =
      ContinuousMap.toLp 2 μ ℂ (a * f) := by
  apply Lp.ext
  filter_upwards [continuousMultiplierL2_coe μ a (ContinuousMap.toLp 2 μ ℂ f),
    f.coeFn_toLp (p := 2) (𝕜 := ℂ) μ,
    (a*f).coeFn_toLp (p := 2) (𝕜 := ℂ) μ] with x hmul hf haf
  rw [hmul, hf, haf]
  rfl

theorem representationVectorLpOperator_intertwines
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) (a : C(K, ℂ))
    (f : Lp ℂ 2 (representationVectorMeasure π v)) :
    representationVectorLpOperator π v
      (continuousMultiplierL2 (representationVectorMeasure π v) a f) =
      π a (representationVectorLpOperator π v f) := by
  have hd := ContinuousMap.toLp_denseRange (p := 2) ℂ (representationVectorMeasure π v) ℂ (by norm_num)
  refine hd.induction ?_ ?_ f
  · rintro z ⟨g,rfl⟩
    rw [continuousMultiplierL2_toLp, representationVectorLpOperator_toLp,
      representationVectorLpOperator_toLp, map_mul]
    rfl
  · exact isClosed_eq
      ((representationVectorLpOperator π v).continuous.comp
        (continuousMultiplierL2 (representationVectorMeasure π v) a).continuous)
      ((π a).continuous.comp (representationVectorLpOperator π v).continuous)

theorem representationVectorLpIsometry_intertwines
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) (a : C(K, ℂ))
    (f : Lp ℂ 2 (representationVectorMeasure π v)) :
    representationVectorLpIsometry π v
      (continuousMultiplierL2 (representationVectorMeasure π v) a f) =
      π a (representationVectorLpIsometry π v f) :=
  representationVectorLpOperator_intertwines π v a f

end MeasureUnitary

#print axioms MeasureUnitary.representationVectorLpIsometry_intertwines
