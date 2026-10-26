import HellingerConditional
import SharedConditionalDensity

/-! Affinity is preserved by a measurable map with a measurable left inverse.
The target need not be standard Borel, which allows the invariant sigma algebra. -/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace MeasureEquivalenceHellinger

variable {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]

theorem rnDeriv_map_leftInverse (j : Z → W) (hj : Measurable j)
    (r : W → Z) (hr : Measurable r) (hleft : Function.LeftInverse r j)
    (μ ν : Measure Z) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hac : μ ≪ ν) :
    (fun z => (μ.map j).rnDeriv (ν.map j) (j z)) =ᵐ[ν] μ.rnDeriv ν := by
  let F : W → ℝ≥0∞ := fun w => μ.rnDeriv ν (r w)
  have hF : Measurable F := (Measure.measurable_rnDeriv _ _).comp hr
  have hD : ν.withDensity (fun z => F (j z)) = μ := by
    have heF : (fun z => F (j z)) = μ.rnDeriv ν :=
      funext (fun z => congrArg (μ.rnDeriv ν) (hleft z))
    rw [heF]
    exact Measure.withDensity_rnDeriv_eq μ ν hac
  have hDj : (ν.map j).withDensity F = μ.map j := by
    rw [← MeasureEquivalenceSharedDensity.map_withDensity_comp ν j hj F hF, hD]
  have hRN := (ν.map j).rnDeriv_withDensity hF
  rw [hDj] at hRN
  have hp := ae_of_ae_map hj.aemeasurable hRN
  filter_upwards [hp] with z hz
  exact hz.trans (congrArg (μ.rnDeriv ν) (hleft z))

theorem affinity_map_leftInverse (j : Z → W) (hj : Measurable j)
    (r : W → Z) (hr : Measurable r) (hleft : Function.LeftInverse r j)
    (μ ν : Measure Z) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    affinity (μ.map j) (ν.map j) = affinity μ ν := by
  have hμ : μ ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hν : ν ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right' μ
  rw [affinity_eq_affinityAgainst (μ.map j) (ν.map j) ((μ+ν).map j)
    (hμ.map hj) (hν.map hj)]
  unfold affinityAgainst
  rw [integral_map hj.aemeasurable
    (((Measure.measurable_rnDeriv _ _).ennreal_toReal.sqrt.mul
      (Measure.measurable_rnDeriv _ _).ennreal_toReal.sqrt).aestronglyMeasurable)]
  rw [affinity_integral]
  apply integral_congr_ae
  filter_upwards [rnDeriv_map_leftInverse j hj r hr hleft μ (μ+ν) hμ,
    rnDeriv_map_leftInverse j hj r hr hleft ν (μ+ν) hν] with z hm hn
  rw [hm, hn]

end MeasureEquivalenceHellinger

#print axioms MeasureEquivalenceHellinger.affinity_map_leftInverse
