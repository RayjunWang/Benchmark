import DensityInverseIntegral
import DensityTargetContinuity
import DensitySourceOpen
import LinearHaarIntegralContinuity

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

def haarFamilyContinuousMap (μ : PositiveCylinderProbabilities) (i : Option HaarNodeIndex) :
    C(HaarCantor, ℝ) :=
  ⟨haarFamilyFunction μ i,
    (continuous_haarFamilyFunction i).comp (continuous_const.prodMk continuous_id)⟩

theorem continuous_haarFamilyContinuousMap (i : Option HaarNodeIndex) :
    Continuous (fun μ : PositiveCylinderProbabilities => haarFamilyContinuousMap μ i) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_haarFamilyFunction i)

theorem densityInverseCoefficients_formula (z : PositiveDensityBundle) (i : Option HaarNodeIndex) :
    densityInverseCoefficients z i =
      linearHaarIntegral (haarFamilyContinuousMap (densityTarget z) i)
        (densitySource z) z.1.2 := by
  rw [densityInverseCoefficients, HilbertBasis.repr_apply_apply,
    cantorRealHaarBasis_apply, L2.inner_def]
  calc
    _ = ∫ x, haarFamilyFunction (densityTarget z) i x * inverseDensityVector z x
        ∂((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
      apply integral_congr_ae
      filter_upwards [haarFamilyFunction_coe (densityTarget z) i] with x hx
      rw [hx, Real.inner_apply, mul_comm]
    _ = ∫ x, haarFamilyFunction (densityTarget z) i x * densityVector z x
        ∂((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor) :=
      integral_inverseDensityVector z _
    _ = _ := (linearHaarIntegral_eq_integral (haarFamilyContinuousMap (densityTarget z) i)
      (densitySource z) z.1.2).symm

theorem continuous_densityInverseCoefficients : Continuous densityInverseCoefficients := by
  apply continuous_haarCoefficients_of_unit_coordinates _
    (fun z => by rw [densityInverseCoefficients, LinearIsometryEquiv.norm_map,
      inverseDensityVector_norm])
  intro i
  have hc := continuous_linearHaarIntegral_joint.comp
    ((continuous_densitySource.prodMk (continuous_snd.comp continuous_subtype_val)).prodMk
      ((continuous_haarFamilyContinuousMap i).comp continuous_densityTarget))
  change Continuous (fun z : PositiveDensityBundle =>
    linearHaarIntegral (haarFamilyContinuousMap (densityTarget z) i)
      (densitySource z) z.1.2) at hc
  simpa only [← densityInverseCoefficients_formula] using hc

theorem continuous_densityInverse : Continuous densityInverse :=
  (continuous_densityTarget.prodMk continuous_densityInverseCoefficients).subtype_mk _

def densityInverseHomeomorph : PositiveDensityBundle ≃ₜ PositiveDensityBundle :=
  { toEquiv := densityInverse_involutive.toPerm densityInverse
    continuous_toFun := continuous_densityInverse
    continuous_invFun := continuous_densityInverse }

/-- The genuine target projection is open, by the proved continuous
inversion homeomorphism and openness of the source projection. -/
theorem isOpenMap_densityTarget : IsOpenMap densityTarget := by
  have heq : densityTarget = densitySource ∘ densityInverse := rfl
  rw [heq]
  exact isOpenMap_densitySource.comp densityInverseHomeomorph.isOpenMap

#print axioms continuous_densityInverse
#print axioms isOpenMap_densityTarget

end BenchmarkJump
