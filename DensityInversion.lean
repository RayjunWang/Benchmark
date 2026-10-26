import DensityBundleTopology
import RNGraph

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

def inverseDensityVector (z : PositiveDensityBundle) :
    Lp ℝ 2 ((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor) :=
  MeasureEquivalenceHellinger.root
    ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
    ((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)

theorem inverseDensityVector_norm (z : PositiveDensityBundle) : ‖inverseDensityVector z‖ = 1 :=
  MeasureEquivalenceHellinger.root_probability_norm _ _ (densitySource_ac_target z)

theorem inverseDensityVector_positive (z : PositiveDensityBundle) :
    ∀ᵐ x ∂((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor),
      0 < inverseDensityVector z x := by
  letI : SigmaFinite (densityTargetMeasure z) := inferInstance
  filter_upwards [MeasureEquivalenceHellinger.root_coe
    ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
    ((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor),
    (densityTarget_ac_source z).ae_le (Measure.rnDeriv_pos (densitySource_ac_target z)),
    Measure.rnDeriv_ne_top
      ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)] with x hx hp ht
  rw [show inverseDensityVector z x = _ from hx]
  exact Real.sqrt_pos.mpr (ENNReal.toReal_pos hp.ne' ht)

def densityInverseCoefficients (z : PositiveDensityBundle) : HaarCoefficientSpace :=
  (cantorRealHaarBasis (densityTarget z)).repr (inverseDensityVector z)

def densityInverse (z : PositiveDensityBundle) : PositiveDensityBundle :=
  ⟨(densityTarget z, densityInverseCoefficients z), by
    constructor
    · change ∀ᵐ x ∂((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor),
        0 < haarLift (densityTarget z) (densityInverseCoefficients z) x
      rw [haarLift, densityInverseCoefficients, LinearIsometryEquiv.symm_apply_apply]
      exact inverseDensityVector_positive z
    · change ‖(cantorRealHaarBasis (densityTarget z)).repr (inverseDensityVector z)‖ = 1
      rw [LinearIsometryEquiv.norm_map, inverseDensityVector_norm]⟩

@[simp] theorem densitySource_inverse (z : PositiveDensityBundle) :
    densitySource (densityInverse z) = densityTarget z := rfl

@[simp] theorem densityVector_inverse (z : PositiveDensityBundle) :
    densityVector (densityInverse z) = inverseDensityVector z :=
  (cantorRealHaarBasis (densityTarget z)).repr.symm_apply_apply _

theorem densityTargetMeasure_inverse (z : PositiveDensityBundle) :
    densityTargetMeasure (densityInverse z) =
      ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  change (MeasureEquivalenceDensity.squareMeasure
    ((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      (densityVector (densityInverse z)) : Measure HaarCantor) = _
  rw [densityVector_inverse]
  exact MeasureEquivalenceRNGraph.squareMeasure_root _ _ (densitySource_ac_target z)

@[simp] theorem densityTarget_inverse (z : PositiveDensityBundle) :
    densityTarget (densityInverse z) = densitySource z := by
  apply Subtype.ext
  apply ProbabilityMeasure.toMeasure_injective
  exact densityTargetMeasure_inverse z

theorem densityBundle_endpoint_ext {z w : PositiveDensityBundle}
    (hs : densitySource z = densitySource w)
    (ht : densityTargetMeasure z = densityTargetMeasure w) : z = w := by
  rcases z with ⟨⟨μ, a⟩, hz⟩
  rcases w with ⟨⟨ν, b⟩, hw⟩
  change μ = ν at hs
  subst ν
  have haAE : ∀ᵐ x ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor),
      0 < haarLift μ a x := hz.1
  have hbAE : ∀ᵐ x ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor),
      0 < haarLift μ b x := hw.1
  have haPos : 0 ≤ haarLift μ a := (Lp.coeFn_nonneg _).mp (haAE.mono fun _ hx => hx.le)
  have hbPos : 0 ≤ haarLift μ b := (Lp.coeFn_nonneg _).mp (hbAE.mono fun _ hx => hx.le)
  have hsq : MeasureEquivalenceDensity.squareMeasure
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) (haarLift μ a) =
      MeasureEquivalenceDensity.squareMeasure
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) (haarLift μ b) := by
    apply Subtype.ext
    exact ht
  have hvec := MeasureEquivalenceDensity.squareMeasure_injective_nonnegative
    ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) haPos hbPos hsq
  have hab : a = b := (cantorRealHaarBasis μ).repr.symm.injective hvec
  subst b
  rfl

theorem densityInverse_involutive : Function.Involutive densityInverse := by
  intro z
  apply densityBundle_endpoint_ext
  · simp
  · rw [densityTargetMeasure_inverse]
    rfl

#print axioms densityTarget_inverse
#print axioms densityInverse_involutive

end BenchmarkJump
