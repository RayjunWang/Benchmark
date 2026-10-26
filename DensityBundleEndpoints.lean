import ContinuousSquareReweight

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

def positiveDensityPointVector (ρ μ : PositiveCylinderProbabilities) :
    Lp ℝ 2 ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) :=
  MeasureEquivalenceHellinger.root
    ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
    ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)

theorem positiveDensityPointVector_positive (ρ μ : PositiveCylinderProbabilities)
    (hμρ : ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (hρμ : ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) :
    ∀ᵐ x ∂((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor),
      0 < positiveDensityPointVector ρ μ x := by
  letI : SigmaFinite ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := inferInstance
  letI : SigmaFinite ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := inferInstance
  filter_upwards [MeasureEquivalenceHellinger.root_coe
    ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
    ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor),
    hρμ.ae_le (Measure.rnDeriv_pos hμρ),
    Measure.rnDeriv_ne_top
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)] with x hx hp ht
  rw [show positiveDensityPointVector ρ μ x = _ from hx]
  exact Real.sqrt_pos.mpr (ENNReal.toReal_pos hp.ne' ht)

def positiveDensityPoint (ρ μ : PositiveCylinderProbabilities)
    (hμρ : ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (hρμ : ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) : PositiveDensityBundle :=
  ⟨(ρ, (cantorRealHaarBasis ρ).repr (positiveDensityPointVector ρ μ)), by
    constructor
    · change ∀ᵐ x ∂((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor),
        0 < haarLift ρ ((cantorRealHaarBasis ρ).repr (positiveDensityPointVector ρ μ)) x
      rw [haarLift, LinearIsometryEquiv.symm_apply_apply]
      exact positiveDensityPointVector_positive ρ μ hμρ hρμ
    · change ‖(cantorRealHaarBasis ρ).repr (positiveDensityPointVector ρ μ)‖ = 1
      rw [LinearIsometryEquiv.norm_map]
      exact MeasureEquivalenceHellinger.root_probability_norm _ _ hμρ⟩

@[simp] theorem densitySource_positiveDensityPoint (ρ μ : PositiveCylinderProbabilities)
    (hμρ : ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (hρμ : ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) :
    densitySource (positiveDensityPoint ρ μ hμρ hρμ) = ρ := rfl

@[simp] theorem densityVector_positiveDensityPoint (ρ μ : PositiveCylinderProbabilities)
    (hμρ : ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (hρμ : ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) :
    densityVector (positiveDensityPoint ρ μ hμρ hρμ) = positiveDensityPointVector ρ μ :=
  (cantorRealHaarBasis ρ).repr.symm_apply_apply _

@[simp] theorem densityTarget_positiveDensityPoint (ρ μ : PositiveCylinderProbabilities)
    (hμρ : ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (hρμ : ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) :
    densityTarget (positiveDensityPoint ρ μ hμρ hρμ) = μ := by
  apply Subtype.ext
  apply ProbabilityMeasure.toMeasure_injective
  change (MeasureEquivalenceDensity.squareMeasure
    ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      (densityVector (positiveDensityPoint ρ μ hμρ hρμ)) : Measure HaarCantor) = _
  rw [densityVector_positiveDensityPoint]
  exact MeasureEquivalenceRNGraph.squareMeasure_root _ _ hμρ

theorem positiveDensityPoint_section_dist_sq (ρ μ : PositiveCylinderProbabilities)
    (hμρ : ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (hρμ : ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x) :
    dist (densityVector (positiveDensityPoint ρ μ hμρ hρμ)) (normalizedContinuousVector ρ w) ^ 2 =
      MeasureEquivalenceHellinger.energy
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((continuousSquareReweight w hw ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  have hSec : densityVector (positiveContinuousSection w hw ρ) = normalizedContinuousVector ρ w :=
    (cantorRealHaarBasis ρ).repr.symm_apply_apply _
  rw [densityVector_positiveDensityPoint, ← hSec,
    ← root_densityTarget_eq (positiveContinuousSection w hw ρ)]
  exact MeasureEquivalenceHellinger.root_dist_sq _ _ _

#print axioms densityTarget_positiveDensityPoint
#print axioms positiveDensityPoint_section_dist_sq

end BenchmarkJump
