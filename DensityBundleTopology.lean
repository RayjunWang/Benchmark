import PositiveDensityGdelta
import DensityMeasure
import Mathlib.Topology.GDelta.MetrizableSpace

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped Topology ENNReal NNReal BigOperators

noncomputable section

namespace BenchmarkJump

def haarTruncateFromProduct (s : Finset (Option HaarNodeIndex))
    (x : Option HaarNodeIndex → ℝ) : HaarCoefficientSpace :=
  ∑ i ∈ s, lp.single 2 i (x i)

theorem continuous_haarTruncateFromProduct (s : Finset (Option HaarNodeIndex)) :
    Continuous (haarTruncateFromProduct s) := by
  apply continuous_finsetSum
  intro i _hi
  exact (lp.singleContinuousAddMonoidHom (fun _ : Option HaarNodeIndex => ℝ) 2 i).continuous.comp
    (continuous_apply i)

theorem haarCoefficientSpace_separable : SeparableSpace HaarCoefficientSpace := by
  have hd : Dense (⋃ s : Finset (Option HaarNodeIndex), range (haarTruncateFromProduct s)) := by
    intro a
    apply mem_closure_of_tendsto (tendsto_haarCoefficientTrunc a)
    exact Eventually.of_forall fun s => mem_iUnion.mpr ⟨s, ⟨(a : Option HaarNodeIndex → ℝ), rfl⟩⟩
  apply hd.isSeparable_iff.mp
  exact IsSeparable.iUnion fun s => isSeparable_range (continuous_haarTruncateFromProduct s)

theorem haarCoefficientSpace_polish : PolishSpace HaarCoefficientSpace := by
  letI : SeparableSpace HaarCoefficientSpace := haarCoefficientSpace_separable
  infer_instance

def PositiveDensityParameters : Set (PositiveCylinderProbabilities × HaarCoefficientSpace) :=
  StrictPositiveHaarParameters ∩ {p | ‖p.2‖ = 1}

theorem isGδ_positiveDensityParameters : IsGδ PositiveDensityParameters := by
  letI : PolishSpace PositiveCylinderProbabilities := positiveCylinderProbabilities_polish
  letI : PolishSpace HaarCoefficientSpace := haarCoefficientSpace_polish
  exact isGδ_strictPositiveHaarParameters.inter
    ((isClosed_eq continuous_snd.norm continuous_const).isGδ)

abbrev PositiveDensityBundle := PositiveDensityParameters

/-- The actual norm-one strictly-positive square-density bundle is Polish. -/
theorem positiveDensityBundle_polish : PolishSpace PositiveDensityBundle := by
  letI : PolishSpace PositiveCylinderProbabilities := positiveCylinderProbabilities_polish
  letI : PolishSpace HaarCoefficientSpace := haarCoefficientSpace_polish
  exact polishSpace_of_isGdelta isGδ_positiveDensityParameters

def densitySource (z : PositiveDensityBundle) : PositiveCylinderProbabilities := z.1.1

def densityVector (z : PositiveDensityBundle) :
    Lp ℝ 2 ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor) :=
  haarLift z.1.1 z.1.2

theorem densityVector_positive (z : PositiveDensityBundle) :
    ∀ᵐ x ∂((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor),
      0 < densityVector z x := z.property.1

theorem densityVector_norm (z : PositiveDensityBundle) : ‖densityVector z‖ = 1 := by
  exact (norm_haarLift z.1.1 z.1.2).trans z.property.2

theorem continuous_densitySource : Continuous densitySource :=
  continuous_fst.comp continuous_subtype_val

theorem integral_densityVector_sq (z : PositiveDensityBundle) :
    (∫ x, densityVector z x ^ 2
      ∂((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) = 1 := by
  calc
    _ = inner ℝ (densityVector z) (densityVector z) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by simp [pow_two]
    _ = ‖densityVector z‖ ^ 2 := real_inner_self_eq_norm_sq _
    _ = 1 := by rw [densityVector_norm]; norm_num

def densityTargetMeasure (z : PositiveDensityBundle) : Measure HaarCantor :=
  ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor).withDensity
    (fun x => ENNReal.ofReal (densityVector z x ^ 2))

theorem densityTargetMeasure_univ (z : PositiveDensityBundle) : densityTargetMeasure z univ = 1 := by
  unfold densityTargetMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      (MeasureEquivalenceDensity.integrable_square _ (densityVector z))
      (Eventually.of_forall fun x => sq_nonneg (densityVector z x)),
    integral_densityVector_sq, ENNReal.ofReal_one]

def densityTargetProbability (z : PositiveDensityBundle) : ProbabilityMeasure HaarCantor :=
  ⟨densityTargetMeasure z, ⟨densityTargetMeasure_univ z⟩⟩

instance densityTargetMeasure_isProbability (z : PositiveDensityBundle) :
    IsProbabilityMeasure (densityTargetMeasure z) := ⟨densityTargetMeasure_univ z⟩

theorem densityTarget_ac_source (z : PositiveDensityBundle) :
    densityTargetMeasure z ≪ ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor) :=
  withDensity_absolutelyContinuous _ _

theorem densitySource_ac_target (z : PositiveDensityBundle) :
    ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪ densityTargetMeasure z := by
  apply withDensity_absolutelyContinuous'
  · exact (((Lp.aestronglyMeasurable (densityVector z)).aemeasurable.pow_const 2).ennreal_ofReal)
  · filter_upwards [densityVector_positive z] with x hx
    exact (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hx)).ne'

/-- Squaring the genuine positive unit density yields another full-support
Cantor probability, mutually absolutely continuous with its source. -/
def densityTarget (z : PositiveDensityBundle) : PositiveCylinderProbabilities :=
  ⟨densityTargetProbability z, by
    intro n s
    apply ENNReal.toReal_pos
    · intro hzero
      have hz := densitySource_ac_target z hzero
      have hpos := (densitySource z).property n s
      change 0 < (((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        (prefixCylinder s)).toReal at hpos
      rw [hz, ENNReal.toReal_zero] at hpos
      exact lt_irrefl _ hpos
    · exact measure_ne_top (densityTargetMeasure z) _⟩

theorem densitySource_target_equivalent (z : PositiveDensityBundle) :
    (((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) ∧
    (((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) :=
  ⟨densitySource_ac_target z, densityTarget_ac_source z⟩

#print axioms positiveDensityBundle_polish
#print axioms densitySource_target_equivalent

end BenchmarkJump
