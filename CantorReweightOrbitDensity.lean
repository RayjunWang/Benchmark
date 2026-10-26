import CantorPrefixFunctions
import MeasureGenericErgodicity

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology

noncomputable section

namespace BenchmarkJump

set_option maxHeartbeats 1500000

def matchingPrefixWeight (μ ν : PositiveCylinderProbabilities) (n : ℕ) : C(HaarCantor,ℝ) :=
  prefixStep (fun s : Fin n → Bool => Real.sqrt
    (((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s) /
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s)))

theorem matchingPrefixWeight_positive (μ ν : PositiveCylinderProbabilities) (n : ℕ) :
    ∀ x, 0 < matchingPrefixWeight μ ν n x := by
  intro x
  exact Real.sqrt_pos.mpr (div_pos (ν.property n _) (μ.property n _))

theorem matchingPrefixWeight_square (μ ν : PositiveCylinderProbabilities) (n : ℕ) (x : HaarCantor) :
    (matchingPrefixWeight μ ν n x) ^ 2 =
      prefixStep (fun s : Fin n → Bool =>
        ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s) /
          ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s)) x :=
  Real.sq_sqrt (div_nonneg measureReal_nonneg measureReal_nonneg)

theorem matchingPrefixWeight_norm (μ ν : PositiveCylinderProbabilities) (n : ℕ) :
    ‖continuousDensityVector μ (matchingPrefixWeight μ ν n)‖ = 1 := by
  have hn : ‖continuousDensityVector μ (matchingPrefixWeight μ ν n)‖ ^ 2 = 1 := by
    rw [continuousDensityVector_norm_sq]
    simp_rw [matchingPrefixWeight_square]
    rw [integral_prefixStep]
    have hs : ∀ s : Fin n → Bool,
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s) *
        (((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s) /
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s)) =
        ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s) := by
      intro s
      exact mul_div_cancel₀ _ (μ.property n s).ne'
    simp_rw [hs]
    exact prefixCylinder_mass_sum ν n
  nlinarith [norm_nonneg (continuousDensityVector μ (matchingPrefixWeight μ ν n))]

theorem matchingPrefixWeight_cell_mass (μ ν : PositiveCylinderProbabilities) (n : ℕ)
    (s : Fin n → Bool) :
    ((continuousSquareReweight (matchingPrefixWeight μ ν n) (matchingPrefixWeight_positive μ ν n) μ :
      ProbabilityMeasure HaarCantor) : Measure HaarCantor) (prefixCylinder s) =
      ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) (prefixCylinder s) := by
  rw [continuousSquareReweight_measure, matchingPrefixWeight_norm]
  simp only [inv_one,one_mul]
  rw [withDensity_apply _ (isClopen_prefixCylinder s).isClosed.measurableSet]
  let a := ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s)
  let b := ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s)
  have hb : 0 < b := μ.property n s
  have hconst : (fun x => ENNReal.ofReal ((matchingPrefixWeight μ ν n x) ^ 2))
      =ᵐ[(((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).restrict (prefixCylinder s))]
        (fun _ => ENNReal.ofReal (a / b)) := by
    filter_upwards [ae_restrict_mem (isClopen_prefixCylinder s).isClosed.measurableSet] with x hx
    rw [matchingPrefixWeight_square,prefixStep_on_cell _ s x hx]
  rw [lintegral_congr_ae hconst,lintegral_const,Measure.restrict_apply_univ]
  rw [ENNReal.ofReal_div_of_pos hb,ofReal_measureReal,ofReal_measureReal]
  exact ENNReal.div_mul_cancel (by
    intro hzero
    have hz := congrArg ENNReal.toReal hzero
    change b = 0 at hz
    exact hb.ne' hz) (measure_ne_top _ _)

theorem matchingPrefixWeight_cylinder_mass (μ ν : PositiveCylinderProbabilities) (n : ℕ)
    (k : MeasureUnitary.CantorCylinderIndex) (hk : ∀ i ∈ k.1, i < n) :
    ((continuousSquareReweight (matchingPrefixWeight μ ν n) (matchingPrefixWeight_positive μ ν n) μ :
      ProbabilityMeasure HaarCantor) : Measure HaarCantor) (MeasureUnitary.cantorCylinder k) =
      ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) (MeasureUnitary.cantorCylinder k) := by
  classical
  rw [cantorCylinder_mass_prefix_sum _ k n hk,cantorCylinder_mass_prefix_sum _ k n hk]
  apply Finset.sum_congr rfl
  intro s _hs
  split_ifs
  · exact matchingPrefixWeight_cell_mass μ ν n s
  · rfl

theorem matchingPrefixWeight_tendsto (μ ν : PositiveCylinderProbabilities) :
    Tendsto (fun n => continuousSquareReweight (matchingPrefixWeight μ ν n)
      (matchingPrefixWeight_positive μ ν n) μ) atTop (𝓝 ν) := by
  apply tendsto_subtype_rng.mpr
  apply (tendsto_cantorProbability_iff _ _).mpr
  intro k
  apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_gt_atTop (k.1.sup id)] with n hn
  exact (congrArg ENNReal.toReal (matchingPrefixWeight_cylinder_mass μ ν n k
    (fun i hi => (Finset.le_sup (f := id) hi).trans_lt hn))).symm

theorem continuousSquareReweight_orbit_dense (μ : PositiveCylinderProbabilities) :
    Dense (range (fun w : PositiveContinuousWeight => continuousSquareReweight w.1 w.property μ)) := by
  intro ν
  apply mem_closure_of_tendsto (matchingPrefixWeight_tendsto μ ν)
  apply Eventually.of_forall
  intro n
  exact ⟨⟨matchingPrefixWeight μ ν n,matchingPrefixWeight_positive μ ν n⟩,rfl⟩

end BenchmarkJump

#print axioms BenchmarkJump.continuousSquareReweight_orbit_dense
