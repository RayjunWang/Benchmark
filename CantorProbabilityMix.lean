import CantorProbabilityCoordinates

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology

noncomputable section

namespace BenchmarkJump

def cantorProbabilityMix (t : unitInterval) (μ ν : ProbabilityMeasure HaarCantor) : ProbabilityMeasure HaarCantor :=
  ⟨ENNReal.ofReal (1 - (t : ℝ)) • (μ : Measure HaarCantor) +
    ENNReal.ofReal (t : ℝ) • (ν : Measure HaarCantor), ⟨by
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
      rw [← ENNReal.ofReal_add (sub_nonneg.mpr t.property.2) t.property.1]
      norm_num⟩⟩

theorem cantorProbabilityMix_apply (t : unitInterval) (μ ν : ProbabilityMeasure HaarCantor) (A : Set HaarCantor) :
    (cantorProbabilityMix t μ ν : Measure HaarCantor) A =
      ENNReal.ofReal (1 - (t : ℝ)) * (μ : Measure HaarCantor) A +
        ENNReal.ofReal (t : ℝ) * (ν : Measure HaarCantor) A := rfl

theorem cantorProbabilityMix_real (t : unitInterval) (μ ν : ProbabilityMeasure HaarCantor) (A : Set HaarCantor) :
    (cantorProbabilityMix t μ ν : Measure HaarCantor).real A =
      (1 - (t : ℝ)) * (μ : Measure HaarCantor).real A +
        (t : ℝ) * (ν : Measure HaarCantor).real A := by
  change (ENNReal.ofReal (1 - (t : ℝ)) • (μ : Measure HaarCantor) +
    ENNReal.ofReal (t : ℝ) • (ν : Measure HaarCantor)).real A = _
  rw [measureReal_add_apply
    (by rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (by rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  simp only [measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal (sub_nonneg.mpr t.property.2),
    ENNReal.toReal_ofReal t.property.1]

theorem cantorProbabilityMix_self (t : unitInterval) (μ : ProbabilityMeasure HaarCantor) :
    cantorProbabilityMix t μ μ = μ := by
  apply injective_cantorProbabilityCoordinates
  funext k
  change (cantorProbabilityMix t μ μ : Measure HaarCantor).real _ = (μ : Measure HaarCantor).real _
  rw [cantorProbabilityMix_real]
  ring

theorem continuous_cantorProbabilityMix :
    Continuous (fun p : unitInterval × (ProbabilityMeasure HaarCantor × ProbabilityMeasure HaarCantor) =>
      cantorProbabilityMix p.1 p.2.1 p.2.2) := by
  apply (continuous_cantorProbability_iff _).mpr
  intro k
  simp_rw [cantorProbabilityMix_real]
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    ((continuous_clopen_mass _ (isClopen_cantorCylinder k)).comp (continuous_fst.comp continuous_snd))).add
    ((continuous_subtype_val.comp continuous_fst).mul
      ((continuous_clopen_mass _ (isClopen_cantorCylinder k)).comp (continuous_snd.comp continuous_snd)))

theorem cantorProbabilityMix_fullSupport_right (t : unitInterval) (ht : 0 < (t : ℝ))
    (μ : ProbabilityMeasure HaarCantor) (ν : PositiveCylinderProbabilities) :
    cantorProbabilityMix t μ ν ∈ PositiveCylinderProbabilities := by
  intro n s
  rw [cantorProbabilityMix_real]
  have hnonneg : 0 ≤ (1 - (t : ℝ)) * (μ : Measure HaarCantor).real (prefixCylinder s) :=
    mul_nonneg (sub_nonneg.mpr t.property.2) measureReal_nonneg
  exact add_pos_of_nonneg_of_pos hnonneg (mul_pos ht (ν.property n s))

def fullSupportMix (t : unitInterval) (ht : 0 < (t : ℝ))
    (μ : ProbabilityMeasure HaarCantor) (ν : PositiveCylinderProbabilities) : PositiveCylinderProbabilities :=
  ⟨cantorProbabilityMix t μ ν, cantorProbabilityMix_fullSupport_right t ht μ ν⟩

theorem continuous_fullSupportMix (t : unitInterval) (ht : 0 < (t : ℝ)) :
    Continuous (fun p : ProbabilityMeasure HaarCantor × PositiveCylinderProbabilities =>
      fullSupportMix t ht p.1 p.2) := by
  apply Continuous.subtype_mk
  exact continuous_cantorProbabilityMix.comp
    (continuous_const.prodMk (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))

end BenchmarkJump

#print axioms BenchmarkJump.continuous_cantorProbabilityMix
