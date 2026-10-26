import CantorProbabilityMixOpenContinuity

/-! Continuous local right inverses of the probability mixture map, through
the finite-prefix resamplings of its two original endpoints. -/

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology

noncomputable section

namespace BenchmarkJump

def mixLiftWeights (μ β ρ : PositiveCylinderProbabilities) (n : ℕ) (s : Fin n → Bool) : ℝ :=
  ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s) +
    ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s) -
    ((β : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s)

lemma mixLiftWeights_sum (μ β ρ : PositiveCylinderProbabilities) (n : ℕ) :
    ∑ s, mixLiftWeights μ β ρ n s = 1 := by
  simp only [mixLiftWeights, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [prefixCylinder_mass_sum μ n, prefixCylinder_mass_sum ρ n, prefixCylinder_mass_sum β n]
  norm_num

lemma continuous_mixLiftWeights (μ β : PositiveCylinderProbabilities) (n : ℕ) (s : Fin n → Bool) :
    Continuous (fun ρ => mixLiftWeights μ β ρ n s) := by
  exact (continuous_const.add ((continuous_clopen_mass _ (isClopen_prefixCylinder s)).comp
    continuous_subtype_val)).sub continuous_const

def mixLiftDomain (μ ν β : PositiveCylinderProbabilities) (n : ℕ) : Set PositiveCylinderProbabilities :=
  {ρ | ∀ s : Fin n → Bool, 0 < mixLiftWeights μ β ρ n s ∧ 0 < mixLiftWeights ν β ρ n s}

lemma isOpen_mixLiftDomain (μ ν β : PositiveCylinderProbabilities) (n : ℕ) :
    IsOpen (mixLiftDomain μ ν β n) := by
  unfold mixLiftDomain
  simp only [setOf_forall, setOf_and]
  apply isOpen_iInter_of_finite
  intro s
  exact (isOpen_lt continuous_const (continuous_mixLiftWeights μ β n s)).inter
    (isOpen_lt continuous_const (continuous_mixLiftWeights ν β n s))

lemma mixLiftDomain_base (μ ν β : PositiveCylinderProbabilities) (n : ℕ) :
    β ∈ mixLiftDomain μ ν β n := by
  intro s
  simpa only [mixLiftWeights, add_sub_cancel_right] using ⟨μ.property n s, ν.property n s⟩

def mixLiftLeft (μ ν β : PositiveCylinderProbabilities) (n : ℕ)
    (ρ : mixLiftDomain μ ν β n) : PositiveCylinderProbabilities :=
  realPrefixReweight ρ n (mixLiftWeights μ β ρ n)
    (mixLiftWeights_sum μ β ρ n) (fun s => (ρ.property s).1)

def mixLiftRight (μ ν β : PositiveCylinderProbabilities) (n : ℕ)
    (ρ : mixLiftDomain μ ν β n) : PositiveCylinderProbabilities :=
  realPrefixReweight ρ n (mixLiftWeights ν β ρ n)
    (mixLiftWeights_sum ν β ρ n) (fun s => (ρ.property s).2)

lemma continuous_mixLiftLeft (μ ν β : PositiveCylinderProbabilities) (n : ℕ) :
    Continuous (mixLiftLeft μ ν β n) :=
  continuous_realPrefixReweight _ continuous_subtype_val n _
    (fun s => (continuous_mixLiftWeights μ β n s).comp continuous_subtype_val)
    _ _

lemma continuous_mixLiftRight (μ ν β : PositiveCylinderProbabilities) (n : ℕ) :
    Continuous (mixLiftRight μ ν β n) :=
  continuous_realPrefixReweight _ continuous_subtype_val n _
    (fun s => (continuous_mixLiftWeights ν β n s).comp continuous_subtype_val)
    _ _

lemma mixLiftLeft_base (μ ν β : PositiveCylinderProbabilities) (n : ℕ) :
    mixLiftLeft μ ν β n ⟨β, mixLiftDomain_base μ ν β n⟩ = prefixResample β μ n := by
  apply Subtype.ext
  apply Subtype.ext
  change prefixReweightMeasure β n (fun s => ENNReal.ofReal (mixLiftWeights μ β β n s)) =
    prefixReweightMeasure β n (fun s => ENNReal.ofReal
      (((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s)))
  congr 1
  funext s
  simp only [mixLiftWeights, add_sub_cancel_right]

lemma mixLiftRight_base (μ ν β : PositiveCylinderProbabilities) (n : ℕ) :
    mixLiftRight μ ν β n ⟨β, mixLiftDomain_base μ ν β n⟩ = prefixResample β ν n := by
  apply Subtype.ext
  apply Subtype.ext
  change prefixReweightMeasure β n (fun s => ENNReal.ofReal (mixLiftWeights ν β β n s)) =
    prefixReweightMeasure β n (fun s => ENNReal.ofReal
      (((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s)))
  congr 1
  funext s
  simp only [mixLiftWeights, add_sub_cancel_right]

theorem mixLift_exact (t : unitInterval) (μ ν : PositiveCylinderProbabilities) (n : ℕ)
    (ρ : mixLiftDomain μ ν (positiveProbabilityMix t μ ν) n) :
    positiveProbabilityMix t (mixLiftLeft μ ν (positiveProbabilityMix t μ ν) n ρ)
      (mixLiftRight μ ν (positiveProbabilityMix t μ ν) n ρ) = (ρ : PositiveCylinderProbabilities) := by
  apply Subtype.ext
  apply Subtype.ext
  apply prefixReweightMeasure_mix
  intro s
  have hreal : (1 - (t : ℝ)) * mixLiftWeights μ (positiveProbabilityMix t μ ν) ρ n s +
      (t : ℝ) * mixLiftWeights ν (positiveProbabilityMix t μ ν) ρ n s =
        ((ρ : PositiveCylinderProbabilities) : ProbabilityMeasure HaarCantor).toMeasure.real (prefixCylinder s) := by
    unfold mixLiftWeights
    change (1 - (t : ℝ)) * (_ + _ - (cantorProbabilityMix t μ ν : Measure HaarCantor).real _) +
      (t : ℝ) * (_ + _ - (cantorProbabilityMix t μ ν : Measure HaarCantor).real _) = _
    rw [cantorProbabilityMix_real]
    ring
  change ENNReal.ofReal (1 - (t : ℝ)) * ENNReal.ofReal (mixLiftWeights μ (positiveProbabilityMix t μ ν) ρ n s) +
      ENNReal.ofReal (t : ℝ) * ENNReal.ofReal (mixLiftWeights ν (positiveProbabilityMix t μ ν) ρ n s) = _
  rw [← ENNReal.ofReal_mul (sub_nonneg.mpr t.property.2),
    ← ENNReal.ofReal_mul t.property.1,
    ← ENNReal.ofReal_add (mul_nonneg (sub_nonneg.mpr t.property.2) ((ρ.property s).1.le))
      (mul_nonneg t.property.1 ((ρ.property s).2.le)), hreal]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

end BenchmarkJump

#print axioms BenchmarkJump.mixLift_exact
