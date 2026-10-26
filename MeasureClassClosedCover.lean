import CantorProbabilityCoordinates
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology

noncomputable section

namespace BenchmarkJump

def clopenACBound (μ : ProbabilityMeasure HaarCantor) (k : ℕ) :
    Set PositiveCylinderProbabilities :=
  {ν | ∀ A : Set HaarCantor, IsClopen A → (2⁻¹ : ℝ≥0∞) ≤ (μ : Measure HaarCantor) A →
    ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A}

theorem continuous_clopen_mass_ennreal (A : Set HaarCantor) (hA : IsClopen A) :
    Continuous (fun μ : ProbabilityMeasure HaarCantor => (μ : Measure HaarCantor) A) := by
  have he : (fun μ : ProbabilityMeasure HaarCantor => (μ : Measure HaarCantor) A) =
      (fun μ : ProbabilityMeasure HaarCantor => ENNReal.ofReal ((μ : Measure HaarCantor).real A)) := by
    funext μ
    exact (ENNReal.ofReal_toReal (measure_ne_top (μ : Measure HaarCantor) A)).symm
  rw [he]
  exact ENNReal.continuous_ofReal.comp (continuous_clopen_mass A hA)

theorem isClosed_clopenACBound (μ : ProbabilityMeasure HaarCantor) (k : ℕ) :
    IsClosed (clopenACBound μ k) := by
  simp only [clopenACBound, setOf_forall]
  apply isClosed_iInter
  intro A
  apply isClosed_iInter
  intro hA
  apply isClosed_iInter
  intro _hμA
  exact isClosed_le continuous_const ((continuous_clopen_mass_ennreal A hA).comp continuous_subtype_val)

theorem ac_mem_clopenACBound (μ : ProbabilityMeasure HaarCantor) (ν : PositiveCylinderProbabilities)
    (hac : (μ : Measure HaarCantor) ≪ ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) :
    ∃ k : ℕ, ν ∈ clopenACBound μ k := by
  let ρ : Measure HaarCantor := ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
  letI : IsProbabilityMeasure (μ : Measure HaarCantor) := μ.property
  letI : IsProbabilityMeasure ρ := (ν : ProbabilityMeasure HaarCantor).property
  letI : SFinite (μ : Measure HaarCantor) := inferInstance
  letI : SigmaFinite ρ := inferInstance
  letI : Measure.HaveLebesgueDecomposition (μ : Measure HaarCantor) ρ :=
    Measure.haveLebesgueDecomposition_of_sigmaFinite (μ : Measure HaarCantor) ρ
  change (μ : Measure HaarCantor) ≪ ρ at hac
  have hi : ∫⁻ x, (μ : Measure HaarCantor).rnDeriv ρ x ∂ρ ≠ ∞ := by
    rw [Measure.lintegral_rnDeriv hac]
    exact measure_ne_top _ _
  obtain ⟨δ,hδ,hbound⟩ := exists_pos_setLIntegral_lt_of_measure_lt hi
    (ε := (2⁻¹ : ℝ≥0∞)) (by simp)
  obtain ⟨k,hk⟩ := ENNReal.exists_inv_nat_lt (ne_of_gt hδ)
  refine ⟨k,fun A hA hμA => ?_⟩
  apply le_of_not_gt
  intro hνA
  have hsmall : ρ A < δ := hνA.trans_le
    ((ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.le_succ k)).trans hk.le)
  have hμsmall := hbound A hsmall
  rw [Measure.setLIntegral_rnDeriv' hac hA.isClosed.measurableSet] at hμsmall
  exact (not_lt_of_ge hμA) hμsmall

end BenchmarkJump

#print axioms BenchmarkJump.ac_mem_clopenACBound
