import UnitarySpectralCodeBorel
import KernelCantorNormalization
import OperatorCyclicRepresentation
import HilbertSequenceTopology

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace OperatorCoding

open MeasureUnitary SpectralDomination

def spectralCountingWeight : Measure ℕ :=
  Measure.sum (fun n : ℕ => (2⁻¹ : ℝ≥0∞) ^ n • Measure.dirac n)

instance spectralCountingWeight_finite : IsFiniteMeasure spectralCountingWeight := by
  constructor
  simp only [spectralCountingWeight, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (mem_univ _), mul_one]
  rw [ENNReal.tsum_geometric_two]
  norm_num

theorem spectralCountingWeight_singleton_ne_zero (n : ℕ) : spectralCountingWeight {n} ≠ 0 := by
  have hle := Measure.le_sum (fun k : ℕ => (2⁻¹ : ℝ≥0∞) ^ k • Measure.dirac k) n
  have hmass := Measure.le_iff'.mp hle {n}
  have hp : 0 < ((2⁻¹ : ℝ≥0∞) ^ n • Measure.dirac n) {n} := by
    simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (mem_singleton n), mul_one]
    exact pos_iff_ne_zero.mpr (pow_ne_zero n (by simp))
  exact ne_of_gt (hp.trans_le hmass)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] [SecondCountableTopology H]

local instance : MeasurableSpace H := borel _
local instance : BorelSpace H := ⟨rfl⟩
local instance : MeasurableSpace (StrongUnitary H) := borel _
local instance : BorelSpace (StrongUnitary H) := ⟨rfl⟩

def unitaryCantorProbability (U : StrongUnitary H) : ProbabilityMeasure Cantor :=
  cantorKernelProbability (greedyCodeKernel spectralCountingWeight)
    (greedyCodeKernel_ne_zero spectralCountingWeight spectralCountingWeight_singleton_ne_zero) U

theorem unitaryCantorProbability_measurable : Measurable (unitaryCantorProbability (H := H)) :=
  cantorKernelProbability_measurable _ _

theorem unitaryCantorProbability_classification (U V : StrongUnitary H) :
    ElementConjugate U V ↔ MeasureEquivalent (unitaryCantorProbability U) (unitaryCantorProbability V) := by
  have hcode := greedyCodeKernel_classification spectralCountingWeight spectralCountingWeight_singleton_ne_zero U V
  have hnorm := cantorKernelProbability_classification (greedyCodeKernel spectralCountingWeight)
    (greedyCodeKernel_ne_zero spectralCountingWeight spectralCountingWeight_singleton_ne_zero) U V
  change ElementConjugate U V ↔
    ((cantorKernelProbability _ _ U : Measure Cantor) ≪ cantorKernelProbability _ _ V ∧
      (cantorKernelProbability _ _ V : Measure Cantor) ≪ cantorKernelProbability _ _ U)
  rw [hnorm]
  rw [← hcode]
  constructor
  · rintro ⟨W,hW⟩
    refine ⟨W,fun x => ?_⟩
    have he := congrArg (fun T : StrongUnitary H => T (W x)) hW
    simpa using he
  · rintro ⟨W,hW⟩
    refine ⟨W,?_⟩
    apply LinearIsometryEquiv.ext
    intro x
    change W (U (W.symm x)) = V x
    rw [hW, W.apply_symm_apply]

theorem unitaries_borelReduce_measureEquivalence :
    BorelReducesWith (borel (StrongUnitary H)) inferInstance ElementConjugate MeasureEquivalent :=
  ⟨unitaryCantorProbability, unitaryCantorProbability_measurable, unitaryCantorProbability_classification⟩

instance spectralCanonicalHilbert_nontrivial : Nontrivial CanonicalHilbert := by
  refine ⟨⟨0, lp.single 2 0 (1 : ℂ), ?_⟩⟩
  intro h
  have he := congrArg (fun v : CanonicalHilbert => v 0) h
  change (0 : ℂ) = 1 at he
  exact zero_ne_one he

theorem cyclicRepresentations_borelReduce_measureEquivalence :
    BorelReducesWith (unitaryRepresentationBorel (Multiplicative ℤ)) inferInstance
      UnitaryRepresentationEquivalent MeasureEquivalent :=
  borelReducesWith_trans cyclicRepresentations_borelBireducible_unitaries.1
    unitaries_borelReduce_measureEquivalence

end OperatorCoding

#print axioms OperatorCoding.cyclicRepresentations_borelReduce_measureEquivalence
