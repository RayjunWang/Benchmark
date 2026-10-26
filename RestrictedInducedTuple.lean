import RestrictedInducedFamily

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid
open MeasureEquivalenceInducedCorners MeasureUnitary

theorem inducedFamilyPhase_coe (k : CompactSequences) (i : CharacterIndex) (u : InducedHilbert) :
    inducedFamilyPhase k i u =ᵐ[cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0)]
      (fun p => ambientPhase k i (orbitPoint p) * u p) :=
  inducedPhaseUnitary_coe restrictedProductMeasure (stageSet 0) (ambientPhase k i)
    (ambientPhase_measurable _ _) (ambientPhase_norm _ _) u

theorem inducedFamilyPhase_factor (k : CompactSequences) (i : CharacterIndex) (u : InducedHilbert) :
    inducedFamilyPhase k i u = character i k • inducedFamilyPhase 0 i u := by
  apply Lp.ext
  filter_upwards [inducedFamilyPhase_coe k i u, inducedFamilyPhase_coe 0 i u,
    Lp.coeFn_smul (character i k) (inducedFamilyPhase 0 i u)] with p hp hp0 hsmul
  rw [hp, hsmul]
  change ambientPhase k i (orbitPoint p) * u p = character i k * (inducedFamilyPhase 0 i u) p
  rw [hp0]
  simp only [ambientPhase, zero_add, character_add, mul_assoc]

theorem inducedFamilyPhase_continuous (i : CharacterIndex) :
    Continuous (fun k : CompactSequences => inducedFamilyPhase k i) := by
  apply (OperatorCoding.strongUnitary_continuous_iff _).mpr
  intro u
  have he : (fun k : CompactSequences => inducedFamilyPhase k i u) =
      (fun k : CompactSequences => character i k • inducedFamilyPhase 0 i u) :=
    funext (fun k => inducedFamilyPhase_factor k i u)
  rw [he]
  exact (character_continuous i).smul continuous_const

abbrev Generator := CharacterIndex ⊕ RationalGroup

def inducedGenerator (k : CompactSequences) (i : Generator) :
    OperatorCoding.StrongUnitary InducedHilbert :=
  Sum.elim (inducedFamilyPhase k) inducedFamilyShift i

theorem inducedGenerator_continuous (i : Generator) :
    Continuous (fun k : CompactSequences => inducedGenerator k i) := by
  cases i with
  | inl i => exact inducedFamilyPhase_continuous i
  | inr q => exact continuous_const

def generatorEnumeration : ℕ → Generator := Classical.choose (exists_surjective_nat Generator)

theorem generatorEnumeration_surjective : Function.Surjective generatorEnumeration :=
  Classical.choose_spec (exists_surjective_nat Generator)

def inducedTuple (k : CompactSequences) (n : ℕ) : OperatorCoding.StrongUnitary InducedHilbert :=
  inducedGenerator k (generatorEnumeration n)

theorem inducedTuple_continuous : Continuous inducedTuple :=
  continuous_pi (fun n => inducedGenerator_continuous (generatorEnumeration n))

theorem exists_inducedTuple_intertwiner_of_zeroSum (k l : CompactSequences)
    (hkl : l - k ∈ zeroSumSubgroup) :
    ∃ W : InducedHilbert ≃ₗᵢ[ℂ] InducedHilbert,
      ∀ n u, W (inducedTuple k n u) = inducedTuple l n (W u) := by
  obtain ⟨h, hh, he⟩ := hkl
  have hs : Summable (fun n => |h n|) := by
    simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using
      (lp.memℓp h).summable (by norm_num : (0 : ℝ) < (1 : ℝ≥0∞).toReal)
  have hsum : (∑' n, h n) = 0 := (mem_zeroSumSpace h).mp hh
  have he' : k + sequenceEmbedding (h : RealSequences) = l := by
    change k + l1Embedding h = l
    rw [he]
    abel
  obtain ⟨W, hphase, hshift⟩ := exists_induced_H_intertwiner (h : RealSequences) hs hsum k
  refine ⟨W, ?_⟩
  intro n u
  unfold inducedTuple inducedGenerator
  cases generatorEnumeration n with
  | inl i => simpa only [Sum.elim_inl, he'] using hphase i u
  | inr q => exact hshift q u

theorem intertwines_generators_of_intertwines_tuple (k l : CompactSequences)
    (W : InducedHilbert ≃ₗᵢ[ℂ] InducedHilbert)
    (hW : ∀ n u, W (inducedTuple k n u) = inducedTuple l n (W u)) :
    (∀ i u, W (inducedFamilyPhase k i u) = inducedFamilyPhase l i (W u)) ∧
      (∀ q u, W (inducedFamilyShift q u) = inducedFamilyShift q (W u)) := by
  constructor
  · intro i u
    obtain ⟨n, hn⟩ := generatorEnumeration_surjective (Sum.inl i)
    have hh := hW n u
    simpa only [inducedTuple, inducedGenerator, hn, Sum.elim_inl] using hh
  · intro q u
    obtain ⟨n, hn⟩ := generatorEnumeration_surjective (Sum.inr q)
    have hh := hW n u
    simpa only [inducedTuple, inducedGenerator, hn, Sum.elim_inr] using hh

end MeasureEquivalenceRestrictedPhase

#print axioms MeasureEquivalenceRestrictedPhase.inducedTuple_continuous
#print axioms MeasureEquivalenceRestrictedPhase.exists_inducedTuple_intertwiner_of_zeroSum
