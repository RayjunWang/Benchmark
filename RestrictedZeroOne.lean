import RestrictedModulus
import RestrictedPermutation
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent

open MeasureTheory Set Filter
open scoped ENNReal Topology symmDiff

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

/-- Independent copies of arbitrarily accurate event approximants force a zero-one law.
The concrete iid-cylinder construction is supplied below. -/
theorem real_zero_one_of_approximants {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (F : Set α) (hF : MeasurableSet F)
    (ha : ∀ ε : ℝ, 0 < ε → ∃ B C : Set α,
      MeasurableSet B ∧ MeasurableSet C ∧
      μ.real (F ∆ B) < ε ∧ μ.real (F ∆ C) < ε ∧
      μ.real (B ∩ C) = (μ.real B) ^ 2) :
    μ.real F = 0 ∨ μ.real F = 1 := by
  let p := μ.real F
  have hid : p = p ^ 2 := by
    by_contra hp
    have hd : 0 < |p - p ^ 2| := abs_pos.mpr (sub_ne_zero.mpr hp)
    let ε := |p - p ^ 2| / 8
    have hε : 0 < ε := by dsimp [ε]; positivity
    obtain ⟨B, C, hBm, hCm, hB, hC, hi⟩ := ha ε hε
    let b := μ.real B
    have hsub : F ∆ (B ∩ C) ⊆ (F ∆ B) ∪ (F ∆ C) := by
      intro x hx
      simp only [mem_symmDiff, mem_inter_iff, mem_union] at *
      tauto
    have hinter : |p - b ^ 2| < 2 * ε := by
      have hle : |p - b ^ 2| ≤ μ.real (F ∆ B) + μ.real (F ∆ C) := by
        calc
          |p - b ^ 2| = |μ.real F - μ.real (B ∩ C)| := by rw [hi]
          _ ≤ μ.real (F ∆ (B ∩ C)) :=
            abs_measureReal_sub_le_measureReal_symmDiff hF.nullMeasurableSet (hBm.inter hCm).nullMeasurableSet
          _ ≤ μ.real ((F ∆ B) ∪ (F ∆ C)) := measureReal_mono hsub
          _ ≤ μ.real (F ∆ B) + μ.real (F ∆ C) := measureReal_union_le _ _
      linarith
    have hbp : |b - p| ≤ ε := by
      have he := (abs_measureReal_sub_le_measureReal_symmDiff hF.nullMeasurableSet hBm.nullMeasurableSet).trans_lt hB
      exact (by simpa only [abs_sub_comm] using he.le)
    have hp0 : 0 ≤ p := measureReal_nonneg
    have hb0 : 0 ≤ b := measureReal_nonneg
    have hp1 : p ≤ 1 := measureReal_le_one
    have hb1 : b ≤ 1 := measureReal_le_one
    have hsq : |b ^ 2 - p ^ 2| ≤ 2 * ε := by
      calc
        |b ^ 2 - p ^ 2| = |b - p| * |b + p| := by rw [← abs_mul]; congr 1; ring
        _ ≤ ε * 2 := mul_le_mul hbp (abs_le.mpr ⟨by linarith, by linarith⟩)
          (abs_nonneg _) hε.le
        _ = 2 * ε := by ring
    have htri := abs_sub_le p (b ^ 2) (p ^ 2)
    dsimp only [ε] at hinter hsq
    linarith
  have he : p * (p - 1) = 0 := by nlinarith [hid]
  rcases mul_eq_zero.mp he with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- The iid product zero-one law for events invariant modulo null sets under finite block swaps. -/
theorem tailProbability_zero_one_of_blockSwap_invariant (F : Set RealSequences)
    (hF : MeasurableSet F)
    (hinv : ∀ N, (permute (blockSwap N)) ⁻¹' F =ᵐ[tailProbability] F) :
    tailProbability F = 0 ∨ tailProbability Fᶜ = 0 := by
  have hreal : tailProbability.real F = 0 ∨ tailProbability.real F = 1 := by
    apply real_zero_one_of_approximants tailProbability F hF
    intro ε hε
    have hcover : ∃ D : Set (Set RealSequences), D.Countable ∧
        D ⊆ measurableCylinders (fun _ : ℕ => ℝ) ∧ tailProbability (⋃₀ D)ᶜ = 0 := by
      refine ⟨{univ}, countable_singleton _, ?_, by simp⟩
      intro s hs
      have hs' : s = univ := mem_singleton_iff.mp hs
      rw [hs']
      exact univ_mem_measurableCylinders _
    obtain ⟨B, hBC, hBF⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      (μ := tailProbability) isSetRing_measurableCylinders hcover
      generateFrom_measurableCylinders.symm hF (ENNReal.ofReal_pos.mpr hε)
    obtain ⟨s, A, hA, rfl⟩ := (mem_measurableCylinders B).mp hBC
    let B : Set RealSequences := cylinder s A
    let N : ℕ := s.sup id + 1
    let C : Set RealSequences := (permute (blockSwap N)) ⁻¹' B
    have hsN : s ⊆ Finset.range N := by
      intro k hk
      have hle : k ≤ s.sup id := Finset.le_sup (f := id) hk
      exact Finset.mem_range.mpr (by dsimp [N]; omega)
    have hBm : MeasurableSet B := hA.cylinder s
    have hCm : MeasurableSet C := (measurable_permute (blockSwap N)) hBm
    have hBr : tailProbability.real (F ∆ B) < ε := by
      have he := (ENNReal.toReal_lt_toReal (measure_ne_top tailProbability _)
        ENNReal.ofReal_ne_top).mpr hBF
      simpa only [Measure.real, ENNReal.toReal_ofReal hε.le, symmDiff_comm, B] using he
    have heq : F ∆ C =ᵐ[tailProbability] (permute (blockSwap N)) ⁻¹' (F ∆ B) := by
      simpa only [preimage_symmDiff, C] using
        (hinv N).symm.symmDiff (ae_eq_refl ((permute (blockSwap N)) ⁻¹' B))
    have hCr : tailProbability.real (F ∆ C) < ε := by
      calc
        tailProbability.real (F ∆ C) =
            tailProbability.real ((permute (blockSwap N)) ⁻¹' (F ∆ B)) :=
          measureReal_congr heq
        _ = tailProbability.real (F ∆ B) := by
          change (tailProbability ((permute (blockSwap N)) ⁻¹' (F ∆ B))).toReal =
            (tailProbability (F ∆ B)).toReal
          rw [← Measure.map_apply (measurable_permute (blockSwap N)) (hF.symmDiff hBm),
            (measurePreserving_permute (blockSwap N)).map_eq]
        _ < ε := hBr
    exact ⟨B, C, hBm, hCm, hBr, hCr, cylinder_blockSwap_independent s N hsN A hA⟩
  rcases hreal with h0 | h1
  · exact Or.inl ((measureReal_eq_zero_iff (measure_ne_top tailProbability F)).mp h0)
  · apply Or.inr
    apply (measureReal_eq_zero_iff (measure_ne_top tailProbability Fᶜ)).mp
    have he := measureReal_add_measureReal_compl (μ := tailProbability) hF
    have hu : tailProbability.real univ = 1 := by simp [Measure.real]
    rw [h1, hu] at he
    linarith

end MeasureEquivalenceRestrictedProduct

#print axioms MeasureEquivalenceRestrictedProduct.real_zero_one_of_approximants
#print axioms MeasureEquivalenceRestrictedProduct.tailProbability_zero_one_of_blockSwap_invariant
