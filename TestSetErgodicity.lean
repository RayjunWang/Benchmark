import ConditionalFibers

/-! A countable determining family suffices to test independence of an
invariant set from the whole sigma-algebra. -/

open MeasureTheory Set
open scoped ENNReal

namespace MeasureEquivalenceErgodicDecomposition

variable {Z : Type*} [MeasurableSpace Z] [StandardBorelSpace Z]
    (ν : Measure Z) [IsProbabilityMeasure ν]

theorem zero_or_conull_of_test_factorization (B : Set Z) (hB : MeasurableSet B)
    (htest : ∀ s : Finset ℕ, ν.real (determiningSet s ∩ B) =
      ν.real (determiningSet s) * ν.real B) :
    ν B = 0 ∨ ν Bᶜ = 0 := by
  have heq : ν.restrict B = (ν B) • ν := by
    apply MeasureTheory.ext_of_generate_finite (range (determiningSet (Z := Z)))
      determiningSet_generates.symm determiningSet_isPiSystem
    · rintro _ ⟨s, rfl⟩
      rw [Measure.restrict_apply (determiningSet_measurable s), Measure.smul_apply, smul_eq_mul]
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top ν _)
        (ENNReal.mul_ne_top (measure_ne_top ν _) (measure_ne_top ν _))).mp
      rw [ENNReal.toReal_mul]
      exact (htest s).trans (mul_comm _ _)
    · simp
  have hBB : ν B = ν B * ν B := by
    have h := congrArg (fun ρ : Measure Z => ρ B) heq
    simpa only [Measure.restrict_apply hB, Set.inter_self, Measure.smul_apply, smul_eq_mul] using h
  have hr : ν.real B = ν.real B * ν.real B := by
    simpa only [ENNReal.toReal_mul, ← measureReal_def] using congrArg ENNReal.toReal hBB
  have hf : ν.real B * (ν.real B - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hf with hz | ho
  · exact Or.inl ((measureReal_eq_zero_iff (measure_ne_top ν B)).mp hz)
  · right
    have hr1 : ν.real B = 1 := sub_eq_zero.mp ho
    have hb1 : ν B = 1 := (ENNReal.toReal_eq_toReal_iff' (measure_ne_top ν B)
      ENNReal.one_ne_top).mp (by simpa only [ENNReal.toReal_one] using hr1)
    rw [measure_compl hB (measure_ne_top ν B), measure_univ, hb1, tsub_self]

end MeasureEquivalenceErgodicDecomposition

#print axioms MeasureEquivalenceErgodicDecomposition.zero_or_conull_of_test_factorization
