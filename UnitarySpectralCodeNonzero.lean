import UnitarySpectralMeasureClassification

/-! The finite multiplicity code of a nonzero Hilbert space is nonzero,
so its probability normalization is legitimate. -/

open MeasureTheory Set Filter
open scoped ENNReal

namespace OperatorCoding

open MeasureUnitary

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] [SecondCountableTopology H]

theorem cyclicSpan_zero (U : StrongUnitary H) : cyclicSpan U 0 = ⊥ := by
  apply bot_unique
  apply cyclicSpan_minimal U 0 ⊥ (by change IsClosed ({(0 : H)} : Set H); exact isClosed_singleton)
  intro n
  simp only [map_zero, Submodule.zero_mem]

theorem exists_greedyCyclicGenerator_ne_zero (U : StrongUnitary H) :
    ∃ n, greedyCyclicGenerator U n ≠ 0 := by
  by_contra h
  push_neg at h
  have hbot : greedyCyclicAllSpan U = ⊥ := by
    unfold greedyCyclicAllSpan
    simp_rw [h,cyclicSpan_zero]
    simp
  exact top_ne_bot ((greedyCyclicAllSpan_eq_top U).symm.trans hbot)

theorem exists_greedySpectralMeasure_ne_zero (U : StrongUnitary H) :
    ∃ n, greedySpectralMeasure U n ≠ 0 := by
  obtain ⟨n,hn⟩ := exists_greedyCyclicGenerator_ne_zero U
  refine ⟨n, ?_⟩
  intro hzero
  have hmass := representationVectorMeasure_mass_toReal (unitaryCircleRepresentation U)
    (greedyCyclicGenerator U n)
  change (greedySpectralMeasure U n Set.univ).toReal = ‖greedyCyclicGenerator U n‖ ^ 2 at hmass
  simp only [hzero,Measure.coe_zero,Pi.zero_apply,ENNReal.toReal_zero] at hmass
  apply hn
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (greedyCyclicGenerator U n)]

theorem support_subset_multiplicityLayer_zero {X : Type*} [MeasurableSpace X]
    (A : ℕ → Set X) (i : ℕ) : A i ⊆ multiplicityLayer A 0 := by
  classical
  intro x hx
  simp only [multiplicityLayer,mem_setOf_eq,Nat.cast_zero]
  have hle : (1 : ℝ≥0∞) ≤ fiberMultiplicity A x := by
    calc
      (1 : ℝ≥0∞) = (A i).indicator (fun _ => (1 : ℝ≥0∞)) x := by simp [hx]
      _ ≤ fiberMultiplicity A x := ENNReal.le_tsum i
  exact lt_of_lt_of_le zero_lt_one hle

theorem unitary_multiplicityLayerCode_ne_zero (U : StrongUnitary H)
    (μ : Measure SpectralCircle) [IsFiniteMeasure μ] (A : ℕ → Set SpectralCircle)
    (hA : ∀ n, MeasurableSet (A n))
    (hUμ : ∀ n, greedySpectralMeasure U n ≪ μ.restrict (A n))
    (w : Measure ℕ) [IsFiniteMeasure w] (hw : ∀ n, w {n} ≠ 0) :
    multiplicityLayerCode μ A w ≠ 0 := by
  intro hzero
  have hac : fiberRestrictedMeasure μ (multiplicityLayer A) ≪ multiplicityLayerCode μ A w :=
    (weightedFiberMeasure_measureClass_count μ (multiplicityLayer A) w hw).1
  rw [hzero,Measure.absolutelyContinuous_zero_iff] at hac
  have hLayer : μ.restrict (multiplicityLayer A 0) = 0 := by
    apply Measure.measure_univ_eq_zero.mp
    have h := congrArg (fun M : Measure (SpectralCircle × ℕ) => M (Set.univ ×ˢ {(0 : ℕ)})) hac
    change fiberRestrictedMeasure μ (multiplicityLayer A) (Set.univ ×ˢ {(0 : ℕ)}) = 0 at h
    rw [fiberRestrictedMeasure_rectangle μ (multiplicityLayer A)
      (multiplicityLayer_measurable A hA) Set.univ MeasurableSet.univ 0] at h
    exact h
  obtain ⟨n,hn⟩ := exists_greedySpectralMeasure_ne_zero U
  apply hn
  apply Measure.absolutelyContinuous_zero_iff.mp
  have hnull : μ.restrict (A n) = 0 := by
    apply Measure.restrict_eq_zero.mpr
    apply measure_mono_null (support_subset_multiplicityLayer_zero A n)
    exact Measure.restrict_eq_zero.mp hLayer
  simpa only [hnull] using hUμ n

end
end OperatorCoding

#print axioms OperatorCoding.unitary_multiplicityLayerCode_ne_zero

