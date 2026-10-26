import FiberMultiplicityTransport

/-! Absolute continuity of a counting-fiber measure is exactly coordinatewise
absolute continuity of its restricted base measures. -/

open MeasureTheory Set Filter
open scoped ENNReal

set_option maxHeartbeats 1500000

namespace MeasureUnitary

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem fiberRestrictedMeasure_apply_sum (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (s : Set (X × ℕ)) (hs : MeasurableSet s) :
    fiberRestrictedMeasure μ A s = ∑' i : ℕ, μ.restrict (A i) ((fun x => (x,i)) ⁻¹' s) := by
  rw [fiberRestrictedMeasure_apply μ A hA s hs]
  have hmeas (i : ℕ) : Measurable (fun x => if x ∈ A i ∧ (x,i) ∈ s then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite ((hA i).inter (hs.preimage (measurable_id.prodMk measurable_const)))
      measurable_const measurable_const
  rw [lintegral_tsum (fun i => (hmeas i).aemeasurable)]
  apply tsum_congr
  intro i
  have heq : (fun x => if x ∈ A i ∧ (x,i) ∈ s then (1 : ℝ≥0∞) else 0) =
      (((fun x => (x,i)) ⁻¹' s) ∩ A i).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases ha : x ∈ A i <;> by_cases hsi : (x,i) ∈ s <;> simp [ha,hsi]
  have hslice : MeasurableSet ((fun x : X => (x,i)) ⁻¹' s) :=
    hs.preimage (measurable_id.prodMk (measurable_const (a := i)))
  rw [heq]
  exact (lintegral_indicator (hslice.inter (hA i)) (fun _ => (1 : ℝ≥0∞))).trans
    (by rw [lintegral_one, Measure.restrict_apply_univ, Measure.restrict_apply hslice])

theorem fiberRestrictedMeasure_rectangle (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (s : Set X) (hs : MeasurableSet s) (i : ℕ) :
    fiberRestrictedMeasure μ A (s ×ˢ {i}) = μ.restrict (A i) s := by
  rw [Measure.restrict_apply (hs.prod (measurableSet_singleton i)), Measure.restrict_apply hs]
  have hset : (s ×ˢ {i}) ∩ measureFiberSet A = (s ∩ A i) ×ˢ {i} := by
    ext p
    rcases p with ⟨x,j⟩
    simp only [mem_inter_iff, mem_prod, mem_singleton_iff, measureFiberSet, mem_setOf_eq]
    constructor
    · rintro ⟨⟨hx,hj⟩,ha⟩
      subst j
      exact ⟨⟨hx,ha⟩,rfl⟩
    · rintro ⟨⟨hx,ha⟩,hj⟩
      subst j
      exact ⟨⟨hx,rfl⟩,ha⟩
  rw [hset, Measure.prod_prod]
  simp only [Measure.count_singleton, mul_one]

variable (ν : Measure X) [IsFiniteMeasure ν]

theorem fiberRestrictedMeasure_absolutelyContinuous_iff (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i)) :
    fiberRestrictedMeasure μ A ≪ fiberRestrictedMeasure ν B ↔
      ∀ i, μ.restrict (A i) ≪ ν.restrict (B i) := by
  constructor
  · intro h i
    apply Measure.AbsolutelyContinuous.mk
    intro s hs hs0
    have hzero : fiberRestrictedMeasure ν B (s ×ˢ {i}) = 0 := by
      rw [fiberRestrictedMeasure_rectangle ν B hB s hs i, hs0]
    have hzero' := h hzero
    rwa [fiberRestrictedMeasure_rectangle μ A hA s hs i] at hzero'
  · intro h
    apply Measure.AbsolutelyContinuous.mk
    intro s hs hs0
    rw [fiberRestrictedMeasure_apply_sum ν B hB s hs, ENNReal.tsum_eq_zero] at hs0
    rw [fiberRestrictedMeasure_apply_sum μ A hA s hs, ENNReal.tsum_eq_zero]
    intro i
    exact h i (hs0 i)

theorem fiberRestrictedMeasure_measureClass_iff (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i)) :
    (fiberRestrictedMeasure μ A ≪ fiberRestrictedMeasure ν B ∧
      fiberRestrictedMeasure ν B ≪ fiberRestrictedMeasure μ A) ↔
      ∀ i, μ.restrict (A i) ≪ ν.restrict (B i) ∧ ν.restrict (B i) ≪ μ.restrict (A i) := by
  rw [fiberRestrictedMeasure_absolutelyContinuous_iff μ ν A B hA hB,
    fiberRestrictedMeasure_absolutelyContinuous_iff ν μ B A hB hA]
  exact forall_and.symm

end
end MeasureUnitary

#print axioms MeasureUnitary.fiberRestrictedMeasure_measureClass_iff

