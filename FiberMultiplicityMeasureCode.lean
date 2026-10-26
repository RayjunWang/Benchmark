import FiberMeasureClass
import FiberMultiplicityLayers

/-! Positive finite counting weights give a finite measure-class code for
all multiplicity layers, without changing any of their null sets. -/

open MeasureTheory Set Filter
open scoped ENNReal

namespace MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X]

def weightedFiberMeasure (μ : Measure X) (A : ℕ → Set X) (w : Measure ℕ) : Measure (X × ℕ) :=
  (μ.prod w).restrict (measureFiberSet A)

instance weightedFiberMeasure_finite (μ : Measure X) [IsFiniteMeasure μ]
    (A : ℕ → Set X) (w : Measure ℕ) [IsFiniteMeasure w] :
    IsFiniteMeasure (weightedFiberMeasure μ A w) := by
  unfold weightedFiberMeasure
  infer_instance

theorem count_measureClass_of_singletons (w : Measure ℕ) (hw : ∀ i, w {i} ≠ 0) :
    (Measure.count : Measure ℕ) ≪ w ∧ w ≪ (Measure.count : Measure ℕ) := by
  constructor
  · intro s hs
    apply Measure.count_eq_zero_iff.mpr
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro i hi
    exact hw i (measure_mono_null (Set.singleton_subset_iff.mpr hi) hs)
  · intro s hs
    rw [Measure.count_eq_zero_iff.mp hs]
    exact measure_empty

theorem weightedFiberMeasure_measureClass_count (μ : Measure X) [IsFiniteMeasure μ]
    (A : ℕ → Set X) (w : Measure ℕ) [IsFiniteMeasure w] (hw : ∀ i, w {i} ≠ 0) :
    fiberRestrictedMeasure μ A ≪ weightedFiberMeasure μ A w ∧
      weightedFiberMeasure μ A w ≪ fiberRestrictedMeasure μ A := by
  have h := count_measureClass_of_singletons w hw
  exact ⟨((Measure.AbsolutelyContinuous.rfl (μ := μ)).prod h.1).restrict _,
    ((Measure.AbsolutelyContinuous.rfl (μ := μ)).prod h.2).restrict _⟩

theorem weightedFiberMeasure_measureClass_iff (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (w w' : Measure ℕ) [IsFiniteMeasure w] [IsFiniteMeasure w']
    (hw : ∀ i, w {i} ≠ 0) (hw' : ∀ i, w' {i} ≠ 0) :
    (weightedFiberMeasure μ A w ≪ weightedFiberMeasure ν B w' ∧
      weightedFiberMeasure ν B w' ≪ weightedFiberMeasure μ A w) ↔
      ∀ i, μ.restrict (A i) ≪ ν.restrict (B i) ∧ ν.restrict (B i) ≪ μ.restrict (A i) := by
  have hμ := weightedFiberMeasure_measureClass_count μ A w hw
  have hν := weightedFiberMeasure_measureClass_count ν B w' hw'
  rw [← fiberRestrictedMeasure_measureClass_iff μ ν A B hA hB]
  constructor
  · rintro ⟨hAB,hBA⟩
    exact ⟨hμ.1.trans (hAB.trans hν.2),hν.1.trans (hBA.trans hμ.2)⟩
  · rintro ⟨hAB,hBA⟩
    exact ⟨hμ.2.trans (hAB.trans hν.1),hν.2.trans (hBA.trans hμ.1)⟩

def multiplicityLayerCode (μ : Measure X) (A : ℕ → Set X) (w : Measure ℕ) : Measure (X × ℕ) :=
  weightedFiberMeasure μ (multiplicityLayer A) w

instance multiplicityLayerCode_finite (μ : Measure X) [IsFiniteMeasure μ]
    (A : ℕ → Set X) (w : Measure ℕ) [IsFiniteMeasure w] :
    IsFiniteMeasure (multiplicityLayerCode μ A w) := by
  unfold multiplicityLayerCode
  infer_instance

theorem multiplicityLayerCode_classification (μ : Measure X) [IsFiniteMeasure μ]
    (A B : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (w : Measure ℕ) [IsFiniteMeasure w] (hw : ∀ i, w {i} ≠ 0) :
    (multiplicityLayerCode μ A w ≪ multiplicityLayerCode μ B w ∧
      multiplicityLayerCode μ B w ≪ multiplicityLayerCode μ A w) ↔
      fiberMultiplicity A =ᵐ[μ] fiberMultiplicity B := by
  rw [multiplicityLayerCode, multiplicityLayerCode,
    weightedFiberMeasure_measureClass_iff μ μ (multiplicityLayer A) (multiplicityLayer B)
      (multiplicityLayer_measurable A hA) (multiplicityLayer_measurable B hB) w w hw hw]
  exact multiplicityLayer_measureClass_iff μ A B hA hB

end
end MeasureUnitary

#print axioms MeasureUnitary.multiplicityLayerCode_classification
