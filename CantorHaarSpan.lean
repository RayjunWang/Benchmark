import CantorHaarCylinders
import HaarSplitSpan

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace BenchmarkJump

def cantorOneVector (μ : PositiveCylinderProbabilities) :
    Lp ℝ 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) :=
  indicatorConstLp 2 MeasurableSet.univ (measure_ne_top _ _) (1 : ℝ)

def cantorPrefixVector (μ : PositiveCylinderProbabilities) {n : ℕ} (s : Fin n → Bool) :
    Lp ℝ 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) :=
  indicatorConstLp 2 (isClopen_prefixCylinder s).isClosed.measurableSet
    (measure_ne_top _ _) (1 : ℝ)

def cantorHaarSpan (μ : PositiveCylinderProbabilities) :
    Submodule ℝ (Lp ℝ 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) :=
  Submodule.span ℝ ({cantorOneVector μ} ∪ range (cantorHaarNode μ))

theorem cantorOneVector_mem_span (μ : PositiveCylinderProbabilities) :
    cantorOneVector μ ∈ cantorHaarSpan μ := Submodule.subset_span (Or.inl rfl)

theorem cantorHaarNode_mem_span (μ : PositiveCylinderProbabilities) (i : HaarNodeIndex) :
    cantorHaarNode μ i ∈ cantorHaarSpan μ := Submodule.subset_span (Or.inr ⟨i, rfl⟩)

/-- Every genuine finite-prefix indicator is in the algebraic span of the
constant and the finite-level Haar nodes. -/
theorem cantorPrefixVector_mem_span (μ : PositiveCylinderProbabilities) :
    ∀ n : ℕ, ∀ s : Fin n → Bool, cantorPrefixVector μ s ∈ cantorHaarSpan μ := by
  intro n
  induction n with
  | zero =>
      intro s
      have heq : cantorPrefixVector μ s = cantorOneVector μ := by
        simp only [cantorPrefixVector, prefixCylinder_zero, cantorOneVector]
      rw [heq]
      exact cantorOneVector_mem_span μ
  | succ n ih =>
      intro s
      let t : Fin n → Bool := Fin.init s
      let A := prefixCylinder (Fin.snoc t false)
      let B := prefixCylinder (Fin.snoc t true)
      have hA : MeasurableSet A := (isClopen_prefixCylinder _).isClosed.measurableSet
      have hB : MeasurableSet B := (isClopen_prefixCylinder _).isClosed.measurableSet
      have hParent :
          indicatorConstLp 2 (hA.union hB)
            (measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) _)
            (1 : ℝ) ∈ cantorHaarSpan μ := by
        simpa only [A, B, prefixCylinder_split, cantorPrefixVector] using ih t
      have hNode : splitHaar ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
          A B hA hB ∈ cantorHaarSpan μ := cantorHaarNode_mem_span μ ⟨n, t⟩
      have hZ : Submodule.span ℝ
          ({indicatorConstLp 2 (hA.union hB)
              (measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) _)
              (1 : ℝ), splitHaar ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
                A B hA hB} : Set (Lp ℝ 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))) ≤
          cantorHaarSpan μ := by
        apply Submodule.span_le.mpr
        intro v hv
        rcases hv with hv | hv
        · exact hv ▸ hParent
        · exact (mem_singleton_iff.mp hv) ▸ hNode
      have hChildren := splitHaar_children_mem_span
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A B hA hB
        (prefixCylinder_children_disjoint t) (μ.property (n + 1) (Fin.snoc t false))
          (μ.property (n + 1) (Fin.snoc t true))
      have hFalse : cantorPrefixVector μ (Fin.snoc t false) ∈ cantorHaarSpan μ := hZ hChildren.1
      have hTrue : cantorPrefixVector μ (Fin.snoc t true) ∈ cantorHaarSpan μ := hZ hChildren.2
      have hsnoc : Fin.snoc t (s (Fin.last n)) = s := Fin.snoc_init_self s
      cases hlast : s (Fin.last n)
      · rw [hlast] at hsnoc
        simpa only [hsnoc] using hFalse
      · rw [hlast] at hsnoc
        simpa only [hsnoc] using hTrue

#print axioms cantorPrefixVector_mem_span

end BenchmarkJump
