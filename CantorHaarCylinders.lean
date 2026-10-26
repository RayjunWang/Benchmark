import ClopenHaarNode
import Mathlib.Data.Fin.Tuple.Basic

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

abbrev HaarCantor := ℕ → Bool
abbrev HaarNodeIndex := Σ n : ℕ, Fin n → Bool

def prefixCylinder {n : ℕ} (s : Fin n → Bool) : Set HaarCantor :=
  {x | ∀ i : Fin n, x i = s i}

theorem isClopen_prefixCylinder {n : ℕ} (s : Fin n → Bool) :
    IsClopen (prefixCylinder s) := by
  change IsClopen {x : HaarCantor | ∀ i : Fin n, x i = s i}
  simp only [setOf_forall]
  apply isClopen_iInter_of_finite
  intro i
  exact (isClopen_discrete ({s i} : Set Bool)).preimage (continuous_apply (i : ℕ))

theorem prefixCylinder_nonempty {n : ℕ} (s : Fin n → Bool) :
    (prefixCylinder s).Nonempty := by
  let x : HaarCantor := fun i => if hi : i < n then s ⟨i, hi⟩ else false
  refine ⟨x, ?_⟩
  intro i
  simp [x, i.isLt]

theorem prefixCylinder_zero (s : Fin 0 → Bool) : prefixCylinder s = univ := by
  ext x
  simp [prefixCylinder]

theorem mem_prefixCylinder_snoc {n : ℕ} (s : Fin n → Bool) (b : Bool) (x : HaarCantor) :
    x ∈ prefixCylinder (Fin.snoc s b) ↔ x ∈ prefixCylinder s ∧ x n = b := by
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · simpa only [Fin.val_castSucc, Fin.snoc_castSucc] using h i.castSucc
    · simpa only [Fin.val_last, Fin.snoc_last] using h (Fin.last n)
  · rintro ⟨hs, hb⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.val_last, Fin.snoc_last] using hb
    · simpa only [Fin.val_castSucc, Fin.snoc_castSucc] using hs j

theorem prefixCylinder_split {n : ℕ} (s : Fin n → Bool) :
    prefixCylinder (Fin.snoc s false) ∪ prefixCylinder (Fin.snoc s true) =
      prefixCylinder s := by
  ext x
  simp only [mem_union, mem_prefixCylinder_snoc]
  cases h : x n <;> simp [h]

theorem prefixCylinder_children_disjoint {n : ℕ} (s : Fin n → Bool) :
    Disjoint (prefixCylinder (Fin.snoc s false)) (prefixCylinder (Fin.snoc s true)) := by
  apply disjoint_left.mpr
  intro x hx hy
  have hx' := (mem_prefixCylinder_snoc s false x).mp hx
  have hy' := (mem_prefixCylinder_snoc s true x).mp hy
  exact Bool.false_ne_true (hx'.2.symm.trans hy'.2)

def PositiveCylinderProbabilities : Set (ProbabilityMeasure HaarCantor) :=
  {μ | ∀ n : ℕ, ∀ s : Fin n → Bool, 0 < (μ : Measure HaarCantor).real (prefixCylinder s)}

theorem isGδ_positiveCylinderProbabilities : IsGδ PositiveCylinderProbabilities := by
  have hOne (i : HaarNodeIndex) : IsOpen
      {μ : ProbabilityMeasure HaarCantor | 0 < (μ : Measure HaarCantor).real (prefixCylinder i.2)} :=
    isOpen_lt continuous_const (continuous_clopen_mass _ (isClopen_prefixCylinder i.2))
  have heq : PositiveCylinderProbabilities =
      ⋂ i : HaarNodeIndex, {μ : ProbabilityMeasure HaarCantor |
        0 < (μ : Measure HaarCantor).real (prefixCylinder i.2)} := by
    ext μ
    simp only [PositiveCylinderProbabilities, mem_setOf_eq, mem_iInter]
    exact ⟨fun h i => h i.1 i.2, fun h n s => h ⟨n, s⟩⟩
  rw [heq]
  exact IsGδ.iInter_of_isOpen hOne

def cantorHaarNode (μ : PositiveCylinderProbabilities) (i : HaarNodeIndex) :
    Lp ℝ 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) :=
  splitHaar _ (prefixCylinder (Fin.snoc i.2 false)) (prefixCylinder (Fin.snoc i.2 true))
    (isClopen_prefixCylinder _).isClosed.measurableSet
    (isClopen_prefixCylinder _).isClosed.measurableSet

theorem cantorHaarNode_norm (μ : PositiveCylinderProbabilities) (i : HaarNodeIndex) :
    ‖cantorHaarNode μ i‖ = 1 :=
  splitHaar_norm _ _ _ _ _ (prefixCylinder_children_disjoint i.2)
    (μ.property (i.1 + 1) (Fin.snoc i.2 false))
    (μ.property (i.1 + 1) (Fin.snoc i.2 true))

theorem cantorHaarNode_inner_one (μ : PositiveCylinderProbabilities) (i : HaarNodeIndex) :
    inner ℝ (cantorHaarNode μ i)
      (indicatorConstLp 2 MeasurableSet.univ
        (measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) univ) (1 : ℝ)) = 0 :=
  splitHaar_inner_one _ _ _ _ _

#print axioms isGδ_positiveCylinderProbabilities
#print axioms cantorHaarNode_norm

end BenchmarkJump
