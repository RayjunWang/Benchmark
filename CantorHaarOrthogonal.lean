import CantorHaarContinuity
import HaarMeanZero
import Mathlib.Analysis.InnerProductSpace.Orthonormal

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

theorem cantorHaarFunction_eq_of_prefix (μ : PositiveCylinderProbabilities)
    (i : HaarNodeIndex) (x y : HaarCantor)
    (hxy : ∀ j : Fin (i.1 + 1), x j = y j) :
    cantorHaarFunction μ i x = cantorHaarFunction μ i y := by
  classical
  have hC (b : Bool) : x ∈ prefixCylinder (Fin.snoc i.2 b) ↔
      y ∈ prefixCylinder (Fin.snoc i.2 b) := by
    constructor
    · intro hx j
      rw [← hxy j]
      exact hx j
    · intro hy j
      rw [hxy j]
      exact hy j
  unfold cantorHaarFunction haarNodeFunction
  by_cases hxf : x ∈ prefixCylinder (Fin.snoc i.2 false) <;>
    by_cases hxt : x ∈ prefixCylinder (Fin.snoc i.2 true)
  all_goals simp [hxf, hxt, ← hC false, ← hC true]

theorem cantorHaarFunction_constant_of_lt (μ : PositiveCylinderProbabilities)
    {n m : ℕ} (hnm : n < m) (s : Fin n → Bool) (t : Fin m → Bool) :
    ∃ c : ℝ, ∀ x ∈ prefixCylinder t, cantorHaarFunction μ ⟨n, s⟩ x = c := by
  obtain ⟨y, hy⟩ := prefixCylinder_nonempty t
  refine ⟨cantorHaarFunction μ ⟨n, s⟩ y, ?_⟩
  intro x hx
  apply cantorHaarFunction_eq_of_prefix μ ⟨n, s⟩ x y
  intro j
  have hj : (j : ℕ) < n + 1 := j.isLt
  have hjm : (j : ℕ) < m := by omega
  exact (hx ⟨j, hjm⟩).trans (hy ⟨j, hjm⟩).symm

theorem cantorHaarFunction_zero_on_other (μ : PositiveCylinderProbabilities)
    {n : ℕ} (s t : Fin n → Bool) (hst : s ≠ t) :
    ∀ x ∈ prefixCylinder t, cantorHaarFunction μ ⟨n, s⟩ x = 0 := by
  classical
  intro x hx
  have hNot : x ∉ prefixCylinder s := by
    intro hs
    apply hst
    funext j
    exact (hs j).symm.trans (hx j)
  have hf : x ∉ prefixCylinder (Fin.snoc s false) :=
    fun h => hNot ((mem_prefixCylinder_snoc s false x).mp h).1
  have ht : x ∉ prefixCylinder (Fin.snoc s true) :=
    fun h => hNot ((mem_prefixCylinder_snoc s true x).mp h).1
  simp [cantorHaarFunction, haarNodeFunction, hf, ht]

theorem cantorHaarNode_inner_zero_of_constant (μ : PositiveCylinderProbabilities)
    (i j : HaarNodeIndex) (c : ℝ)
    (hConst : ∀ x ∈ prefixCylinder i.2, cantorHaarFunction μ j x = c) :
    inner ℝ (cantorHaarNode μ i) (cantorHaarNode μ j) = 0 := by
  apply splitHaar_inner_eq_zero_of_constant_on_parent _ _ _ _ _ (cantorHaarNode μ j) c
  filter_upwards [cantorHaarNode_coe μ j] with x hx hxParent
  rw [hx]
  apply hConst x
  rw [← prefixCylinder_split]
  exact hxParent

theorem cantorHaarNode_inner_zero_of_lt (μ : PositiveCylinderProbabilities)
    {n m : ℕ} (hnm : n < m) (s : Fin n → Bool) (t : Fin m → Bool) :
    inner ℝ (cantorHaarNode μ ⟨n, s⟩) (cantorHaarNode μ ⟨m, t⟩) = 0 := by
  obtain ⟨c, hc⟩ := cantorHaarFunction_constant_of_lt μ hnm s t
  rw [real_inner_comm]
  exact cantorHaarNode_inner_zero_of_constant μ ⟨m, t⟩ ⟨n, s⟩ c hc

theorem cantorHaarNode_inner_zero_same_level (μ : PositiveCylinderProbabilities)
    {n : ℕ} (s t : Fin n → Bool) (hst : s ≠ t) :
    inner ℝ (cantorHaarNode μ ⟨n, s⟩) (cantorHaarNode μ ⟨n, t⟩) = 0 := by
  rw [real_inner_comm]
  exact cantorHaarNode_inner_zero_of_constant μ ⟨n, t⟩ ⟨n, s⟩ 0
    (cantorHaarFunction_zero_on_other μ s t hst)

/-- All actual normalized binary-tree Haar nodes are orthonormal for every
probability positive on every genuine finite-prefix cylinder. -/
theorem cantorHaarNode_orthonormal (μ : PositiveCylinderProbabilities) :
    Orthonormal ℝ (cantorHaarNode μ) := by
  refine ⟨cantorHaarNode_norm μ, ?_⟩
  rintro ⟨n, s⟩ ⟨m, t⟩ hne
  rcases lt_trichotomy n m with hnm | hnm | hmn
  · exact cantorHaarNode_inner_zero_of_lt μ hnm s t
  · subst m
    apply cantorHaarNode_inner_zero_same_level μ s t
    intro hst
    subst t
    exact hne rfl
  · rw [real_inner_comm]
    exact cantorHaarNode_inner_zero_of_lt μ hmn t s

#print axioms cantorHaarNode_orthonormal

end BenchmarkJump
