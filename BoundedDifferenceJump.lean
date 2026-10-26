import JumpRows
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-! The actual bounded-difference relation and its Friedman--Stanley jump,
including the Borel facts and closed exhaustion used in the manuscript. -/

open Filter Set Topology TopologicalSpace
open scoped Topology

namespace BenchmarkJump

abbrev RealSequences := ℕ → ℝ

def UniformBound (n : ℕ) (x y : RealSequences) : Prop :=
  ∀ i, |x i - y i| ≤ (n : ℝ)

def BoundedDifference (x y : RealSequences) : Prop :=
  ∃ n : ℕ, UniformBound n x y

theorem uniformBound_refl (x : RealSequences) : UniformBound 0 x x := by
  intro i
  simp

theorem uniformBound_symm {n : ℕ} {x y : RealSequences}
    (h : UniformBound n x y) : UniformBound n y x := by
  intro i
  simpa only [abs_sub_comm] using h i

theorem uniformBound_trans {n m : ℕ} {x y z : RealSequences}
    (hxy : UniformBound n x y) (hyz : UniformBound m y z) :
    UniformBound (n + m) x z := by
  intro i
  calc
    |x i - z i| ≤ |x i - y i| + |y i - z i| := abs_sub_le _ _ _
    _ ≤ (n : ℝ) + m := add_le_add (hxy i) (hyz i)
    _ = ((n + m : ℕ) : ℝ) := by norm_cast

theorem boundedDifference_equivalence : Equivalence BoundedDifference := by
  constructor
  · intro x
    exact ⟨0, uniformBound_refl x⟩
  · rintro x y ⟨n, h⟩
    exact ⟨n, uniformBound_symm h⟩
  · rintro x y z ⟨n, hn⟩ ⟨m, hm⟩
    exact ⟨n + m, uniformBound_trans hn hm⟩

theorem isClosed_uniformBound (n : ℕ) :
    IsClosed {p : RealSequences × RealSequences | UniformBound n p.1 p.2} := by
  change IsClosed {p : RealSequences × RealSequences | ∀ i, |p.1 i - p.2 i| ≤ (n : ℝ)}
  simp only [setOf_forall]
  apply isClosed_iInter
  intro i
  exact isClosed_le
    ((((continuous_apply i).comp continuous_fst).sub
      ((continuous_apply i).comp continuous_snd)).abs) continuous_const

theorem measurableSet_boundedDifference :
    MeasurableSet {p : RealSequences × RealSequences | BoundedDifference p.1 p.2} := by
  change MeasurableSet {p : RealSequences × RealSequences | ∃ n, UniformBound n p.1 p.2}
  simpa only [setOf_exists] using
    MeasurableSet.iUnion (fun n => (isClosed_uniformBound n).measurableSet)

theorem boundedDifference_iff_real_bound (x y : RealSequences) :
    BoundedDifference x y ↔ ∃ C : ℝ, ∀ i, |x i - y i| ≤ C := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hn⟩
  · rintro ⟨C, hC⟩
    obtain ⟨n, hn⟩ := exists_nat_ge C
    exact ⟨n, fun i => (hC i).trans hn⟩

def BoundedDifferenceJump : (ℕ → RealSequences) → (ℕ → RealSequences) → Prop :=
  Jump BoundedDifference

theorem boundedDifferenceJump_equivalence : Equivalence BoundedDifferenceJump :=
  jump_equivalence BoundedDifference boundedDifference_equivalence

theorem measurableSet_boundedDifferenceJump :
    MeasurableSet {p : (ℕ → RealSequences) × (ℕ → RealSequences) |
      BoundedDifferenceJump p.1 p.2} := by
  have hOne (k l : ℕ) : MeasurableSet
      {p : (ℕ → RealSequences) × (ℕ → RealSequences) |
        BoundedDifference (p.1 k) (p.2 l)} := by
    have hm : Measurable (fun p : (ℕ → RealSequences) × (ℕ → RealSequences) =>
        (p.1 k, p.2 l)) :=
      ((measurable_pi_apply k).comp measurable_fst).prodMk
        ((measurable_pi_apply l).comp measurable_snd)
    exact measurableSet_boundedDifference.preimage hm
  have hFwd : MeasurableSet
      {p : (ℕ → RealSequences) × (ℕ → RealSequences) |
        ∀ k, ∃ l, BoundedDifference (p.1 k) (p.2 l)} := by
    simpa only [setOf_forall, setOf_exists] using
      MeasurableSet.iInter (fun k => MeasurableSet.iUnion (hOne k))
  have hRev : MeasurableSet
      {p : (ℕ → RealSequences) × (ℕ → RealSequences) |
        ∀ l, ∃ k, BoundedDifference (p.1 k) (p.2 l)} := by
    simpa only [setOf_forall, setOf_exists] using
      MeasurableSet.iInter (fun l => MeasurableSet.iUnion (fun k => hOne k l))
  exact hFwd.inter hRev

#print axioms boundedDifference_equivalence
#print axioms isClosed_uniformBound
#print axioms measurableSet_boundedDifferenceJump

end BenchmarkJump
