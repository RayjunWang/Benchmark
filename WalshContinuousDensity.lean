import ShiftWalshCharacters
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! Finite linear combinations of Walsh characters are uniformly dense in
the continuous real-valued functions on the full binary shift. -/

open Set
open scoped Topology symmDiff

noncomputable section

namespace BenchmarkShift

local instance : DecidableEq Group := Classical.decEq Group

def continuousWalsh (S : Finset Group) : C(Point, ℝ) := ⟨walsh S, continuous_walsh S⟩

lemma continuousWalsh_empty : continuousWalsh ∅ = 1 := by ext x; simp [continuousWalsh, walsh]

lemma continuousWalsh_mul (S T : Finset Group) :
    continuousWalsh S * continuousWalsh T = continuousWalsh (S ∆ T) := by
  ext x
  exact walsh_mul S T x

def walshSubmonoid : Submonoid C(Point, ℝ) where
  carrier := Set.range continuousWalsh
  one_mem' := ⟨∅, continuousWalsh_empty⟩
  mul_mem' := by
    rintro a b ⟨S, rfl⟩ ⟨T, rfl⟩
    exact ⟨S ∆ T, (continuousWalsh_mul S T).symm⟩

def walshAlgebra : Subalgebra ℝ C(Point, ℝ) := Algebra.adjoin ℝ (Set.range continuousWalsh)

lemma walshAlgebra_toSubmodule : walshAlgebra.toSubmodule =
    Submodule.span ℝ (Set.range continuousWalsh) := by
  unfold walshAlgebra
  rw [Algebra.adjoin_eq_span]
  change Submodule.span ℝ (Submonoid.closure (walshSubmonoid : Set C(Point, ℝ)) : Set C(Point, ℝ)) = _
  rw [walshSubmonoid.closure_eq]
  rfl

lemma coinSign_injective : Function.Injective coinSign := by
  intro a b h
  cases a <;> cases b <;> first | rfl | norm_num [coinSign] at h

lemma walshAlgebra_separatesPoints : walshAlgebra.SeparatesPoints := by
  intro x y hxy
  have hex : ∃ g : Group, x g ≠ y g := by
    by_contra h
    push Not at h
    exact hxy (funext h)
  obtain ⟨g, hg⟩ := hex
  refine ⟨walsh {g}, ⟨continuousWalsh {g}, Algebra.subset_adjoin ⟨{g}, rfl⟩, rfl⟩, ?_⟩
  intro heq
  apply hg
  apply coinSign_injective
  simpa only [walsh, Finset.prod_singleton] using heq

theorem dense_continuous_walsh_span :
    Dense (Submodule.span ℝ (Set.range continuousWalsh) : Set C(Point, ℝ)) := by
  have hclosure := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    walshAlgebra walshAlgebra_separatesPoints
  have hdense : Dense (walshAlgebra : Set C(Point, ℝ)) := by
    rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe, hclosure]
    rfl
  have hset : (walshAlgebra : Set C(Point, ℝ)) =
      (Submodule.span ℝ (Set.range continuousWalsh) : Set C(Point, ℝ)) := by
    rw [← walshAlgebra_toSubmodule]
    rfl
  rwa [← hset]

end BenchmarkShift

#print axioms BenchmarkShift.dense_continuous_walsh_span
