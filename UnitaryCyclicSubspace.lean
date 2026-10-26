import OperatorCyclicRepresentation
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! The actual closed cyclic subspace of one unitary and its reducing
restriction. These are the first structural ingredients for the remaining
spectral-multiplicity classification, which is not asserted here. -/

open Set
open scoped InnerProductSpace

set_option maxHeartbeats 800000

namespace OperatorCoding

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def cyclicSpan (U : StrongUnitary H) (v : H) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range (fun n : ℤ => (U ^ n) v))).topologicalClosure

theorem cyclicSpan_isClosed (U : StrongUnitary H) (v : H) :
    IsClosed (cyclicSpan U v : Set H) :=
  Submodule.isClosed_topologicalClosure _

theorem cyclicSpan_contains_orbit (U : StrongUnitary H) (v : H) (n : ℤ) :
    (U ^ n) v ∈ cyclicSpan U v :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (mem_range_self n))

theorem cyclicSpan_contains_generator (U : StrongUnitary H) (v : H) :
    v ∈ cyclicSpan U v := by
  simpa using cyclicSpan_contains_orbit U v 0

theorem cyclicSpan_minimal (U : StrongUnitary H) (v : H) (P : Submodule ℂ H)
    (hclosed : IsClosed (P : Set H)) (hcontains : ∀ n : ℤ, (U ^ n) v ∈ P) :
    cyclicSpan U v ≤ P :=
  Submodule.topologicalClosure_minimal _
    (Submodule.span_le.mpr (by rintro _ ⟨n,rfl⟩; exact hcontains n)) hclosed

theorem cyclicSpan_zpow_invariant (U : StrongUnitary H) (v : H) (m : ℤ)
    (x : H) (hx : x ∈ cyclicSpan U v) : (U ^ m) x ∈ cyclicSpan U v := by
  let P := Submodule.span ℂ (Set.range (fun n : ℤ => (U ^ n) v))
  have hspan : Set.MapsTo (U ^ m) (P : Set H) (P : Set H) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨n,rfl⟩ := hy
      apply Submodule.subset_span
      refine ⟨m+n, ?_⟩
      change (U ^ (m+n)) v = (U ^ m) ((U ^ n) v)
      rw [zpow_add]
      rfl
    | zero => simpa only [map_zero] using P.zero_mem
    | add y z hy hz ihy ihz =>
      simpa only [map_add] using P.add_mem ihy ihz
    | smul a y hy ih =>
      simpa only [map_smul] using P.smul_mem a ih
  exact hspan.closure (U ^ m).continuous hx

def cyclicRestriction (U : StrongUnitary H) (v : H) :
    StrongUnitary (cyclicSpan U v) where
  toFun x := ⟨U x, by simpa only [zpow_one] using cyclicSpan_zpow_invariant U v 1 x x.property⟩
  invFun x := ⟨U.symm x, by
    simpa only [zpow_neg_one] using cyclicSpan_zpow_invariant U v (-1) x x.property⟩
  left_inv x := Subtype.ext (U.symm_apply_apply x)
  right_inv x := Subtype.ext (U.apply_symm_apply x)
  map_add' x y := Subtype.ext (U.map_add x y)
  map_smul' a x := Subtype.ext (U.map_smul a x)
  norm_map' x := U.norm_map x

theorem cyclicSpan_orthogonal_zpow_invariant (U : StrongUnitary H) (v : H) (m : ℤ)
    (x : H) (hx : x ∈ (cyclicSpan U v)ᗮ) : (U ^ m) x ∈ (cyclicSpan U v)ᗮ := by
  intro w hw
  have hw' : (U ^ m).symm w ∈ cyclicSpan U v := by
    simpa only [zpow_neg] using cyclicSpan_zpow_invariant U v (-m) w hw
  have hinner : inner ℂ w ((U ^ m) x) = inner ℂ ((U ^ m).symm w) x := by
    simpa only [LinearIsometryEquiv.apply_symm_apply] using
      (U ^ m).inner_map_map ((U ^ m).symm w) x
  exact hinner.trans (hx _ hw')

end
end OperatorCoding

#print axioms OperatorCoding.cyclicRestriction
#print axioms OperatorCoding.cyclicSpan_orthogonal_zpow_invariant
