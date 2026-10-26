import RootContinuity
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Topology.Instances.Rat
import Mathlib.Data.Finsupp.Encodable

/-! A countable dense subgroup of the intrinsic zero-sum l1 group. -/

open Filter Topology TopologicalSpace Set
open scoped Topology ENNReal

namespace MeasureEquivalenceSolenoid

noncomputable section

def rationalFinite : (ℕ →₀ ℚ) →+ RealL1 :=
  Finsupp.liftAddHom (fun i =>
    (lp.singleAddMonoidHom (E := fun _ : ℕ => ℝ) 1 i).comp
      (Rat.castHom ℝ).toAddMonoidHom)

@[simp] theorem rationalFinite_single (i : ℕ) (q : ℚ) :
    rationalFinite (Finsupp.single i q) = lp.single 1 i (q:ℝ) := by
  exact Finsupp.liftAddHom_apply_single _ _ _

theorem rationalFinite_dense : DenseRange rationalFinite := by
  let R := rationalFinite.range
  have hs (i : ℕ) (a : ℝ) : lp.single 1 i a ∈ R.topologicalClosure := by
    have ha : a ∈ closure (range (fun q : ℚ => (q:ℝ))) := Rat.denseRange_cast a
    have hi : Continuous (fun a : ℝ => (lp.single 1 i a : RealL1)) :=
      (lp.singleContinuousAddMonoidHom (fun _ : ℕ => ℝ) 1 i).continuous
    have hm := mem_closure_image (hi.continuousAt : ContinuousAt
      (fun a : ℝ => (lp.single 1 i a : RealL1)) a) ha
    apply closure_mono (s := (fun a : ℝ => (lp.single 1 i a : RealL1)) ''
      range (fun q : ℚ => (q:ℝ))) (t := (R:Set RealL1)) _ hm
    rintro _ ⟨a, ⟨q, rfl⟩, rfl⟩
    exact ⟨Finsupp.single i q, rationalFinite_single i q⟩
  intro x
  change x ∈ R.topologicalClosure
  apply R.isClosed_topologicalClosure.mem_of_tendsto
    (lp.hasSum_single (by norm_num : (1:ℝ≥0∞) ≠ ⊤) x)
  exact Filter.Eventually.of_forall (fun s =>
    R.topologicalClosure.sum_mem (fun i _hi => hs i (x i)))

def zeroSumProjection : RealL1 →+ zeroSumSpace where
  toFun h := ⟨h - lp.single 1 0 ((lp.tsumCLM ℝ ℕ ℝ) h), by
    change (lp.tsumCLM ℝ ℕ ℝ) (h - lp.single 1 0 ((lp.tsumCLM ℝ ℕ ℝ) h)) = 0
    rw [map_sub]
    have hs (a : ℝ) : (lp.tsumCLM ℝ ℕ ℝ) (lp.single 1 0 a) = a := by
      simp [lp.tsumCLM_apply]
    rw [hs, sub_self]⟩
  map_zero' := by
    apply Subtype.ext
    change (0:RealL1) - lp.single 1 0 ((lp.tsumCLM ℝ ℕ ℝ) 0) = 0
    rw [map_zero, lp.single_zero, sub_zero]
  map_add' := by
    intro h k
    apply Subtype.ext
    simp only [map_add, lp.single_add, Submodule.coe_add]
    abel

theorem zeroSumProjection_continuous : Continuous zeroSumProjection := by
  apply Continuous.subtype_mk
  exact continuous_id.sub
    ((lp.singleContinuousAddMonoidHom (fun _ : ℕ => ℝ) 1 0).continuous.comp
      (lp.tsumCLM ℝ ℕ ℝ).continuous)

theorem zeroSumProjection_surjective : Function.Surjective zeroSumProjection := by
  intro h
  refine ⟨h, Subtype.ext ?_⟩
  have hh : (lp.tsumCLM ℝ ℕ ℝ) (h:RealL1) = 0 := h.property
  change (h:RealL1) - lp.single 1 0 ((lp.tsumCLM ℝ ℕ ℝ) (h:RealL1)) = (h:RealL1)
  rw [hh]
  simp

def rationalZeroSum : (ℕ →₀ ℚ) →+ zeroSumSpace := zeroSumProjection.comp rationalFinite

theorem rationalZeroSum_dense : DenseRange rationalZeroSum :=
  zeroSumProjection_surjective.denseRange.comp rationalFinite_dense zeroSumProjection_continuous

def denseRationalSubgroup : AddSubgroup zeroSumSpace := rationalZeroSum.range

theorem denseRationalSubgroup_countable : (denseRationalSubgroup:Set zeroSumSpace).Countable :=
  Set.countable_range rationalZeroSum

theorem denseRationalSubgroup_dense : Dense (denseRationalSubgroup:Set zeroSumSpace) :=
  rationalZeroSum_dense

def compactRationalSubgroup : AddSubgroup CompactSequences :=
  denseRationalSubgroup.map MeasureEquivalenceRootContinuity.zeroSumInclusion

end
end MeasureEquivalenceSolenoid

#print axioms MeasureEquivalenceSolenoid.rationalFinite_dense
#print axioms MeasureEquivalenceSolenoid.rationalZeroSum_dense
