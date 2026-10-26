import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Tactic

/-! The compact solenoid group and its real-sequence embedding from Section 8.
This file contains supporting lemmas, not the operator separation theorem. -/

open Filter Topology TopologicalSpace
open scoped Topology ENNReal

namespace MeasureEquivalenceSolenoid

noncomputable section

def characterGroup : AddSubgroup (ℚ → UnitAddCircle) where
  carrier := {f | f 0 = 0 ∧ ∀ q r, f (q+r) = f q + f r}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    constructor
    · simp [hf.1, hg.1]
    · intro q r
      simp only [Pi.add_apply, hf.2, hg.2]
      abel
  neg_mem' := by
    intro f hf
    constructor
    · simp [hf.1]
    · intro q r
      simp [hf.2, add_comm]

theorem characterGroup_closed : IsClosed (characterGroup : Set (ℚ → UnitAddCircle)) := by
  change IsClosed {f : ℚ → UnitAddCircle | f 0 = 0 ∧ ∀ q r, f (q+r) = f q + f r}
  simp only [Set.setOf_and, Set.setOf_forall]
  exact (isClosed_eq (continuous_apply 0) continuous_const).inter
    (isClosed_iInter fun q => isClosed_iInter fun r =>
      isClosed_eq (continuous_apply (q+r)) ((continuous_apply q).add (continuous_apply r)))

abbrev Solenoid := characterGroup
abbrev CompactSequences := ℕ → Solenoid

instance : CompactSpace Solenoid :=
  characterGroup_closed.isClosedEmbedding_subtypeVal.compactSpace
instance : PolishSpace Solenoid := characterGroup_closed.polishSpace
instance : MeasurableSpace Solenoid := borel Solenoid
instance : BorelSpace Solenoid := ⟨rfl⟩

def realCharacter (t : ℝ) : Solenoid :=
  ⟨fun q => ((q:ℝ)*t : ℝ), by
    constructor
    · simp
    · intro q r
      simp [add_mul]⟩

@[simp] theorem realCharacter_apply (t : ℝ) (q : ℚ) :
    (realCharacter t : ℚ → UnitAddCircle) q = ((q:ℝ)*t : ℝ) := rfl

theorem realCharacter_continuous : Continuous realCharacter := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro q
  exact (AddCircle.continuous_mk' (1:ℝ)).comp (continuous_const.mul continuous_id)

def realCharacterHom : ℝ →+ Solenoid where
  toFun := realCharacter
  map_zero' := by ext q; simp [realCharacter]
  map_add' := by intro x y; ext q; simp [realCharacter, mul_add]

theorem realCharacter_injective : Function.Injective realCharacter := by
  intro x y hxy
  by_contra hne
  have hd : x-y ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * |x-y|)
  have hn0 : (0:ℝ) < n := lt_of_le_of_lt (by positivity) hn
  have hnN : n ≠ 0 := by exact_mod_cast hn0.ne'
  let q : ℚ := 1 / n
  have hq : (q:ℝ) = 1/(n:ℝ) := by simp [q]
  have hc : ((((q:ℝ) * (x-y)):ℝ) : UnitAddCircle) = 0 := by
    have h := congrArg (fun f : Solenoid => (f:ℚ → UnitAddCircle) q) hxy
    simpa only [realCharacter_apply, mul_sub, AddCircle.coe_sub, sub_eq_zero] using h
  have habs : |(q:ℝ) * (x-y)| ≤ |(1:ℝ)| / 2 := by
    rw [hq, abs_mul, abs_one_div, abs_of_pos hn0, abs_one]
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ hn0).mpr
    nlinarith [abs_nonneg (x-y)]
  have hh := (AddCircle.norm_coe_eq_abs_iff (p := (1:ℝ)) (by norm_num)).mpr habs
  rw [hc, norm_zero] at hh
  have hz : (q:ℝ) * (x-y) = 0 := abs_eq_zero.mp hh.symm
  rcases mul_eq_zero.mp hz with hq0 | hd0
  · rw [hq] at hq0
    exact one_div_ne_zero (by exact_mod_cast hnN) hq0
  · exact hd hd0

def sequenceEmbedding : (ℕ → ℝ) →+ CompactSequences where
  toFun x n := realCharacter (x n)
  map_zero' := by ext n q; simp [realCharacter]
  map_add' := by intro x y; ext n q; simp [realCharacter, mul_add]

theorem sequenceEmbedding_continuous : Continuous sequenceEmbedding := by
  apply continuous_pi
  intro n
  exact realCharacter_continuous.comp (continuous_apply n)

theorem sequenceEmbedding_injective : Function.Injective sequenceEmbedding := by
  intro x y h
  funext n
  exact realCharacter_injective (congrFun h n)

example : CompactSpace CompactSequences := inferInstance
example : PolishSpace CompactSequences := inferInstance

abbrev RealL1 := lp (fun _ : ℕ => ℝ) 1

def zeroSumSpace : Submodule ℝ RealL1 := (lp.tsumCLM ℝ ℕ ℝ).ker

@[simp] theorem mem_zeroSumSpace (h : RealL1) :
    h ∈ zeroSumSpace ↔ (∑' n, h n) = 0 := by
  rfl

theorem zeroSumSpace_closed : IsClosed (zeroSumSpace : Set RealL1) :=
  (lp.tsumCLM ℝ ℕ ℝ).isClosed_ker

instance : CompleteSpace zeroSumSpace :=
  zeroSumSpace_closed.isComplete.completeSpace_coe

def l1Embedding : RealL1 →+ CompactSequences where
  toFun h := sequenceEmbedding (h : ℕ → ℝ)
  map_zero' := map_zero sequenceEmbedding
  map_add' := by intro h k; exact map_add sequenceEmbedding (h:ℕ→ℝ) (k:ℕ→ℝ)

theorem l1Embedding_continuous : Continuous l1Embedding := by
  apply sequenceEmbedding_continuous.comp
  apply continuous_pi
  intro n
  exact (lp.lipschitzWith_one_eval (E := fun _ : ℕ => ℝ) (1:ℝ≥0∞) n).continuous

theorem l1Embedding_injective : Function.Injective l1Embedding := by
  intro x y h
  apply lp.ext
  exact sequenceEmbedding_injective h

def summableSubgroup : AddSubgroup CompactSequences := l1Embedding.range
def zeroSumSubgroup : AddSubgroup CompactSequences :=
  zeroSumSpace.toAddSubgroup.map l1Embedding

theorem zeroSumSubgroup_le : zeroSumSubgroup ≤ summableSubgroup := by
  rintro x ⟨h, _hh, rfl⟩
  exact ⟨h, rfl⟩

@[simp] theorem l1Embedding_mem_zeroSumSubgroup (h : RealL1) :
    l1Embedding h ∈ zeroSumSubgroup ↔ (∑' n, h n) = 0 := by
  constructor
  · rintro ⟨u, hu, he⟩
    have : u = h := l1Embedding_injective he
    simpa [this] using hu
  · intro hh
    exact ⟨h, (mem_zeroSumSpace h).mpr hh, rfl⟩

def coordinateShift (a : ℝ) : CompactSequences := l1Embedding (lp.single 1 0 a)

theorem coordinateShift_mem_summable (a : ℝ) :
    coordinateShift a ∈ summableSubgroup := ⟨_, rfl⟩

@[simp] theorem coordinateShift_mem_zeroSum (a : ℝ) :
    coordinateShift a ∈ zeroSumSubgroup ↔ a = 0 := by
  rw [coordinateShift, l1Embedding_mem_zeroSumSubgroup]
  simp

theorem zeroSumSubgroup_ne_summable : zeroSumSubgroup ≠ summableSubgroup := by
  intro h
  have hm := coordinateShift_mem_summable 1
  rw [← h, coordinateShift_mem_zeroSum] at hm
  norm_num at hm

def twoPoint (a : ℝ) (n : ℕ) : RealL1 :=
  lp.single 1 0 a - lp.single 1 (n+1) a

theorem twoPoint_zeroSum (a : ℝ) (n : ℕ) : twoPoint a n ∈ zeroSumSpace := by
  change (lp.tsumCLM ℝ ℕ ℝ) (twoPoint a n) = 0
  rw [twoPoint, map_sub]
  simp [lp.tsumCLM_apply]

theorem twoPoint_norm_le (a : ℝ) (n : ℕ) : ‖twoPoint a n‖ ≤ 2 * |a| := by
  calc
    ‖twoPoint a n‖ ≤ ‖(lp.single 1 0 a : RealL1)‖ + ‖(lp.single 1 (n+1) a : RealL1)‖ := norm_sub_le _ _
    _ = 2 * |a| := by simp [lp.norm_single]; ring

theorem twoPoint_limit (a : ℝ) :
    Tendsto (fun n => l1Embedding (twoPoint a n)) atTop (𝓝 (coordinateShift a)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop i] with n hn
  have hi : i ≠ n+1 := by omega
  change realCharacter ((lp.single 1 0 a : RealL1) i) = realCharacter ((twoPoint a n) i)
  congr 1
  change (lp.single 1 0 a : RealL1) i =
    (lp.single 1 0 a : RealL1) i - (lp.single 1 (n+1) a : RealL1) i
  have hz : (lp.single 1 (n+1) a : RealL1) i = 0 :=
    lp.single_apply_ne (E := fun _ : ℕ => ℝ) 1 (n+1) a hi
  rw [hz, sub_zero]

theorem decompose_l1 (h : RealL1) :
    ∃ z ∈ zeroSumSubgroup, l1Embedding h = z + coordinateShift (∑' n, h n) := by
  let a := (lp.tsumCLM ℝ ℕ ℝ) h
  let u : RealL1 := h - lp.single 1 0 a
  have hu : u ∈ zeroSumSpace := by
    change (lp.tsumCLM ℝ ℕ ℝ) u = 0
    dsimp only [u]
    rw [map_sub]
    have hs : (lp.tsumCLM ℝ ℕ ℝ) (lp.single 1 0 a) = a := by
      simp [lp.tsumCLM_apply]
    rw [hs]
    exact sub_self a
  refine ⟨l1Embedding u, ⟨u, hu, rfl⟩, ?_⟩
  change l1Embedding h = l1Embedding (h - lp.single 1 0 a) + l1Embedding (lp.single 1 0 a)
  rw [← map_add, sub_add_cancel]

def finiteTruncation (s : Finset ℕ) (x : ℕ → ℝ) : RealL1 :=
  ∑ i ∈ s, lp.single 1 i (x i)

theorem finiteTruncation_continuous (s : Finset ℕ) : Continuous (finiteTruncation s) := by
  apply continuous_finsetSum
  intro i _hi
  exact (lp.singleContinuousAddMonoidHom (fun _ : ℕ => ℝ) 1 i).continuous.comp
    (continuous_apply i)

theorem realL1_separable : SeparableSpace RealL1 := by
  have hd : Dense (⋃ s : Finset ℕ, Set.range (finiteTruncation s)) := by
    intro x
    apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num : (1:ℝ≥0∞) ≠ ⊤) x)
    exact Filter.Eventually.of_forall (fun s => Set.mem_iUnion.mpr ⟨s, ⟨(x:ℕ→ℝ), rfl⟩⟩)
  apply hd.isSeparable_iff.mp
  exact IsSeparable.iUnion (fun s => isSeparable_range (finiteTruncation_continuous s))

instance : PolishSpace RealL1 := by
  letI := realL1_separable
  infer_instance

instance : PolishSpace zeroSumSpace := zeroSumSpace_closed.polishSpace

theorem summableSubgroup_borel : MeasurableSet (summableSubgroup : Set CompactSequences) := by
  exact MeasureTheory.measurableSet_range_of_continuous_injective
    l1Embedding_continuous l1Embedding_injective

theorem zeroSumSubgroup_borel : MeasurableSet (zeroSumSubgroup : Set CompactSequences) := by
  have hc : Continuous (fun h : zeroSumSpace => l1Embedding (h:RealL1)) :=
    l1Embedding_continuous.comp continuous_subtype_val
  have hi : Function.Injective (fun h : zeroSumSpace => l1Embedding (h:RealL1)) :=
    fun _ _ h => Subtype.ext (l1Embedding_injective h)
  have he : (zeroSumSubgroup : Set CompactSequences) =
      Set.range (fun h : zeroSumSpace => l1Embedding (h:RealL1)) := by
    ext x
    constructor
    · rintro ⟨u, hu, hx⟩
      exact ⟨⟨u, hu⟩, hx⟩
    · rintro ⟨⟨u, hu⟩, hx⟩
      exact ⟨u, hu, hx⟩
  rw [he]
  exact MeasureTheory.measurableSet_range_of_continuous_injective hc hi

#print axioms realCharacter_injective
#print axioms sequenceEmbedding_injective
#print axioms sequenceEmbedding_continuous
#print axioms zeroSumSubgroup_ne_summable
#print axioms twoPoint_limit
#print axioms decompose_l1
#print axioms zeroSumSubgroup_borel

end
end MeasureEquivalenceSolenoid
