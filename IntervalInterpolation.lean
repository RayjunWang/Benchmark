import CircleChart
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Algebra.ConstMulAction

open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

def affineMix (q : ℝ) (p : ℝ × ℝ) : ℝ := (1 - q) * p.1 + q * p.2

theorem continuous_affineMix (q : ℝ) : Continuous (affineMix q) := by
  unfold affineMix
  fun_prop

theorem isOpenMap_affineMix (q : ℝ) : IsOpenMap (affineMix q) := by
  by_cases hq : q = 1
  · subst q
    have heq : affineMix 1 = (@Prod.snd ℝ ℝ) := by
      funext p
      unfold affineMix
      ring
    rw [heq]
    exact isOpenMap_snd
  have hne : (1 - q : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  intro W hW
  have heq : affineMix q '' W = ⋃ y : ℝ,
      (fun x : ℝ => (1 - q) * x + q * y) '' {x | (x, y) ∈ W} := by
    ext z
    constructor
    · rintro ⟨⟨x, y⟩, hxy, rfl⟩
      exact mem_iUnion.mpr ⟨y, x, hxy, rfl⟩
    · intro hz
      obtain ⟨y, x, hxy, hxz⟩ := mem_iUnion.mp hz
      exact ⟨(x, y), hxy, hxz⟩
  rw [heq]
  apply isOpen_iUnion
  intro y
  have hmul : IsOpenMap (fun x : ℝ => (1 - q) * x) := isOpenMap_smul₀ hne
  exact ((isOpenMap_add_right (q * y)).comp hmul) _
    (hW.preimage (continuous_id.prodMk continuous_const))

def intervalMix (a b q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (p : Set.Ioo a b × Set.Ioo a b) : Set.Ioo a b :=
  ⟨affineMix q (p.1, p.2), by
    simpa only [affineMix, smul_eq_mul] using
      (convex_Ioo a b) p.1.property p.2.property
        (sub_nonneg.mpr hq1) hq0 (by ring : 1 - q + q = 1)⟩

theorem continuous_intervalMix (a b q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Continuous (intervalMix a b q hq0 hq1) :=
  ((continuous_affineMix q).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _

theorem isOpenMap_intervalMix (a b q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsOpenMap (intervalMix a b q hq0 hq1) := by
  have hInc : IsOpenMap
      (fun p : Set.Ioo a b × Set.Ioo a b => ((p.1 : ℝ), (p.2 : ℝ))) :=
    isOpen_Ioo.isOpenMap_subtype_val.prodMap isOpen_Ioo.isOpenMap_subtype_val
  exact ((isOpenMap_affineMix q).comp hInc).subtype_mk _

theorem intervalMix_surjective (a b q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Function.Surjective (intervalMix a b q hq0 hq1) := by
  intro x
  refine ⟨(x, x), ?_⟩
  apply Subtype.ext
  change (1 - q) * (x : ℝ) + q * (x : ℝ) = (x : ℝ)
  ring

abbrev IntervalBox (a b : ℕ → ℝ) := ∀ i, Set.Ioo (a i) (b i)

def boxPairHomeomorph (a b : ℕ → ℝ) :
    (IntervalBox a b × IntervalBox a b) ≃ₜ
      (∀ i, Set.Ioo (a i) (b i) × Set.Ioo (a i) (b i)) where
  toFun p i := (p.1 i, p.2 i)
  invFun p := (fun i => (p i).1, fun i => (p i).2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun i =>
    ((continuous_apply i).comp continuous_fst).prodMk
      ((continuous_apply i).comp continuous_snd)
  continuous_invFun :=
    (continuous_pi fun i => continuous_fst.comp (continuous_apply i)).prodMk
      (continuous_pi fun i => continuous_snd.comp (continuous_apply i))

def boxMix (a b : ℕ → ℝ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (p : IntervalBox a b × IntervalBox a b) : IntervalBox a b :=
  fun i => intervalMix (a i) (b i) q hq0 hq1 (p.1 i, p.2 i)

theorem continuous_boxMix (a b : ℕ → ℝ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Continuous (boxMix a b q hq0 hq1) :=
  (continuous_pi fun i => (continuous_intervalMix (a i) (b i) q hq0 hq1).comp
    (((continuous_apply i).comp continuous_fst).prodMk
      ((continuous_apply i).comp continuous_snd)))

theorem isOpenMap_boxMix (a b : ℕ → ℝ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsOpenMap (boxMix a b q hq0 hq1) :=
  (IsOpenMap.piMap
    (fun i => isOpenMap_intervalMix (a i) (b i) q hq0 hq1)
    (Eventually.of_forall fun i => intervalMix_surjective (a i) (b i) q hq0 hq1)).comp
      (boxPairHomeomorph a b).isOpenMap

theorem affineMix_difference (x y q r : ℝ) :
    |affineMix q (x, y) - affineMix r (x, y)| = |q - r| * |y - x| := by
  have heq : affineMix q (x, y) - affineMix r (x, y) = (q - r) * (y - x) := by
    unfold affineMix
    ring
  rw [heq, abs_mul]

/-- The uniform coordinate estimate for interpolation in a bounded chart. -/
theorem circle_affineMix_bound (x y q r : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    ‖(affineMix q (x, y) : UnitAddCircle) -
      (affineMix r (x, y) : UnitAddCircle)‖ ≤ |q - r| := by
  have hxy : |y - x| ≤ (1 : ℝ) := abs_le.mpr ⟨by linarith [hy.1, hx.2],
    by linarith [hy.2, hx.1]⟩
  calc
    _ = ‖((affineMix q (x, y) - affineMix r (x, y) : ℝ) : UnitAddCircle)‖ := by
      rw [AddCircle.coe_sub]
    _ ≤ |affineMix q (x, y) - affineMix r (x, y)| := by
      simpa only [Real.norm_eq_abs] using
        (QuotientAddGroup.norm_mk_le_norm
          (m := affineMix q (x, y) - affineMix r (x, y))
          (S := AddSubgroup.zmultiples (1 : ℝ)))
    _ = |q - r| * |y - x| := affineMix_difference x y q r
    _ ≤ |q - r| * 1 := mul_le_mul_of_nonneg_left hxy (abs_nonneg _)
    _ = |q - r| := mul_one _

#print axioms isOpenMap_boxMix
#print axioms circle_affineMix_bound

end BenchmarkJump
