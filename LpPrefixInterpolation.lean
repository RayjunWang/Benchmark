import LpCountableAction
import IntervalInterpolation

/-! Open finite-prefix affine interpolation in the product of real lines. -/

open Filter Set Topology TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace BenchmarkCountableReverse

open BenchmarkJump

def realPairHomeomorph : (RealSequences × RealSequences) ≃ₜ (ℕ → ℝ × ℝ) where
  toFun q i := (q.1 i, q.2 i)
  invFun q := (fun i => (q i).1, fun i => (q i).2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun i =>
    ((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd)
  continuous_invFun := (continuous_pi fun i => continuous_fst.comp (continuous_apply i)).prodMk
    (continuous_pi fun i => continuous_snd.comp (continuous_apply i))

def prefixMix (N : ℕ) (q : ℝ) (z : RealSequences × RealSequences) : RealSequences :=
  fun i => affineMix (if i < N then q else 0) (z.1 i, z.2 i)

lemma continuous_prefixMix (N : ℕ) (q : ℝ) : Continuous (prefixMix N q) :=
  continuous_pi fun i => (continuous_affineMix _).comp
    (((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd))

lemma isOpenMap_prefixMix (N : ℕ) (q : ℝ) : IsOpenMap (prefixMix N q) := by
  have hs (i : ℕ) : Function.Surjective (affineMix (if i < N then q else 0)) := by
    intro x
    refine ⟨(x, x), ?_⟩
    unfold affineMix
    ring
  exact (IsOpenMap.piMap (fun i => isOpenMap_affineMix _)
    (Eventually.of_forall hs)).comp realPairHomeomorph.isOpenMap

def PrefixConvex (C : Set RealSequences) : Prop :=
  ∀ N q, 0 ≤ q → q ≤ 1 → ∀ x ∈ C, ∀ y ∈ C, prefixMix N q (x, y) ∈ C

theorem exists_open_prefixConvex_subset (V : Set RealSequences)
    (hVo : IsOpen V) (hVn : V.Nonempty) :
    ∃ C : Set RealSequences, IsOpen C ∧ C.Nonempty ∧ C ⊆ V ∧ PrefixConvex C := by
  classical
  obtain ⟨x, hx⟩ := hVn
  obtain ⟨I, U, hU, hUV⟩ := isOpen_pi_iff.mp hVo x hx
  have hB (i : ℕ) (hi : i ∈ I) :
      ∃ ε > (0 : ℝ), Metric.ball (x i) ε ⊆ U i :=
    Metric.isOpen_iff.mp (hU i hi).1 (x i) (hU i hi).2
  choose ε hεpos hεsub using hB
  let r : ℕ → ℝ := fun i => if hi : i ∈ I then ε i hi else 1
  let C : Set RealSequences := (I : Set ℕ).pi fun i => Metric.ball (x i) (r i)
  have hCr (i : ℕ) (hi : i ∈ I) : 0 < r i := by simpa [r, hi] using hεpos i hi
  refine ⟨C, isOpen_set_pi I.finite_toSet (fun _ _ => Metric.isOpen_ball), ?_, ?_, ?_⟩
  · exact ⟨x, fun i hi => Metric.mem_ball_self (hCr i hi)⟩
  · intro y hy
    apply hUV
    intro i hi
    change i ∈ I at hi
    apply hεsub i hi
    simpa [r, hi] using hy i hi
  · intro N q hq0 hq1 y hy z hz i hi
    by_cases hin : i < N
    · have hyD : |y i - x i| < r i := hy i hi
      have hzD : |z i - x i| < r i := hz i hi
      have hyR : y i ∈ Ioo (x i - r i) (x i + r i) :=
        ⟨by linarith [(abs_lt.mp hyD).1], by linarith [(abs_lt.mp hyD).2]⟩
      have hzR : z i ∈ Ioo (x i - r i) (x i + r i) :=
        ⟨by linarith [(abs_lt.mp hzD).1], by linarith [(abs_lt.mp hzD).2]⟩
      have hm := (convex_Ioo (x i - r i) (x i + r i)) hyR hzR
        (sub_nonneg.mpr hq1) hq0 (by ring : 1 - q + q = 1)
      change x i - r i < affineMix q (y i, z i) ∧ affineMix q (y i, z i) < x i + r i at hm
      change |prefixMix N q (y, z) i - x i| < r i
      simp only [prefixMix, if_pos hin]
      apply abs_lt.mpr
      constructor <;> linarith [hm.1, hm.2]
    · simpa [prefixMix, hin, affineMix] using hy i hi

def prefixMixOn (C : Set RealSequences) (hC : PrefixConvex C)
    (N : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (z : C × C) : C :=
  ⟨prefixMix N q (z.1, z.2), hC N q hq0 hq1 z.1 z.1.property z.2 z.2.property⟩

lemma continuous_prefixMixOn (C : Set RealSequences) (hC : PrefixConvex C)
    (N : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Continuous (prefixMixOn C hC N q hq0 hq1) :=
  ((continuous_prefixMix N q).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _

lemma isOpenMap_prefixMixOn (C : Set RealSequences) (hCo : IsOpen C) (hC : PrefixConvex C)
    (N : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsOpenMap (prefixMixOn C hC N q hq0 hq1) :=
  ((isOpenMap_prefixMix N q).comp
    (hCo.isOpenMap_subtype_val.prodMap hCo.isOpenMap_subtype_val)).subtype_mk _

def prefixVector (p : ℝ≥0∞) (N : ℕ) (x : RealSequences) : Translations p :=
  ∑ i ∈ Finset.range N, lp.single p i (x i)

lemma prefixVector_apply (p : ℝ≥0∞) (N : ℕ) (x : RealSequences) (i : ℕ) :
    prefixVector p N x i = if i < N then x i else 0 := by
  simp only [prefixVector, lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply,
    Finset.sum_pi_single, Finset.mem_range]

lemma prefixMix_add_vector (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (N : ℕ) (q r : ℝ) (x y : RealSequences) :
    prefixMix N q (x, y) = prefixMix N r (x, y) +
      coordinates p ((q - r) • prefixVector p N (y - x)) := by
  funext i
  change affineMix (if i < N then q else 0) (x i, y i) =
    affineMix (if i < N then r else 0) (x i, y i) +
      ((q - r) • prefixVector p N (y - x)) i
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, prefixVector_apply]
  by_cases hi : i < N <;> simp only [hi, ite_true, ite_false, Pi.sub_apply, affineMix] <;> ring

lemma prefixMix_zero (N : ℕ) (x y : RealSequences) : prefixMix N 0 (x, y) = x := by
  funext i
  simp [prefixMix, affineMix]

lemma tendsto_prefixMix_one (x y : RealSequences) :
    Tendsto (fun N : ℕ => prefixMix N 1 (x, y)) atTop (𝓝 y) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop i] with N hN
  simp [prefixMix, hN, affineMix]

end BenchmarkCountableReverse

#print axioms BenchmarkCountableReverse.exists_open_prefixConvex_subset
#print axioms BenchmarkCountableReverse.prefixMix_add_vector
