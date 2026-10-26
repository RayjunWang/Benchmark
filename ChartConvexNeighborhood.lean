import IntervalInterpolation

open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

def chartMix (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (p : CircleChartSpace × CircleChartSpace) : CircleChartSpace :=
  boxMix (fun _ => 0) (fun _ => 1) q hq0 hq1 p

theorem continuous_chartMix (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Continuous (chartMix q hq0 hq1) :=
  continuous_boxMix (fun _ => 0) (fun _ => 1) q hq0 hq1

theorem isOpenMap_chartMix (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsOpenMap (chartMix q hq0 hq1) :=
  isOpenMap_boxMix (fun _ => 0) (fun _ => 1) q hq0 hq1

def ChartConvex (C : Set CircleChartSpace) : Prop :=
  ∀ q (hq0 : 0 ≤ q) (hq1 : q ≤ 1), ∀ x ∈ C, ∀ y ∈ C,
    chartMix q hq0 hq1 (x, y) ∈ C

/-- Every nonempty open set in the product chart contains a nonempty open
cylinder preserved by all coordinatewise affine interpolations. -/
theorem exists_open_chartConvex_subset (V : Set CircleChartSpace)
    (hVo : IsOpen V) (hVn : V.Nonempty) :
    ∃ C : Set CircleChartSpace, IsOpen C ∧ C.Nonempty ∧ C ⊆ V ∧ ChartConvex C := by
  classical
  obtain ⟨x, hx⟩ := hVn
  obtain ⟨I, U, hU, hUV⟩ := isOpen_pi_iff.mp hVo x hx
  have hB (i : ℕ) (hi : i ∈ I) :
      ∃ ε > (0 : ℝ), Metric.ball (x i) ε ⊆ U i :=
    Metric.isOpen_iff.mp (hU i hi).1 (x i) (hU i hi).2
  choose ε hεpos hεsub using hB
  let r : ℕ → ℝ := fun i => if hi : i ∈ I then ε i hi else 1
  let C : Set CircleChartSpace := (I : Set ℕ).pi fun i => Metric.ball (x i) (r i)
  have hCr (i : ℕ) (hi : i ∈ I) : 0 < r i := by
    simpa [r, hi] using hεpos i hi
  refine ⟨C, isOpen_set_pi I.finite_toSet (fun _ _ => Metric.isOpen_ball), ?_, ?_, ?_⟩
  · refine ⟨x, ?_⟩
    intro i hi
    exact Metric.mem_ball_self (hCr i hi)
  · intro y hy
    apply hUV
    intro i hi
    change i ∈ I at hi
    apply hεsub i hi
    simpa [r, hi] using hy i hi
  · intro q hq0 hq1 y hy z hz
    intro i hi
    have hyD : |(y i : ℝ) - (x i : ℝ)| < r i := hy i hi
    have hzD : |(z i : ℝ) - (x i : ℝ)| < r i := hz i hi
    have hyR : (y i : ℝ) ∈ Set.Ioo ((x i : ℝ) - r i) ((x i : ℝ) + r i) :=
      ⟨by linarith [(abs_lt.mp hyD).1], by linarith [(abs_lt.mp hyD).2]⟩
    have hzR : (z i : ℝ) ∈ Set.Ioo ((x i : ℝ) - r i) ((x i : ℝ) + r i) :=
      ⟨by linarith [(abs_lt.mp hzD).1], by linarith [(abs_lt.mp hzD).2]⟩
    have hmix := (convex_Ioo ((x i : ℝ) - r i) ((x i : ℝ) + r i)) hyR hzR
      (sub_nonneg.mpr hq1) hq0 (by ring : 1 - q + q = 1)
    change (x i : ℝ) - r i < affineMix q ((y i : ℝ), (z i : ℝ)) ∧
      affineMix q ((y i : ℝ), (z i : ℝ)) < (x i : ℝ) + r i at hmix
    change |affineMix q ((y i : ℝ), (z i : ℝ)) - (x i : ℝ)| < r i
    apply abs_lt.mpr
    constructor <;> linarith [hmix.1, hmix.2]

def chartMixOn (C : Set CircleChartSpace) (hC : ChartConvex C)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (p : C × C) : C :=
  ⟨chartMix q hq0 hq1 (p.1, p.2), hC q hq0 hq1 p.1 p.1.property p.2 p.2.property⟩

theorem continuous_chartMixOn (C : Set CircleChartSpace) (hC : ChartConvex C)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Continuous (chartMixOn C hC q hq0 hq1) :=
  ((continuous_chartMix q hq0 hq1).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _

theorem isOpenMap_chartMixOn (C : Set CircleChartSpace) (hCo : IsOpen C)
    (hC : ChartConvex C) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsOpenMap (chartMixOn C hC q hq0 hq1) :=
  ((isOpenMap_chartMix q hq0 hq1).comp
    (hCo.isOpenMap_subtype_val.prodMap hCo.isOpenMap_subtype_val)).subtype_mk _

#print axioms exists_open_chartConvex_subset
#print axioms isOpenMap_chartMixOn

end BenchmarkJump
