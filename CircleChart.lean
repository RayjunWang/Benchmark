import CircleRowClosure
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.NhdsWithin

open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

abbrev CircleChartInterval := Set.Ioo (0 : ℝ) 1
abbrev CircleChartSpace := ℕ → CircleChartInterval

def circleChartCoordinate (x : CircleChartInterval) : UnitAddCircle := (x : ℝ)

def circleChart (x : CircleChartSpace) : CircleSequences :=
  fun i => circleChartCoordinate (x i)

theorem isOpenEmbedding_circleChartCoordinate : IsOpenEmbedding circleChartCoordinate := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val
  · intro x y hxy
    apply Subtype.ext
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show (x : ℝ) ∈ Ico (0 : ℝ) (0 + 1) from by
        simpa only [zero_add] using Ioo_subset_Ico_self x.property)
      (show (y : ℝ) ∈ Ico (0 : ℝ) (0 + 1) from by
        simpa only [zero_add] using Ioo_subset_Ico_self y.property)).mp
    exact hxy
  · exact QuotientAddGroup.isOpenMap_coe.comp isOpen_Ioo.isOpenMap_subtype_val

theorem isEmbedding_circleChart : IsEmbedding circleChart :=
  IsEmbedding.piMap (fun _ => isOpenEmbedding_circleChartCoordinate.isEmbedding)

theorem continuous_circleChart : Continuous circleChart := isEmbedding_circleChart.continuous

theorem range_circleChartCoordinate : range circleChartCoordinate = ({0}ᶜ : Set UnitAddCircle) := by
  have hr := (AddCircle.openPartialHomeomorphCoe (1 : ℝ) 0).image_source_eq_target
  convert hr using 1
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, by simpa [AddCircle.openPartialHomeomorphCoe, CircleChartInterval]
        using x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, by simpa [AddCircle.openPartialHomeomorphCoe, CircleChartInterval] using hx⟩, rfl⟩

theorem denseRange_circleChartCoordinate : DenseRange circleChartCoordinate := by
  intro y
  by_cases hy : y = 0
  · subst y
    have h0 : (0 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
      rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
      exact ⟨le_rfl, by norm_num⟩
    have hcl := image_closure_subset_closure_image (AddCircle.continuous_mk' (1 : ℝ))
      ⟨0, h0, rfl⟩
    have heq : ((fun x : ℝ => (x : UnitAddCircle)) '' Set.Ioo (0 : ℝ) 1) =
        range circleChartCoordinate := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨x, x.property, rfl⟩
    change (0 : UnitAddCircle) ∈ closure
      ((fun x : ℝ => (x : UnitAddCircle)) '' Set.Ioo (0 : ℝ) 1) at hcl
    rw [heq] at hcl
    exact hcl
  · apply subset_closure
    rw [range_circleChartCoordinate]
    simpa using hy

theorem denseRange_circleChart : DenseRange circleChart :=
  DenseRange.piMap (fun _ => denseRange_circleChartCoordinate)

theorem range_circleChart : range circleChart = {x : CircleSequences | ∀ i, x i ≠ 0} := by
  classical
  ext x
  constructor
  · rintro ⟨y, rfl⟩ i
    have hi : circleChartCoordinate (y i) ∈ range circleChartCoordinate := mem_range_self _
    rw [range_circleChartCoordinate] at hi
    exact hi
  · intro hx
    have hi (i : ℕ) : ∃ y : CircleChartInterval, circleChartCoordinate y = x i := by
      apply mem_range.mp
      rw [range_circleChartCoordinate]
      exact hx i
    choose y hy using hi
    exact ⟨y, funext hy⟩

/-- The dense product chart is comeager in the compact circle product. -/
theorem circleChart_range_residual : range circleChart ∈ residual CircleSequences := by
  have hOne (i : ℕ) : {x : CircleSequences | x i ≠ 0} ∈ residual CircleSequences := by
    apply residual_of_dense_open
    · exact isOpen_compl_singleton.preimage (continuous_apply i)
    · have hd : Dense ({0}ᶜ : Set UnitAddCircle) := by
        rw [← range_circleChartCoordinate]
        exact denseRange_circleChartCoordinate
      exact hd.preimage (isOpenMap_eval i)
  simpa only [range_circleChart, setOf_forall] using countable_iInter_mem.mpr hOne

/-- Dense embeddings preserve residual assertions by preimage. -/
theorem tendsto_residual_of_denseEmbedding {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] {f : A → B}
    (hf : IsEmbedding f) (hd : DenseRange f) : Tendsto f (residual A) (residual B) := by
  apply le_countableGenerate_iff_of_countableInterFilter.mpr
  rintro U ⟨hUo, hUd⟩
  apply residual_of_dense_open (hUo.preimage hf.continuous)
  apply dense_iff_inter_open.mpr
  intro V hVo hVn
  obtain ⟨W, hWo, hWV⟩ := hf.isInducing.isOpen_iff.mp hVo
  obtain ⟨a, haV⟩ := hVn
  have haW : f a ∈ W := by change a ∈ f ⁻¹' W; rw [hWV]; exact haV
  obtain ⟨b, hbW, hbU⟩ := hUd.inter_open_nonempty W hWo ⟨f a, haW⟩
  obtain ⟨z, hzWU, hzRange⟩ := hd.inter_open_nonempty (W ∩ U) (hWo.inter hUo) ⟨b, hbW, hbU⟩
  obtain ⟨a', rfl⟩ := hzRange
  exact ⟨a', by rw [← hWV]; exact hzWU.1, hzWU.2⟩

#print axioms circleChart_range_residual
#print axioms tendsto_residual_of_denseEmbedding

end BenchmarkJump
