import PositiveSectionDensity

open MeasureTheory Set Filter Topology
open scoped Topology

noncomputable section

namespace BenchmarkJump

/-- The source projection of the genuine positive square-density bundle is open.
The proof uses the proved density and continuity of positive continuous sections. -/
theorem isOpenMap_densitySource : IsOpenMap densitySource := by
  intro W hW
  apply isOpen_iff_mem_nhds.mpr
  rintro μ ⟨z, hzW, rfl⟩
  obtain ⟨V, hVo, hVW⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hW
  have hzV : z.1 ∈ V := by
    change z ∈ Subtype.val ⁻¹' V
    rw [hVW]
    exact hzW
  obtain ⟨U, A, hUo, hAo, hμU, haA, hUA⟩ :=
    isOpen_prod_iff.mp hVo z.1.1 z.1.2 hzV
  obtain ⟨ε, hε, hBall⟩ := Metric.isOpen_iff.mp hAo z.1.2 haA
  obtain ⟨w, hw, hNear⟩ := positiveContinuousSection_fiber_dense z ε hε
  have hsecW : positiveContinuousSection w hw (densitySource z) ∈ W := by
    rw [← hVW]
    exact hUA ⟨hμU, hBall hNear⟩
  have hN := (hW.preimage (continuous_positiveContinuousSection w hw)).mem_nhds hsecW
  exact mem_of_superset hN (fun ν hν =>
    ⟨positiveContinuousSection w hw ν, hν, densitySource_positiveContinuousSection w hw ν⟩)

theorem densitySource_surjective : Function.Surjective densitySource := by
  intro μ
  exact ⟨positiveContinuousSection 1 (by intro x; norm_num) μ,
    densitySource_positiveContinuousSection 1 (by intro x; norm_num) μ⟩

#print axioms isOpenMap_densitySource

end BenchmarkJump
