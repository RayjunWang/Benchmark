import DensitySourceOpen

open MeasureTheory Set Filter Topology
open scoped Topology

noncomputable section

namespace BenchmarkJump

theorem densityBundle_section_hits_open (W : Set PositiveDensityBundle)
    (hWo : IsOpen W) (hWn : W.Nonempty) :
    ∃ μ : PositiveCylinderProbabilities, ∃ w : C(HaarCantor, ℝ),
      ∃ hw : ∀ x, 0 < w x, positiveContinuousSection w hw μ ∈ W := by
  obtain ⟨z, hzW⟩ := hWn
  obtain ⟨V, hVo, hVW⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hWo
  have hzV : z.1 ∈ V := by
    change z ∈ Subtype.val ⁻¹' V
    rw [hVW]
    exact hzW
  obtain ⟨U, A, _hUo, hAo, hμU, haA, hUA⟩ := isOpen_prod_iff.mp hVo z.1.1 z.1.2 hzV
  obtain ⟨ε, hε, hBall⟩ := Metric.isOpen_iff.mp hAo z.1.2 haA
  obtain ⟨w, hw, hNear⟩ := positiveContinuousSection_fiber_dense z ε hε
  refine ⟨densitySource z, w, hw, ?_⟩
  rw [← hVW]
  exact hUA ⟨hμU, hBall hNear⟩

/-- A genuine open bundle neighborhood contains a uniform L2 tube around
one positive continuous section over an open source neighborhood. -/
theorem densityBundle_tube_at_section (W : Set PositiveDensityBundle) (hWo : IsOpen W)
    (μ : PositiveCylinderProbabilities) (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x)
    (hSec : positiveContinuousSection w hw μ ∈ W) :
    ∃ U : Set PositiveCylinderProbabilities, ∃ ε : ℝ,
      IsOpen U ∧ μ ∈ U ∧ 0 < ε ∧
      ∀ z : PositiveDensityBundle, densitySource z ∈ U →
        dist (densityVector z) (normalizedContinuousVector (densitySource z) w) < ε → z ∈ W := by
  obtain ⟨V, hVo, hVW⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hWo
  have hSecV : (μ, continuousSectionCoefficients w μ) ∈ V := by
    change positiveContinuousSection w hw μ ∈ Subtype.val ⁻¹' V
    rw [hVW]
    exact hSec
  obtain ⟨U₀, A, hU₀o, hAo, hμU₀, haA, hUA⟩ :=
    isOpen_prod_iff.mp hVo μ (continuousSectionCoefficients w μ) hSecV
  obtain ⟨δ, hδ, hBall⟩ := Metric.isOpen_iff.mp hAo (continuousSectionCoefficients w μ) haA
  let U := U₀ ∩ (continuousSectionCoefficients w) ⁻¹'
    Metric.ball (continuousSectionCoefficients w μ) (δ / 2)
  have hUo : IsOpen U := hU₀o.inter
    (Metric.isOpen_ball.preimage (continuous_continuousSectionCoefficients w hw))
  have hμU : μ ∈ U := ⟨hμU₀, by simp only [mem_preimage, Metric.mem_ball, dist_self]; positivity⟩
  refine ⟨U, δ / 2, hUo, hμU, by positivity, ?_⟩
  intro z hzU hzNear
  have hLift : haarLift (densitySource z)
      (continuousSectionCoefficients w (densitySource z)) =
      normalizedContinuousVector (densitySource z) w :=
    (cantorRealHaarBasis (densitySource z)).repr.symm_apply_apply _
  have hCoeff : dist z.1.2 (continuousSectionCoefficients w (densitySource z)) < δ / 2 := by
    rw [← dist_haarLift (densitySource z), hLift]
    exact hzNear
  have hSecNear : dist (continuousSectionCoefficients w (densitySource z))
      (continuousSectionCoefficients w μ) < δ / 2 := hzU.2
  have hNear : dist z.1.2 (continuousSectionCoefficients w μ) < δ := by
    have ht := dist_triangle z.1.2 (continuousSectionCoefficients w (densitySource z))
      (continuousSectionCoefficients w μ)
    linarith only [ht, hCoeff, hSecNear]
  rw [← hVW]
  exact hUA ⟨hzU.1, hBall hNear⟩

#print axioms densityBundle_tube_at_section

end BenchmarkJump
