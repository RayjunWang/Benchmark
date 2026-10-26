import MeasureSmoothingFiberLift
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

local instance : PolishSpace PositiveCylinderProbabilities := positiveCylinderProbabilities_polish
local instance : PolishSpace PositiveDensityBundle := positiveDensityBundle_polish

theorem positiveProbabilityMix_zero (μ ν : PositiveCylinderProbabilities) :
    positiveProbabilityMix 0 μ ν = μ := by
  apply Subtype.ext
  apply ProbabilityMeasure.toMeasure_injective
  ext A hA
  change ENNReal.ofReal (1 - ((0 : unitInterval) : ℝ)) *
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A +
      ENNReal.ofReal ((0 : unitInterval) : ℝ) *
        ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A = _
  simp

def smoothingParameter (N : ℕ) : unitInterval :=
  ⟨1 / ((N : ℝ) + 1), by
    constructor
    · positivity
    · rw [div_le_one (by positivity)]
      linarith only [Nat.cast_nonneg (α := ℝ) N]⟩

theorem smoothingParameter_pos (N : ℕ) : 0 < (smoothingParameter N : ℝ) := by
  dsimp [smoothingParameter]
  positivity

theorem tendsto_smoothingParameter : Tendsto smoothingParameter atTop (𝓝 0) := by
  apply tendsto_subtype_rng.mpr
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem tendsto_smoothing (μ σ : PositiveCylinderProbabilities) :
    Tendsto (fun N => positiveProbabilityMix (smoothingParameter N) μ σ) atTop (𝓝 μ) := by
  have hArg : Continuous (fun r : unitInterval => (r, (μ, σ))) :=
    continuous_id.prodMk continuous_const
  have hc := continuous_positiveProbabilityMix.comp hArg
  change Continuous (fun r : unitInterval => positiveProbabilityMix r μ σ) at hc
  simpa only [positiveProbabilityMix_zero] using (hc.tendsto 0).comp tendsto_smoothingParameter

/-- Arbitrary Hellinger-close endpoints in the continuity set obey the same
closed output bound: smoothing gives actual fiber points, and good fiber
points are dense. No intersection with a fixed Hellinger ball is assumed. -/
theorem measure_small_pair_bound
    (W : Set PositiveDensityBundle) (hWo : IsOpen W)
    (U : Set PositiveCylinderProbabilities)
    (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x) (ε : ℝ) (hε : 0 < ε)
    (hTube : ∀ z : PositiveDensityBundle, densitySource z ∈ U →
      dist (densityVector z) (normalizedContinuousVector (densitySource z) w) < ε → z ∈ W)
    (D : Set PositiveCylinderProbabilities) (hD : D ∈ residual PositiveCylinderProbabilities)
    (f g : PositiveCylinderProbabilities → RealSequences) (hf : ContinuousOn f D) (n : ℕ)
    (hRes : ∀ᶠ z in residual PositiveDensityBundle,
      z ∈ W → UniformBound n (f (densityTarget z)) (g (densitySource z)))
    (μ₁ μ₂ σ ρ : PositiveCylinderProbabilities)
    (hσ : ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) =
      measureMidpoint ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (hRew : continuousSquareReweight w hw ρ = σ) (hρU : ρ ∈ U)
    (hE : MeasureEquivalenceHellinger.energy
      ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      (((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) +
        ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) < ε ^ 2)
    (hμ₁D : μ₁ ∈ D) (hμ₂D : μ₂ ∈ D) : UniformBound (2 * n) (f μ₁) (f μ₂) := by
  letI : PolishSpace W := hWo.polishSpace
  letI : PolishSpace (OpenFiberSquare (fun z : W => densitySource z)) :=
    openFiberSquare_polish _ (continuous_densitySource.comp continuous_subtype_val)
  let G : Set (OpenFiberSquare (fun z : W => densitySource z)) :=
    {q | densityTarget q.1.1 ∈ D ∧ densityTarget q.1.2 ∈ D ∧
      UniformBound (2 * n) (f (densityTarget q.1.1)) (f (densityTarget q.1.2))}
  let S := measureFiberEndpoints W '' G
  have hG : G ∈ residual _ := measure_good_fiber_pairs W hWo D hD f g n hRes
  have hDense (p : OpenFiberSquare (fun z : W => densitySource z)) :
      measureFiberEndpoints W p ∈ closure S :=
    (continuous_measureFiberEndpoints W).continuousAt.continuousWithinAt.mem_closure_image
      (dense_of_mem_residual hG p)
  have hSmooth (N : ℕ) :
      (positiveProbabilityMix (smoothingParameter N) μ₁ σ,
        positiveProbabilityMix (smoothingParameter N) μ₂ σ) ∈ closure S := by
    obtain ⟨p, hp⟩ := measure_smoothing_fiber_lift W U w hw ε hε hTube
      μ₁ μ₂ σ ρ hσ hRew hρU hE (smoothingParameter N) (smoothingParameter_pos N)
    exact hp ▸ hDense p
  have hLim := (tendsto_smoothing μ₁ σ).prodMk_nhds (tendsto_smoothing μ₂ σ)
  have hp : (μ₁, μ₂) ∈ closure S := isClosed_closure.mem_of_tendsto hLim
    (Eventually.of_forall hSmooth)
  apply measure_uniformBound_of_mem_closure f hf (2 * n) S _ _ (μ₁, μ₂) ⟨hμ₁D, hμ₂D⟩ hp
  · rintro q ⟨r, hr, rfl⟩
    exact ⟨hr.1, hr.2.1⟩
  · rintro q ⟨r, hr, rfl⟩
    exact hr.2.2

#print axioms measure_small_pair_bound

end BenchmarkJump
