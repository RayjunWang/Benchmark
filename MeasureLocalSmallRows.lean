import MeasureSmallPairBound
import PositiveConvexNeighborhoods
import PositiveReweightNeighborhood

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

local instance : PolishSpace PositiveCylinderProbabilities := positiveCylinderProbabilities_polish
local instance : PolishSpace PositiveDensityBundle := positiveDensityBundle_polish
local instance : MeasurableSpace PositiveCylinderProbabilities := borel PositiveCylinderProbabilities
local instance : BorelSpace PositiveCylinderProbabilities := ⟨rfl⟩
local instance : MeasurableSpace PositiveDensityBundle := borel PositiveDensityBundle
local instance : BorelSpace PositiveDensityBundle := ⟨rfl⟩

/- Every Borel jump homomorphism on the genuine full-support measure space
has a uniform small-Hellinger row bound on a nonempty convex weak-open set. -/
theorem measure_local_small_rows
    (F : PositiveCylinderProbabilities → ℕ → RealSequences) (hFm : Measurable F)
    (hF : Homomorphism FullSupportMeasureEquivalence (Jump BoundedDifference) F)
    (k : ℕ) (A : Set PositiveCylinderProbabilities) (hAo : IsOpen A) (hAn : A.Nonempty) :
    ∃ O D : Set PositiveCylinderProbabilities, ∃ ε : ℝ, ∃ n : ℕ,
      IsOpen O ∧ O.Nonempty ∧ O ⊆ A ∧ PositiveMixConvex O ∧ 0 < ε ∧
      D ∈ residual PositiveCylinderProbabilities ∧ ContinuousOn (fun μ => F μ k) D ∧
      ∀ μ₁ ∈ O, ∀ μ₂ ∈ O, μ₁ ∈ D → μ₂ ∈ D →
        MeasureEquivalenceHellinger.energy
          ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
          ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
          (((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) +
            ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) < ε ^ 2 →
        UniformBound n (F μ₁ k) (F μ₂ k) := by
  obtain ⟨l, n, W, hWo, hWn, hWA, hRes⟩ := measure_row_match_open F hFm hF k A hAo hAn
  obtain ⟨μ₀, w, hw, hSec⟩ := densityBundle_section_hits_open W hWo hWn
  obtain ⟨U, ε, hUo, hμ₀U, hε, hTube⟩ := densityBundle_tube_at_section W hWo μ₀ w hw hSec
  have hν₀A : continuousSquareReweight w hw μ₀ ∈ A := by
    change densityTarget (positiveContinuousSection w hw μ₀) ∈ A
    exact hWA hSec
  obtain ⟨O, hOo, hOn, hOA, hOconvex, hLift⟩ :=
    positiveReweight_convex_neighborhood w hw U A hUo hAo μ₀ hμ₀U hν₀A
  let f : PositiveCylinderProbabilities → RealSequences := fun μ => F μ k
  let g : PositiveCylinderProbabilities → RealSequences := fun μ => F μ l
  obtain ⟨D, hDG, hDd, hf⟩ := measurable_continuousOn_residual f ((measurable_pi_apply k).comp hFm)
  have hD : D ∈ residual PositiveCylinderProbabilities := residual_of_dense_Gδ hDG hDd
  refine ⟨O, D, ε, 2 * n, hOo, hOn, hOA,
    hOconvex, hε, hD, hf, ?_⟩
  intro μ₁ hμ₁O μ₂ hμ₂O hμ₁D hμ₂D hE
  let σ := positiveProbabilityMix halfUnitInterval μ₁ μ₂
  have hσO : σ ∈ O := hOconvex halfUnitInterval μ₁ hμ₁O μ₂ hμ₂O
  obtain ⟨ρ, hρU, hRew⟩ := hLift σ hσO
  exact measure_small_pair_bound W hWo U w hw ε hε hTube D hD f g hf n hRes
    μ₁ μ₂ σ ρ (positiveProbabilityMix_half_measure μ₁ μ₂) hRew hρU hE hμ₁D hμ₂D

#print axioms measure_local_small_rows

end BenchmarkJump
