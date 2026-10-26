import DensityInverseContinuity
import BoundedDifferenceJump
import CategoryLocal
import OpenFiberSquare

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

def FullSupportMeasureEquivalence (μ ν : PositiveCylinderProbabilities) : Prop :=
  ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ∧
    ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)

theorem densityTarget_surjective : Function.Surjective densityTarget := by
  intro μ
  obtain ⟨z, hz⟩ := densitySource_surjective μ
  exact ⟨densityInverse z, (densityTarget_inverse z).trans hz⟩

/-- The concrete Baire cover of the genuine density bundle yields one fixed
row match, residually on a nonempty open subset over any prescribed target open set. -/
theorem measure_row_match_open
    (F : PositiveCylinderProbabilities → ℕ → RealSequences) (hFm : Measurable F)
    (hF : Homomorphism FullSupportMeasureEquivalence (Jump BoundedDifference) F)
    (k : ℕ) (A : Set PositiveCylinderProbabilities) (hAo : IsOpen A) (hAn : A.Nonempty) :
    ∃ l n : ℕ, ∃ W : Set PositiveDensityBundle,
      IsOpen W ∧ W.Nonempty ∧ W ⊆ densityTarget ⁻¹' A ∧
      ∀ᶠ z in residual PositiveDensityBundle,
        z ∈ W → UniformBound n (F (densityTarget z) k) (F (densitySource z) l) := by
  let B : ℕ × ℕ → Set PositiveDensityBundle := fun i =>
    {z | UniformBound i.2 (F (densityTarget z) k) (F (densitySource z) i.1)}
  have hB (i : ℕ × ℕ) : BaireMeasurableSet (B i) := by
    apply MeasurableSet.baireMeasurableSet
    exact (isClosed_uniformBound i.2).measurableSet.preimage
      (((measurable_pi_apply k).comp (hFm.comp continuous_densityTarget.measurable)).prodMk
        ((measurable_pi_apply i.1).comp (hFm.comp continuous_densitySource.measurable)))
  let Ω : Set PositiveDensityBundle := densityTarget ⁻¹' A
  have hΩo : IsOpen Ω := hAo.preimage continuous_densityTarget
  have hΩn : Ω.Nonempty := by
    obtain ⟨μ, hμ⟩ := hAn
    obtain ⟨z, hz⟩ := densityTarget_surjective μ
    refine ⟨z, ?_⟩
    change densityTarget z ∈ A
    rw [hz]
    exact hμ
  have hCover : Ω ⊆ ⋃ i, B i := by
    intro z _hz
    obtain ⟨l, hl⟩ := (hF (densitySource z) (densityTarget z)
      (densitySource_target_equivalent z)).2 k
    obtain ⟨n, hn⟩ := boundedDifference_equivalence.symm hl
    exact mem_iUnion.mpr ⟨(l, n), hn⟩
  obtain ⟨i, W, hWo, hWn, hWΩ, hWr⟩ :=
    baire_cover_local_residual B hB Ω hΩo hΩn hCover
  exact ⟨i.1, i.2, W, hWo, hWn, hWΩ, hWr⟩

theorem measure_good_fiber_pairs (W : Set PositiveDensityBundle) (hWo : IsOpen W)
    (D : Set PositiveCylinderProbabilities) (hD : D ∈ residual PositiveCylinderProbabilities)
    (f g : PositiveCylinderProbabilities → RealSequences) (n : ℕ)
    (hRes : ∀ᶠ z in residual PositiveDensityBundle,
      z ∈ W → UniformBound n (f (densityTarget z)) (g (densitySource z))) :
    ∀ᶠ p in residual (OpenFiberSquare (fun z : W => densitySource z)),
      densityTarget p.1.1 ∈ D ∧ densityTarget p.1.2 ∈ D ∧
      UniformBound (2 * n) (f (densityTarget p.1.1)) (f (densityTarget p.1.2)) := by
  let s : W → PositiveCylinderProbabilities := fun z => densitySource z
  let t : W → PositiveCylinderProbabilities := fun z => densityTarget z
  have hsC : Continuous s := continuous_densitySource.comp continuous_subtype_val
  have hsO : IsOpenMap s := isOpenMap_densitySource.comp hWo.isOpenMap_subtype_val
  have htC : Continuous t := continuous_densityTarget.comp continuous_subtype_val
  have htO : IsOpenMap t := isOpenMap_densityTarget.comp hWo.isOpenMap_subtype_val
  have hResW : ∀ᶠ z : W in residual W, UniformBound n (f (t z)) (g (s z)) := by
    have h := eventually_residual_open_subspace W hWo hRes
    filter_upwards [h] with z hz
    exact hz z.property
  have h1 := tendsto_residual_of_isOpenMap (continuous_fiberSquareLeft s)
    (isOpenMap_fiberSquareLeft s hsC hsO) hResW
  have h2 := tendsto_residual_of_isOpenMap (continuous_fiberSquareRight s)
    (isOpenMap_fiberSquareRight s hsC hsO) hResW
  have hD1 := tendsto_residual_of_isOpenMap
    (htC.comp (continuous_fiberSquareLeft s))
    (htO.comp (isOpenMap_fiberSquareLeft s hsC hsO)) hD
  have hD2 := tendsto_residual_of_isOpenMap
    (htC.comp (continuous_fiberSquareRight s))
    (htO.comp (isOpenMap_fiberSquareRight s hsC hsO)) hD
  filter_upwards [h1, h2, hD1, hD2] with p hp1 hp2 hpD1 hpD2
  change UniformBound n (f (t (fiberSquareLeft s p))) (g (s (fiberSquareLeft s p))) at hp1
  change UniformBound n (f (t (fiberSquareRight s p))) (g (s (fiberSquareRight s p))) at hp2
  refine ⟨hpD1, hpD2, ?_⟩
  have heq : s (fiberSquareLeft s p) = s (fiberSquareRight s p) := p.property
  rw [← heq] at hp2
  have hB := uniformBound_trans hp1 (uniformBound_symm hp2)
  simpa only [two_mul] using hB

#print axioms measure_row_match_open
#print axioms measure_good_fiber_pairs

end BenchmarkJump
