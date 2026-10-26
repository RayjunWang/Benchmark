import MeasureRowCover
import DensityBundleEndpoints
import DensityBundleTube

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

local instance : PolishSpace PositiveCylinderProbabilities := positiveCylinderProbabilities_polish
local instance : PolishSpace PositiveDensityBundle := positiveDensityBundle_polish

def measureFiberEndpoints (W : Set PositiveDensityBundle)
    (p : OpenFiberSquare (fun z : W => densitySource z)) :
    PositiveCylinderProbabilities × PositiveCylinderProbabilities :=
  (densityTarget p.1.1, densityTarget p.1.2)

theorem continuous_measureFiberEndpoints (W : Set PositiveDensityBundle) :
    Continuous (measureFiberEndpoints W) :=
  ((continuous_densityTarget.comp continuous_subtype_val).comp
    (continuous_fiberSquareLeft _)).prodMk
      ((continuous_densityTarget.comp continuous_subtype_val).comp (continuous_fiberSquareRight _))

theorem measure_uniformBound_of_mem_closure {D : Set PositiveCylinderProbabilities}
    (f : PositiveCylinderProbabilities → RealSequences) (hf : ContinuousOn f D)
    (n : ℕ) (S : Set (PositiveCylinderProbabilities × PositiveCylinderProbabilities))
    (hSD : S ⊆ D ×ˢ D)
    (hBound : ∀ p ∈ S, UniformBound n (f p.1) (f p.2))
    (p : PositiveCylinderProbabilities × PositiveCylinderProbabilities) (hpD : p ∈ D ×ˢ D)
    (hp : p ∈ closure S) : UniformBound n (f p.1) (f p.2) := by
  have hc := ((hf p.1 hpD.1).prodMap (hf p.2 hpD.2)).mono hSD
  have hm : MapsTo (Prod.map f f) S
      {q : RealSequences × RealSequences | UniformBound n q.1 q.2} := hBound
  have hcl := hc.mem_closure hp hm
  simpa only [(isClosed_uniformBound n).closure_eq] using hcl

/-- The actual Baire fiber-square estimate extends to every pair in that
fiber square whose targets lie in the relative continuity set. -/
theorem measure_bound_on_every_fiber_pair
    (W : Set PositiveDensityBundle) (hWo : IsOpen W)
    (D : Set PositiveCylinderProbabilities) (hD : D ∈ residual PositiveCylinderProbabilities)
    (f g : PositiveCylinderProbabilities → RealSequences) (hf : ContinuousOn f D) (n : ℕ)
    (hRes : ∀ᶠ z in residual PositiveDensityBundle,
      z ∈ W → UniformBound n (f (densityTarget z)) (g (densitySource z)))
    (p : OpenFiberSquare (fun z : W => densitySource z))
    (hpD : measureFiberEndpoints W p ∈ D ×ˢ D) :
    UniformBound (2 * n) (f (densityTarget p.1.1)) (f (densityTarget p.1.2)) := by
  letI : PolishSpace W := hWo.polishSpace
  letI : PolishSpace (OpenFiberSquare (fun z : W => densitySource z)) :=
    openFiberSquare_polish _ (continuous_densitySource.comp continuous_subtype_val)
  let G : Set (OpenFiberSquare (fun z : W => densitySource z)) :=
    {q | densityTarget q.1.1 ∈ D ∧ densityTarget q.1.2 ∈ D ∧
      UniformBound (2 * n) (f (densityTarget q.1.1)) (f (densityTarget q.1.2))}
  have hG : G ∈ residual _ := measure_good_fiber_pairs W hWo D hD f g n hRes
  have hp : p ∈ closure G := dense_of_mem_residual hG p
  have hImage : measureFiberEndpoints W p ∈ closure (measureFiberEndpoints W '' G) :=
    (continuous_measureFiberEndpoints W).continuousAt.continuousWithinAt.mem_closure_image hp
  apply measure_uniformBound_of_mem_closure f hf (2 * n) (measureFiberEndpoints W '' G) _ _ _ hpD hImage
  · rintro q ⟨r, hr, rfl⟩
    exact ⟨hr.1, hr.2.1⟩
  · rintro q ⟨r, hr, rfl⟩
    exact hr.2.2

#print axioms measure_bound_on_every_fiber_pair

end BenchmarkJump
