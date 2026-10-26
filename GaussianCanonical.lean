import GaussianContinuity

/-! Measurability of the actual Gaussian family for the canonical evaluation
(Giry) measurable structure on measures and probability measures.
-/

open MeasureTheory

namespace MeasureEquivalenceGaussian

theorem measurable_gaussianProduct_canonical : Measurable gaussianProduct := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hm : Measurable (fun a : ℕ → ℝ =>
      gaussianProduct 0 ((fun x : ℕ → ℝ => x + a) ⁻¹' s)) := by
    have hset : MeasurableSet ((fun z : (ℕ → ℝ) × (ℕ → ℝ) => z.2 + z.1) ⁻¹' s) :=
      (measurable_snd.add measurable_fst) hs
    exact measurable_measure_prodMk_left hset
  have he : (fun a : ℕ → ℝ => gaussianProduct a s) =
      (fun a => gaussianProduct 0 ((fun x : ℕ → ℝ => x + a) ⁻¹' s)) := by
    funext a
    have hmap := gaussianProduct_map_add a 0
    simp only [zero_add] at hmap
    rw [← hmap]
    exact Measure.map_apply
      (show Measurable (fun x : ℕ → ℝ => x + a) from measurable_id.add_const a) hs
  rw [he]
  exact hm

theorem measurable_gaussianProbability_canonical : Measurable gaussianProbability :=
  measurable_gaussianProduct_canonical.subtype_mk

#print axioms measurable_gaussianProduct_canonical
#print axioms measurable_gaussianProbability_canonical

end MeasureEquivalenceGaussian
