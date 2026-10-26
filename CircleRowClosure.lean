import CircleSmallPairs

open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

open MeasureEquivalenceCircle MeasureEquivalenceCircleTopology

local instance : PolishSpace NullCircleGroup := h0_polish
local instance : SeparableSpace NullCircleGroup := h0_separable

/-- The finite-truncation closure step in the concrete circle proof.
The uniform output bound holds even for a pair whose difference need not
itself be a null sequence, provided the coordinate distances are small. -/
theorem circle_small_pair_bound
    (U : Set CircleSequences) (W : Set NullCircleGroup)
    (hUo : IsOpen U) (hWo : IsOpen W)
    (D : Set CircleSequences) (hD : D ∈ residual CircleSequences)
    (f g : CircleSequences → RealSequences) (hf : ContinuousOn f D)
    (n : ℕ)
    (hRes : ∀ᶠ p in residual (CircleSequences × NullCircleGroup),
      p ∈ U ×ˢ W → UniformBound n (f (circleAction p)) (g p.1))
    (h₀ : NullCircleGroup) (hh₀ : h₀ ∈ W) (ε : ℝ)
    (hBall : Metric.ball h₀ ε ⊆ W)
    (x z : CircleSequences) (hx : x ∈ U)
    (hyD : circleAction (x, h₀) ∈ D) (hzD : z ∈ D)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδε : δ < ε)
    (hSmall : ∀ i, ‖z i - circleAction (x, h₀) i‖ ≤ δ) :
    UniformBound (2 * n) (f (circleAction (x, h₀))) (f z) := by
  classical
  let Ω : Set CircleTriples := U ×ˢ (W ×ˢ W)
  let G : Set CircleTriples := {t | t ∈ Ω →
    tripleEndpoints t ∈ D ×ˢ D ∧
    UniformBound (2 * n) (f (tripleEndpoints t).1) (f (tripleEndpoints t).2)}
  have hG : G ∈ residual CircleTriples := circle_good_triples U W D hD f g n hRes
  let S : Set CircleTriples := Ω ∩ G
  have hΩclosure : Ω ⊆ closure S :=
    mem_closure_inter_of_residual Ω G (hUo.prod (hWo.prod hWo)) hG
  let v : ℕ → CircleTriples := fun N =>
    (x, h₀, h₀ + trunc0 (Finset.range N) (z - circleAction (x, h₀)))
  have hv (N : ℕ) : v N ∈ Ω := by
    refine ⟨hx, hh₀, hBall ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have ht := norm_trunc0_le (Finset.range N) (z - circleAction (x, h₀)) δ hδ hSmall
    simpa only [v, add_sub_cancel_left] using lt_of_le_of_lt ht hδε
  have hvImg (N : ℕ) : tripleEndpoints (v N) ∈ closure (tripleEndpoints '' S) :=
    image_closure_subset_closure_image continuous_tripleEndpoints
      ⟨v N, hΩclosure (hv N), rfl⟩
  have hvLim : Tendsto (fun N => tripleEndpoints (v N)) atTop
      (𝓝 (circleAction (x, h₀), z)) :=
    tendsto_const_nhds.prodMk_nhds (tendsto_truncated_endpoint x z h₀)
  have hp : (circleAction (x, h₀), z) ∈ closure (tripleEndpoints '' S) :=
    isClosed_closure.mem_of_tendsto hvLim (Eventually.of_forall hvImg)
  apply uniformBound_of_mem_closure f hf (2 * n) (tripleEndpoints '' S)
    (fun p hp => ?_) (fun p hp => ?_) (circleAction (x, h₀), z) ⟨hyD, hzD⟩ hp
  · obtain ⟨t, ht, rfl⟩ := hp
    exact (ht.2 ht.1).1
  · obtain ⟨t, ht, rfl⟩ := hp
    exact (ht.2 ht.1).2

#print axioms circle_small_pair_bound

end BenchmarkJump
