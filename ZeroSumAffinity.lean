import RootContinuity
import HellingerInner

/-! The uniform small-shift affinity estimate for the intrinsic zero-sum
l1 subgroup, derived from actual RN roots rather than assumed. -/

open MeasureTheory Filter Topology
open scoped Topology ENNReal

noncomputable section

namespace MeasureEquivalenceZeroSumAffinity

open MeasureEquivalenceSolenoid MeasureEquivalenceRootContinuity
open MeasureEquivalenceRNGraph MeasureEquivalenceHellinger

variable {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    [MulAction (Multiplicative CompactSequences) Z]
    [ContinuousSMul (Multiplicative CompactSequences) Z]
    (M : Measure Z) [IsProbabilityMeasure M]
    (hQI : ∀ h : CompactSequences, h ∈ zeroSumSubgroup →
      Multiplicative.ofAdd h ∈ quasiInvariantSubgroup M)

def zeroSumAffinity (h : zeroSumSpace) : ℝ :=
  affinity M (M.map (fun z => Multiplicative.ofAdd (zeroSumInclusion h) • z))

include hQI in
theorem zeroSumAffinity_continuous : Continuous (zeroSumAffinity M) := by
  have he : zeroSumAffinity M = fun h : zeroSumSpace =>
      inner ℝ (root M M) (zeroSumRoot M h) := by
    funext h
    exact affinity_eq_inner_roots M _ M Measure.AbsolutelyContinuous.rfl
      (hQI _ ⟨h, h.property, rfl⟩).1
  rw [he]
  exact continuous_const.inner (zeroSumRoot_continuous M hQI)

theorem zeroSumAffinity_zero : zeroSumAffinity M 0 = 1 := by
  change affinity M (M.map (fun z => Multiplicative.ofAdd (zeroSumInclusion 0) • z)) = 1
  have hz : zeroSumInclusion 0 = 0 := map_zero zeroSumInclusion
  rw [hz]
  change affinity M (M.map (fun z => (1 : Multiplicative CompactSequences) • z)) = 1
  simpa only [one_smul, Measure.map_id'] using affinity_self M

include hQI in
theorem uniform_twoPoint_affinity (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, |a| < δ → ∀ n : ℕ,
      1 - ε ≤ affinity M
        (M.map (fun z => Multiplicative.ofAdd (l1Embedding (twoPoint a n)) • z)) := by
  have hzero := zeroSumAffinity_zero M
  have hev : ∀ᶠ h : zeroSumSpace in 𝓝 0, 1 - ε < zeroSumAffinity M h :=
    (zeroSumAffinity_continuous M hQI).continuousAt.eventually
      (lt_mem_nhds (by rw [hzero]; linarith : 1-ε < zeroSumAffinity M 0))
  obtain ⟨d, hd, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨d/2, by positivity, ?_⟩
  intro a ha n
  let u : zeroSumSpace := ⟨twoPoint a n, twoPoint_zeroSum a n⟩
  have hu : dist u 0 < d := by
    rw [dist_zero_right]
    change ‖twoPoint a n‖ < d
    exact (twoPoint_norm_le a n).trans_lt (by linarith)
  exact (hball hu).le

end MeasureEquivalenceZeroSumAffinity

#print axioms MeasureEquivalenceZeroSumAffinity.uniform_twoPoint_affinity
