import TruncatedEnergy
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Both limiting steps in the spectral-gap energy argument: first let the
number of coordinates tend to infinity by monotone convergence, and then
let the truncation threshold tend to infinity. -/

open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

noncomputable section

namespace BenchmarkPrefixEnergy

open BenchmarkTruncatedEnergy

lemma energyClip_tsum (a : ℕ → ℝ≥0∞) (n : ℕ) :
    energyClip (∑' i, a i) n = ⨆ N : ℕ, energyClip (∑ i ∈ Finset.range N, a i) n := by
  unfold energyClip
  rw [ENNReal.tsum_eq_iSup_nat, ENNReal.iSup_mul]
  exact iSup_inf_eq _ _

variable {X S : Type*} [MeasurableSpace X] [Fintype S]
  (μ : Measure X) [IsFiniteMeasure μ]

theorem ae_finite_tsum_of_prefix_energy
    (a : ℕ → X → ℝ≥0∞) (ha : ∀ i, Measurable (a i))
    (c : S → X → ℝ) (hc : ∀ s, Measurable (c s))
    (K : ℝ≥0∞) (hK : K ≠ ∞)
    (henergy : ∀ N n : ℕ,
      (∫⁻ x, energyClip (∑ i ∈ Finset.range N, a i x) n ∂μ) ≤
        K * ∑ s : S, ∫⁻ x, realClip (c s x) n ∂μ) :
    ∀ᵐ x ∂μ, (∑' i, a i x) ≠ ∞ := by
  apply ae_finite_of_truncated_energy μ (fun x => ∑' i, a i x)
    (Measurable.ennreal_tsum ha) c hc K hK
  intro n
  have hm : ∀ N : ℕ, Measurable (fun x => energyClip (∑ i ∈ Finset.range N, a i x) n) := by
    intro N
    unfold energyClip
    exact ((Finset.measurable_sum _ (fun i _ => ha i)).mul_const _).min measurable_const
  have hmono : Monotone (fun N : ℕ => fun x => energyClip (∑ i ∈ Finset.range N, a i x) n) := by
    intro N M hNM x
    unfold energyClip
    apply min_le_min_right
    apply mul_le_mul_right'
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hNM)
  calc
    (∫⁻ x, energyClip (∑' i, a i x) n ∂μ) =
        ∫⁻ x, ⨆ N : ℕ, energyClip (∑ i ∈ Finset.range N, a i x) n ∂μ := by
      congr 1
      funext x
      exact energyClip_tsum (fun i => a i x) n
    _ = ⨆ N : ℕ, ∫⁻ x, energyClip (∑ i ∈ Finset.range N, a i x) n ∂μ := lintegral_iSup hm hmono
    _ ≤ K * ∑ s : S, ∫⁻ x, realClip (c s x) n ∂μ := iSup_le fun N => henergy N n

theorem ae_summable_of_prefix_energy
    (a : ℕ → X → ℝ) (ha : ∀ i, Measurable (a i)) (ha0 : ∀ i x, 0 ≤ a i x)
    (c : S → X → ℝ) (hc : ∀ s, Measurable (c s))
    (K : ℝ≥0∞) (hK : K ≠ ∞)
    (henergy : ∀ N n : ℕ,
      (∫⁻ x, energyClip (∑ i ∈ Finset.range N, ENNReal.ofReal (a i x)) n ∂μ) ≤
        K * ∑ s : S, ∫⁻ x, realClip (c s x) n ∂μ) :
    ∀ᵐ x ∂μ, Summable (fun i => a i x) := by
  have hf := ae_finite_tsum_of_prefix_energy μ (fun i x => ENNReal.ofReal (a i x))
    (fun i => (ha i).ennreal_ofReal) c hc K hK henergy
  filter_upwards [hf] with x hx
  have hs := ENNReal.summable_toReal hx
  simpa only [ENNReal.toReal_ofReal (ha0 _ x)] using hs

end BenchmarkPrefixEnergy

#print axioms BenchmarkPrefixEnergy.ae_summable_of_prefix_energy
