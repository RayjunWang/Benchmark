import PrefixTruncatedEnergy

/-! Normalization of the finite-prefix energy estimates. Displacement
energies are only assumed finite almost everywhere, with no integrability
requirement. This closes the two-limit argument for such estimates. -/

open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

noncomputable section

namespace BenchmarkNormalizedTruncation

open BenchmarkTruncatedEnergy BenchmarkPrefixEnergy

def threshold (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((n : ℝ) + 1)
def reciprocal (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (1 / ((n : ℝ) + 1))

lemma reciprocal_mul_threshold (n : ℕ) : reciprocal n * threshold n = 1 := by
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  unfold reciprocal threshold
  rw [← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hpos.ne']
  norm_num

lemma energyClip_eq_scaled_min (H : ℝ≥0∞) (n : ℕ) :
    energyClip H n = reciprocal n * min H (threshold n) := by
  unfold energyClip
  rw [mul_min, reciprocal_mul_threshold, mul_comm (reciprocal n) H]
  rfl

lemma realClip_toReal (c : ℝ≥0∞) (hc : c ≠ ∞) (n : ℕ) :
    realClip c.toReal n = energyClip c n := by
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  unfold realClip energyClip
  rw [ENNReal.ofReal_min, ENNReal.ofReal_one, ENNReal.ofReal_div_of_pos hpos,
    ENNReal.ofReal_toReal hc, div_eq_mul_inv, one_div, ENNReal.ofReal_inv_of_pos hpos]

variable {X S : Type*} [MeasurableSpace X] [Fintype S]
  (μ : Measure X) [IsFiniteMeasure μ]

lemma integral_energyClip (H : X → ℝ≥0∞) (n : ℕ) :
    (∫⁻ x, energyClip (H x) n ∂μ) =
      reciprocal n * ∫⁻ x, min (H x) (threshold n) ∂μ := by
  simp_rw [energyClip_eq_scaled_min]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Finite-prefix unnormalized truncated-energy inequalities force almost
every full energy sum to be finite. The comparison energies may be
unbounded and need not belong to L¹. -/
theorem ae_finite_tsum_of_unnormalized_energy
    (a : ℕ → X → ℝ≥0∞) (ha : ∀ i, Measurable (a i))
    (c : S → X → ℝ≥0∞) (hc : ∀ s, Measurable (c s))
    (hcfinite : ∀ s, ∀ᵐ x ∂μ, c s x ≠ ∞)
    (K : ℝ≥0∞) (hK : K ≠ ∞)
    (henergy : ∀ N n : ℕ,
      (∫⁻ x, min (∑ i ∈ Finset.range N, a i x) (threshold n) ∂μ) ≤
        K * ∑ s : S, ∫⁻ x, min (c s x) (threshold n) ∂μ) :
    ∀ᵐ x ∂μ, (∑' i, a i x) ≠ ∞ := by
  classical
  apply ae_finite_tsum_of_prefix_energy μ a ha (fun s x => (c s x).toReal)
    (fun s => (hc s).ennreal_toReal) K hK
  intro N n
  have hrewrite : (∑ s : S, ∫⁻ x, energyClip (c s x) n ∂μ) =
      ∑ s : S, ∫⁻ x, realClip (c s x).toReal n ∂μ := by
    apply Finset.sum_congr rfl
    intro s _
    apply lintegral_congr_ae
    filter_upwards [hcfinite s] with x hx
    exact (realClip_toReal (c s x) hx n).symm
  calc
    (∫⁻ x, energyClip (∑ i ∈ Finset.range N, a i x) n ∂μ) =
        reciprocal n * ∫⁻ x, min (∑ i ∈ Finset.range N, a i x) (threshold n) ∂μ :=
      integral_energyClip μ _ n
    _ ≤ reciprocal n * (K * ∑ s : S, ∫⁻ x, min (c s x) (threshold n) ∂μ) :=
      mul_le_mul_left' (henergy N n) _
    _ = K * ∑ s : S, ∫⁻ x, energyClip (c s x) n ∂μ := by
      simp_rw [integral_energyClip μ]
      rw [← Finset.mul_sum]
      ac_rfl
    _ = K * ∑ s : S, ∫⁻ x, realClip (c s x).toReal n ∂μ := by rw [hrewrite]

end BenchmarkNormalizedTruncation

#print axioms BenchmarkNormalizedTruncation.ae_finite_tsum_of_unnormalized_energy
