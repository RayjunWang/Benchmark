import MetropolisCoupling
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.SpecificLimits.Basic

/-! Countably many accepted couplings are combined into one contraction.
Positive weights retain precisely the intersection of all fixed spaces. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureEquivalenceMarkov

variable {Z : Type*} [MeasurableSpace Z]

noncomputable def couplingMixture (w : ℕ → ℝ≥0∞) (J : ℕ → Measure (Z × Z)) :
    Measure (Z × Z) := Measure.sum (fun n => w n • J n)

theorem couplingMixture_marginal_fst (w : ℕ → ℝ≥0∞) (J : ℕ → Measure (Z × Z))
    (μ : Measure Z) (hw : ∑' n, w n = 1) (hJ : ∀ n, (J n).map Prod.fst = μ) :
    (couplingMixture w J).map Prod.fst = μ := by
  rw [couplingMixture, Measure.map_sum measurable_fst.aemeasurable]
  ext s hs
  rw [Measure.sum_apply _ hs]
  simp_rw [Measure.map_smul, hJ, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.tsum_mul_right, hw, one_mul]

theorem couplingMixture_marginal_snd (w : ℕ → ℝ≥0∞) (J : ℕ → Measure (Z × Z))
    (μ : Measure Z) (hw : ∑' n, w n = 1) (hJ : ∀ n, (J n).map Prod.snd = μ) :
    (couplingMixture w J).map Prod.snd = μ := by
  rw [couplingMixture, Measure.map_sum measurable_snd.aemeasurable]
  ext s hs
  rw [Measure.sum_apply _ hs]
  simp_rw [Measure.map_smul, hJ, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.tsum_mul_right, hw, one_mul]

theorem couplingMixture_ae_iff (w : ℕ → ℝ≥0∞) (J : ℕ → Measure (Z × Z))
    (hw : ∀ n, w n ≠ 0) (P : Z × Z → Prop) :
    (∀ᵐ z ∂couplingMixture w J, P z) ↔ ∀ n, ∀ᵐ z ∂J n, P z := by
  rw [couplingMixture, Measure.ae_sum_iff]
  simp_rw [Measure.ae_ennreal_smul_measure_iff (hw _)]

/-- A concrete strictly positive probability vector. -/
noncomputable def geometricWeights (n : ℕ) : ℝ≥0∞ := (2⁻¹) ^ (n + 1)

theorem geometricWeights_ne_zero (n : ℕ) : geometricWeights n ≠ 0 := by
  unfold geometricWeights
  exact pow_ne_zero _ (by simp)

theorem geometricWeights_sum : ∑' n, geometricWeights n = 1 := by
  unfold geometricWeights
  rw [ENNReal.tsum_geometric_add_one]
  norm_num
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- Mean-ergodic convergence for the actual coupling transition. -/
theorem couplingTransition_mean_ergodic
    (μ : Measure Z) (J : Measure (Z × Z))
    (hfst : J.map Prod.fst = μ) (hsnd : J.map Prod.snd = μ)
    (f : Lp ℝ 2 μ) :
    Tendsto (fun n => birkhoffAverage ℝ (couplingTransition μ J hfst hsnd) id n f)
      atTop (𝓝 ((LinearMap.eqLocus (couplingTransition μ J hfst hsnd) 1).orthogonalProjection f)) :=
  (couplingTransition μ J hfst hsnd).tendsto_birkhoffAverage_orthogonalProjection
    (couplingTransition_norm_le_one μ J hfst hsnd) f

/-- One explicit stationary coupling carries all countably many
accepted automorphism moves with strictly positive geometric weights. -/
noncomputable def metropolisMixtureCoupling (μ : Measure Z) (e : ℕ → Z ≃ᵐ Z) :
    Measure (Z × Z) :=
  couplingMixture geometricWeights (fun n => completedCoupling μ (acceptanceFlow μ (e n)) (e n))

theorem metropolisMixtureCoupling_marginals (μ : Measure Z) [IsFiniteMeasure μ]
    (e : ℕ → Z ≃ᵐ Z) (hmap : ∀ n, μ.map (e n) ≪ μ) :
    (metropolisMixtureCoupling μ e).map Prod.fst = μ + μ ∧
      (metropolisMixtureCoupling μ e).map Prod.snd = μ + μ := by
  constructor
  · apply couplingMixture_marginal_fst _ _ _ geometricWeights_sum
    intro n
    exact (completedCoupling_marginals μ _ (e n)
      (acceptanceFlow_le μ (e n)) (acceptanceFlow_inverse_le μ (e n) (hmap n))).1
  · apply couplingMixture_marginal_snd _ _ _ geometricWeights_sum
    intro n
    exact (completedCoupling_marginals μ _ (e n)
      (acceptanceFlow_le μ (e n)) (acceptanceFlow_inverse_le μ (e n) (hmap n))).2

noncomputable def metropolisMixtureTransition (μ : Measure Z) [IsFiniteMeasure μ]
    (e : ℕ → Z ≃ᵐ Z) (hmap : ∀ n, μ.map (e n) ≪ μ) :
    Lp ℝ 2 (μ + μ) →L[ℝ] Lp ℝ 2 (μ + μ) :=
  couplingTransition (μ + μ) (metropolisMixtureCoupling μ e)
    (metropolisMixtureCoupling_marginals μ e hmap).1
    (metropolisMixtureCoupling_marginals μ e hmap).2

theorem metropolisMixtureTransition_norm_le_one (μ : Measure Z) [IsFiniteMeasure μ]
    (e : ℕ → Z ≃ᵐ Z) (hmap : ∀ n, μ.map (e n) ≪ μ) :
    ‖metropolisMixtureTransition μ e hmap‖ ≤ 1 := couplingTransition_norm_le_one _ _ _ _

/-- The fixed space of this one concrete contraction is exactly the
intersection of the automorphism-invariant subspaces. -/
theorem metropolisMixtureTransition_fixed_iff (μ : Measure Z) [IsFiniteMeasure μ]
    (e : ℕ → Z ≃ᵐ Z) (hmap : ∀ n, μ.map (e n) ≪ μ)
    (hback : ∀ n, μ ≪ μ.map (e n)) (f : Lp ℝ 2 (μ + μ)) :
    metropolisMixtureTransition μ e hmap f = f ↔
      ∀ n, ∀ᵐ z ∂μ, f z = f ((e n).symm z) := by
  unfold metropolisMixtureTransition
  rw [couplingTransition_fixed_iff, metropolisMixtureCoupling,
    couplingMixture_ae_iff _ _ geometricWeights_ne_zero]
  exact forall_congr' (fun n => completedCoupling_ae_equal_iff μ (acceptanceFlow μ (e n)) (e n)
    (acceptanceFlow_equivalent μ (e n) (hback n)).2
    (acceptanceFlow_equivalent μ (e n) (hback n)).1 f (Lp.stronglyMeasurable f).measurable)

/-- Normalized version with the original probability/finite measure μ
as each marginal. -/
noncomputable def normalizedMetropolisCoupling (μ : Measure Z) (e : ℕ → Z ≃ᵐ Z) :
    Measure (Z × Z) := (2 : ℝ≥0∞)⁻¹ • metropolisMixtureCoupling μ e

theorem half_smul_double (μ : Measure Z) : (2 : ℝ≥0∞)⁻¹ • (μ + μ) = μ := by
  rw [← two_smul ℝ≥0∞ μ, smul_smul, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_smul]

theorem normalizedMetropolisCoupling_marginals (μ : Measure Z) [IsFiniteMeasure μ]
    (e : ℕ → Z ≃ᵐ Z) (hmap : ∀ n, μ.map (e n) ≪ μ) :
    (normalizedMetropolisCoupling μ e).map Prod.fst = μ ∧
      (normalizedMetropolisCoupling μ e).map Prod.snd = μ := by
  constructor
  · rw [normalizedMetropolisCoupling, Measure.map_smul,
      (metropolisMixtureCoupling_marginals μ e hmap).1, half_smul_double]
  · rw [normalizedMetropolisCoupling, Measure.map_smul,
      (metropolisMixtureCoupling_marginals μ e hmap).2, half_smul_double]

noncomputable def normalizedMetropolisTransition (μ : Measure Z) [IsFiniteMeasure μ]
    (e : ℕ → Z ≃ᵐ Z) (hmap : ∀ n, μ.map (e n) ≪ μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  couplingTransition μ (normalizedMetropolisCoupling μ e)
    (normalizedMetropolisCoupling_marginals μ e hmap).1
    (normalizedMetropolisCoupling_marginals μ e hmap).2

theorem normalizedMetropolisTransition_norm_le_one (μ : Measure Z) [IsFiniteMeasure μ]
    (e : ℕ → Z ≃ᵐ Z) (hmap : ∀ n, μ.map (e n) ≪ μ) :
    ‖normalizedMetropolisTransition μ e hmap‖ ≤ 1 := couplingTransition_norm_le_one _ _ _ _

theorem normalizedMetropolisTransition_fixed_iff (μ : Measure Z) [IsFiniteMeasure μ]
    (e : ℕ → Z ≃ᵐ Z) (hmap : ∀ n, μ.map (e n) ≪ μ)
    (hback : ∀ n, μ ≪ μ.map (e n)) (f : Lp ℝ 2 μ) :
    normalizedMetropolisTransition μ e hmap f = f ↔
      ∀ n, ∀ᵐ z ∂μ, f z = f ((e n).symm z) := by
  unfold normalizedMetropolisTransition
  rw [couplingTransition_fixed_iff, normalizedMetropolisCoupling,
    Measure.ae_ennreal_smul_measure_iff (by simp), metropolisMixtureCoupling,
    couplingMixture_ae_iff _ _ geometricWeights_ne_zero]
  exact forall_congr' (fun n => completedCoupling_ae_equal_iff μ (acceptanceFlow μ (e n)) (e n)
    (acceptanceFlow_equivalent μ (e n) (hback n)).2
    (acceptanceFlow_equivalent μ (e n) (hback n)).1 f (Lp.stronglyMeasurable f).measurable)

end MeasureEquivalenceMarkov

#print axioms MeasureEquivalenceMarkov.couplingMixture_marginal_fst
#print axioms MeasureEquivalenceMarkov.geometricWeights_sum
#print axioms MeasureEquivalenceMarkov.couplingTransition_mean_ergodic
#print axioms MeasureEquivalenceMarkov.metropolisMixtureTransition_fixed_iff
#print axioms MeasureEquivalenceMarkov.normalizedMetropolisTransition_fixed_iff
