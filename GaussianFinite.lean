import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-! Concrete variance-one Gaussian likelihood and affinity identities.
This file does not claim the infinite Gaussian product criterion.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace MeasureEquivalenceGaussian

noncomputable def likelihood (a b x : ℝ) : ℝ :=
  Real.exp ((a - b) * x + (-(a ^ 2 - b ^ 2) / 2))

noncomputable def rootLikelihood (a b x : ℝ) : ℝ :=
  Real.exp (((a - b) / 2) * x + (-(a ^ 2 - b ^ 2) / 4))

lemma rootLikelihood_sq (a b x : ℝ) :
    rootLikelihood a b x ^ 2 = likelihood a b x := by
  simp only [rootLikelihood, likelihood, pow_two, ← Real.exp_add]
  congr 1
  ring

lemma integral_exp_affine (b t c : ℝ) :
    (∫ x, Real.exp (t * x + c) ∂gaussianReal b 1) =
      Real.exp (b * t + t ^ 2 / 2 + c) := by
  have hm : (∫ x, Real.exp (t * x) ∂gaussianReal b 1) =
      Real.exp (b * t + t ^ 2 / 2) := by
    simpa [mgf] using congrFun (mgf_fun_id_gaussianReal (μ := b) (v := 1)) t
  simp_rw [Real.exp_add]
  rw [integral_mul_const, hm]
  simp [Real.exp_add]

lemma integrable_exp_affine (b t c : ℝ) :
    Integrable (fun x => Real.exp (t * x + c)) (gaussianReal b 1) := by
  simp_rw [Real.exp_add]
  exact (integrable_exp_mul_gaussianReal (μ := b) (v := 1) t).mul_const _

theorem integral_likelihood (a b : ℝ) :
    (∫ x, likelihood a b x ∂gaussianReal b 1) = 1 := by
  simp only [likelihood]
  rw [integral_exp_affine]
  have h : b * (a - b) + (a - b) ^ 2 / 2 + -(a ^ 2 - b ^ 2) / 2 = 0 := by ring
  rw [h, Real.exp_zero]

theorem integral_rootLikelihood (a b : ℝ) :
    (∫ x, rootLikelihood a b x ∂gaussianReal b 1) =
      Real.exp (-(a - b) ^ 2 / 8) := by
  simp only [rootLikelihood]
  rw [integral_exp_affine]
  congr 1
  ring

lemma integrable_likelihood (a b : ℝ) :
    Integrable (likelihood a b) (gaussianReal b 1) :=
  integrable_exp_affine b (a - b) (-(a ^ 2 - b ^ 2) / 2)

lemma integrable_rootLikelihood (a b : ℝ) :
    Integrable (rootLikelihood a b) (gaussianReal b 1) :=
  integrable_exp_affine b ((a - b) / 2) (-(a ^ 2 - b ^ 2) / 4)

theorem gaussian_withDensity_likelihood (a b : ℝ) :
    (gaussianReal b 1).withDensity (fun x => ENNReal.ofReal (likelihood a b x)) =
      gaussianReal a 1 := by
  rw [gaussianReal_of_var_ne_zero b one_ne_zero,
    gaussianReal_of_var_ne_zero a one_ne_zero]
  rw [← withDensity_mul volume (measurable_gaussianPDF b 1)
    (show Measurable (fun x => ENNReal.ofReal (likelihood a b x)) by
      unfold likelihood
      fun_prop)]
  apply withDensity_congr_ae
  apply ae_of_all
  intro x
  simp only [Pi.mul_apply, gaussianPDF]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg b 1 x)]
  congr 1
  simp only [gaussianPDFReal, likelihood, NNReal.coe_one, mul_one]
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  ring

lemma gaussian_set_likelihood (a b : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    ENNReal.ofReal (∫ x in s, likelihood a b x ∂gaussianReal b 1) =
      gaussianReal a 1 s := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_likelihood a b).restrict
    (ae_of_all _ (fun x => (Real.exp_pos _).le))]
  rw [← withDensity_apply _ hs, gaussian_withDensity_likelihood]

theorem finite_gaussian_withDensity_likelihood
    {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (Measure.pi (fun i => gaussianReal (b i) 1)).withDensity
        (fun x => ENNReal.ofReal (∏ i, likelihood (a i) (b i) (x i))) =
      Measure.pi (fun i => gaussianReal (a i) 1) := by
  apply (Measure.pi_eq ?_).symm
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal
      (Integrable.fintype_prod (fun i => integrable_likelihood (a i) (b i))).restrict
      (ae_of_all _ (fun x => Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le))),
    Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  have hnonneg (i : ι) : 0 ≤ ∫ x in s i, likelihood (a i) (b i) x
      ∂gaussianReal (b i) 1 := integral_nonneg (fun x => (Real.exp_pos _).le)
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hnonneg i)]
  apply Finset.prod_congr rfl
  intro i _
  exact gaussian_set_likelihood (a i) (b i) (hs i)

theorem finite_gaussian_affinity {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (∫ x : ι → ℝ, ∏ i, rootLikelihood (a i) (b i) (x i)
      ∂Measure.pi (fun i => gaussianReal (b i) 1)) =
      Real.exp (-(∑ i, (a i - b i) ^ 2) / 8) := by
  rw [integral_fintype_prod_eq_prod]
  simp_rw [integral_rootLikelihood]
  rw [← Real.exp_sum]
  congr 1
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

theorem finite_gaussian_second_moment {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (∫ x : ι → ℝ, (∏ i, rootLikelihood (a i) (b i) (x i)) ^ 2
      ∂Measure.pi (fun i => gaussianReal (b i) 1)) = 1 := by
  simp_rw [← Finset.prod_pow, rootLikelihood_sq]
  rw [integral_fintype_prod_eq_prod]
  simp [integral_likelihood]

noncomputable def gaussianProduct (a : ℕ → ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun n => gaussianReal (a n) 1)

noncomputable def blockRoot (I : Finset ℕ) (a b : ℕ → ℝ) (x : ℕ → ℝ) : ℝ :=
  ∏ i : I, rootLikelihood (a i) (b i) (x i)

theorem gaussian_product_block_affinity (I : Finset ℕ) (a b : ℕ → ℝ) :
    (∫ x, blockRoot I a b x ∂gaussianProduct b) =
      Real.exp (-(∑ i : I, (a i - b i) ^ 2) / 8) := by
  change (∫ x, (fun y : I → ℝ => ∏ i : I, rootLikelihood (a i) (b i) (y i))
    (I.restrict x) ∂Measure.infinitePi (fun n => gaussianReal (b n) 1)) = _
  rw [integral_restrict_infinitePi (fun n => gaussianReal (b n) 1)
    (s := I) (f := fun y : I → ℝ => ∏ i : I, rootLikelihood (a i) (b i) (y i)) (by
    apply Continuous.aestronglyMeasurable
    unfold rootLikelihood
    fun_prop)]
  exact finite_gaussian_affinity (fun i : I => a i) (fun i : I => b i)

theorem gaussian_product_block_second_moment (I : Finset ℕ) (a b : ℕ → ℝ) :
    (∫ x, blockRoot I a b x ^ 2 ∂gaussianProduct b) = 1 := by
  change (∫ x, (fun y : I → ℝ => (∏ i : I, rootLikelihood (a i) (b i) (y i)) ^ 2)
    (I.restrict x) ∂Measure.infinitePi (fun n => gaussianReal (b n) 1)) = _
  rw [integral_restrict_infinitePi (fun n => gaussianReal (b n) 1)
    (s := I) (f := fun y : I → ℝ => (∏ i : I, rootLikelihood (a i) (b i) (y i)) ^ 2) (by
    apply Continuous.aestronglyMeasurable
    unfold rootLikelihood
    fun_prop)]
  exact finite_gaussian_second_moment (fun i : I => a i) (fun i : I => b i)

theorem gaussian_product_block_memLp (I : Finset ℕ) (a b : ℕ → ℝ) :
    MemLp (blockRoot I a b) 2 (gaussianProduct b) := by
  apply (memLp_two_iff_integrable_sq (by
    apply Continuous.aestronglyMeasurable
    unfold blockRoot rootLikelihood
    fun_prop)).mpr
  apply Integrable.of_integral_ne_zero
  rw [gaussian_product_block_second_moment]
  exact one_ne_zero

end MeasureEquivalenceGaussian

#print axioms MeasureEquivalenceGaussian.gaussian_withDensity_likelihood
#print axioms MeasureEquivalenceGaussian.finite_gaussian_withDensity_likelihood
#print axioms MeasureEquivalenceGaussian.integral_rootLikelihood
#print axioms MeasureEquivalenceGaussian.finite_gaussian_affinity
#print axioms MeasureEquivalenceGaussian.gaussian_product_block_affinity
#print axioms MeasureEquivalenceGaussian.gaussian_product_block_second_moment
#print axioms MeasureEquivalenceGaussian.gaussian_product_block_memLp
