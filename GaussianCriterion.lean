import GaussianFinite
import ProductAffinity
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration

/-! Assembly of the infinite Gaussian product criterion.
Only completed lemmas are included; no placeholder assumptions are used.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal BigOperators Topology InnerProductSpace

namespace MeasureEquivalenceGaussian

instance gaussianProduct_probability (a : ℕ → ℝ) : IsProbabilityMeasure (gaussianProduct a) := by
  unfold gaussianProduct
  infer_instance

lemma continuous_blockRoot (I : Finset ℕ) (a b : ℕ → ℝ) :
    Continuous (blockRoot I a b) := by
  unfold blockRoot rootLikelihood
  fun_prop

lemma blockRoot_nonneg (I : Finset ℕ) (a b : ℕ → ℝ) (x : ℕ → ℝ) :
    0 ≤ blockRoot I a b x :=
  Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le)

lemma map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {f : β → ℝ≥0∞} {g : α → β}
    (hf : Measurable f) (hg : Measurable g) :
    (μ.withDensity (fun x => f (g x))).map g = (μ.map g).withDensity f := by
  ext s hs
  rw [Measure.map_apply hg hs, withDensity_apply _ (hg hs),
    withDensity_apply _ hs, setLIntegral_map hs hf hg]

lemma weighted_block_map (I : Finset ℕ) (a b : ℕ → ℝ) :
    ((gaussianProduct b).withDensity (fun x => ENNReal.ofReal (blockRoot I a b x ^ 2))).map
      I.restrict = Measure.pi (fun i : I => gaussianReal (a i) 1) := by
  have heq : (fun x => ENNReal.ofReal (blockRoot I a b x ^ 2)) =
      (fun x => (fun y : I → ℝ => ENNReal.ofReal
        (∏ i : I, likelihood (a i) (b i) (y i))) (I.restrict x)) := by
    funext x
    simp only [blockRoot, ← Finset.prod_pow, rootLikelihood_sq]
    rfl
  rw [heq]
  rw [map_withDensity_comp (gaussianProduct b)
    (f := fun y : I → ℝ => ENNReal.ofReal (∏ i : I, likelihood (a i) (b i) (y i)))
    (g := I.restrict) (by unfold likelihood; fun_prop) (Finset.measurable_restrict I)]
  change ((Measure.infinitePi (fun n => gaussianReal (b n) 1)).map I.restrict).withDensity _ = _
  rw [Measure.infinitePi_map_restrict, finite_gaussian_withDensity_likelihood]

lemma weighted_block_map_subset {I J : Finset ℕ} (hJI : J ⊆ I) (a b : ℕ → ℝ) :
    ((gaussianProduct b).withDensity (fun x => ENNReal.ofReal (blockRoot I a b x ^ 2))).map
      J.restrict = Measure.pi (fun j : J => gaussianReal (a j) 1) := by
  have hm := congrArg
    (fun η : Measure (I → ℝ) => η.map (Finset.restrict₂ (π := fun _ : ℕ => ℝ) hJI))
    (weighted_block_map I a b)
  dsimp only at hm
  rw [Measure.map_map (Finset.measurable_restrict₂ hJI) (Finset.measurable_restrict I),
    Finset.restrict₂_comp_restrict] at hm
  exact hm.trans (isProjectiveMeasureFamily_pi (fun n => gaussianReal (a n) 1) I J hJI).symm

lemma block_cylinder_density {I J : Finset ℕ} (hJI : J ⊆ I) (a b : ℕ → ℝ)
    {s : Set (J → ℝ)} (hs : MeasurableSet s) :
    ENNReal.ofReal (∫ x in cylinder J s, blockRoot I a b x ^ 2 ∂gaussianProduct b) =
      gaussianProduct a (cylinder J s) := by
  rw [ofReal_integral_eq_lintegral_ofReal
    (gaussian_product_block_memLp I a b).integrable_sq.restrict
    (ae_of_all _ (fun x => sq_nonneg _))]
  change (∫⁻ x in J.restrict ⁻¹' s, ENNReal.ofReal (blockRoot I a b x ^ 2)
    ∂gaussianProduct b) = _
  rw [← withDensity_apply _ (Finset.measurable_restrict J hs)]
  change ((gaussianProduct b).withDensity _ ) (J.restrict ⁻¹' s) = _
  rw [← Measure.map_apply (Finset.measurable_restrict J) hs, weighted_block_map_subset hJI]
  exact (Measure.infinitePi_cylinder (fun n => gaussianReal (a n) 1) hs).symm

noncomputable def blockRootLp (I : Finset ℕ) (a b : ℕ → ℝ) : Lp ℝ 2 (gaussianProduct b) :=
  (gaussian_product_block_memLp I a b).toLp (blockRoot I a b)

lemma blockRootLp_coe (I : Finset ℕ) (a b : ℕ → ℝ) :
    blockRootLp I a b =ᵐ[gaussianProduct b] blockRoot I a b :=
  MemLp.coeFn_toLp (gaussian_product_block_memLp I a b)

lemma blockRootLp_unit (I : Finset ℕ) (a b : ℕ → ℝ) : ‖blockRootLp I a b‖ = 1 := by
  have hi : ⟪blockRootLp I a b, blockRootLp I a b⟫_ℝ = 1 := by
    rw [L2.inner_def]
    calc
      _ = ∫ x, blockRoot I a b x ^ 2 ∂gaussianProduct b := by
        apply integral_congr_ae
        filter_upwards [blockRootLp_coe I a b] with x hx
        simp [hx, pow_two]
      _ = 1 := gaussian_product_block_second_moment I a b
  rw [real_inner_self_eq_norm_sq] at hi
  nlinarith [norm_nonneg (blockRootLp I a b)]

lemma blockRoot_sdiff {I J : Finset ℕ} (hIJ : I ⊆ J) (a b : ℕ → ℝ) (x : ℕ → ℝ) :
    blockRoot J a b x = blockRoot (J \ I) a b x * blockRoot I a b x := by
  unfold blockRoot
  rw [Finset.prod_coe_sort J (fun i : ℕ => rootLikelihood (a i) (b i) (x i)),
    Finset.prod_coe_sort (J \ I) (fun i : ℕ => rootLikelihood (a i) (b i) (x i)),
    Finset.prod_coe_sort I (fun i : ℕ => rootLikelihood (a i) (b i) (x i))]
  exact (Finset.prod_sdiff hIJ).symm

lemma blockRoot_indep (I J : Finset ℕ) (hIJ : Disjoint I J) (a b : ℕ → ℝ) :
    IndepFun (fun x => blockRoot I a b x ^ 2) (blockRoot J a b) (gaussianProduct b) := by
  have hind : iIndepFun (fun n (x : ℕ → ℝ) => x n) (gaussianProduct b) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have hb := hind.indepFun_finset I J hIJ (fun _ => measurable_pi_apply _)
  exact hb.comp
    (show Measurable (fun y : I → ℝ => (∏ i : I, rootLikelihood (a i) (b i) (y i)) ^ 2) by
      unfold rootLikelihood
      fun_prop)
    (show Measurable (fun y : J → ℝ => ∏ i : J, rootLikelihood (a i) (b i) (y i)) by
      unfold rootLikelihood
      fun_prop)

lemma blockRootLp_inner_of_subset {I J : Finset ℕ} (hIJ : I ⊆ J) (a b : ℕ → ℝ) :
    ⟪blockRootLp I a b, blockRootLp J a b⟫_ℝ =
      Real.exp (-(∑ i ∈ J \ I, (a i - b i) ^ 2) / 8) := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, blockRoot I a b x ^ 2 * blockRoot (J \ I) a b x ∂gaussianProduct b := by
      apply integral_congr_ae
      filter_upwards [blockRootLp_coe I a b, blockRootLp_coe J a b] with x hi hj
      simp only [hi, hj, Real.inner_apply]
      rw [blockRoot_sdiff hIJ]
      ring
    _ = (∫ x, blockRoot I a b x ^ 2 ∂gaussianProduct b) *
        ∫ x, blockRoot (J \ I) a b x ∂gaussianProduct b := by
      exact (blockRoot_indep I (J \ I) disjoint_sdiff_self_right a b).integral_fun_mul_eq_mul_integral
        (continuous_blockRoot I a b |>.pow 2 |>.aestronglyMeasurable)
        (continuous_blockRoot (J \ I) a b).aestronglyMeasurable
    _ = _ := by
      rw [gaussian_product_block_second_moment, gaussian_product_block_affinity, one_mul]
      rw [Finset.sum_coe_sort (J \ I) (fun i : ℕ => (a i - b i) ^ 2)]

noncomputable def energy (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (a i - b i) ^ 2

lemma energy_mono (a b : ℕ → ℝ) : Monotone (energy a b) := by
  intro m n hmn
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
    (fun _ _ _ => sq_nonneg _)

lemma range_inner_of_le (a b : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    ⟪blockRootLp (Finset.range m) a b, blockRootLp (Finset.range n) a b⟫_ℝ =
      Real.exp (-|energy a b n - energy a b m| / 8) := by
  rw [blockRootLp_inner_of_subset (Finset.range_mono hmn),
    Finset.sum_sdiff_eq_sub (Finset.range_mono hmn),
    abs_of_nonneg (sub_nonneg.mpr (energy_mono a b hmn))]
  rfl

lemma range_inner (a b : ℕ → ℝ) (m n : ℕ) :
    ⟪blockRootLp (Finset.range m) a b, blockRootLp (Finset.range n) a b⟫_ℝ =
      Real.exp (-|energy a b n - energy a b m| / 8) := by
  obtain h | h := le_total m n
  · exact range_inner_of_le a b h
  · rw [real_inner_comm, range_inner_of_le a b h, abs_sub_comm]

lemma range_affinity_tendsto_one (a b : ℕ → ℝ)
    (hs : Summable (fun n => (a n - b n) ^ 2)) :
    Tendsto (fun p : ℕ × ℕ =>
      ⟪blockRootLp (Finset.range p.1) a b, blockRootLp (Finset.range p.2) a b⟫_ℝ)
      atTop (𝓝 1) := by
  have hE : Tendsto (energy a b) atTop (𝓝 (∑' n, (a n - b n) ^ 2)) :=
    hs.hasSum.tendsto_sum_nat
  have hf : Tendsto (fun p : ℕ × ℕ => energy a b p.1) atTop
      (𝓝 (∑' n, (a n - b n) ^ 2)) := by
    rw [← prod_atTop_atTop_eq]
    exact hE.comp tendsto_fst
  have hg : Tendsto (fun p : ℕ × ℕ => energy a b p.2) atTop
      (𝓝 (∑' n, (a n - b n) ^ 2)) := by
    rw [← prod_atTop_atTop_eq]
    exact hE.comp tendsto_snd
  have hd : Tendsto (fun p : ℕ × ℕ => energy a b p.2 - energy a b p.1)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using hg.sub hf
  simp_rw [range_inner]
  simpa only [Function.comp_def, abs_zero, neg_zero, zero_div, Real.exp_zero] using
    Real.continuous_exp.continuousAt.tendsto.comp (hd.abs.neg.div_const 8)

theorem gaussian_absolutelyContinuous_of_summable (a b : ℕ → ℝ)
    (hs : Summable (fun n => (a n - b n) ^ 2)) : gaussianProduct a ≪ gaussianProduct b := by
  apply MeasureEquivalenceProductAffinity.product_absolutelyContinuous_of_affinity_tendsto_one
    (fun n => blockRootLp (Finset.range n) a b)
    (fun n => blockRootLp_unit (Finset.range n) a b) (range_affinity_tendsto_one a b hs)
  intro I s hsm
  obtain ⟨k, hk⟩ := I.exists_nat_subset_range
  apply eventually_atTop.mpr
  refine ⟨k, fun n hn => ?_⟩
  have hi : (∫ x in cylinder I s, (blockRootLp (Finset.range n) a b x) ^ 2
      ∂gaussianProduct b) = ∫ x in cylinder I s, blockRoot (Finset.range n) a b x ^ 2
      ∂gaussianProduct b := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (blockRootLp_coe (Finset.range n) a b)] with x hx
    rw [hx]
  rw [hi]
  exact block_cylinder_density (hk.trans (Finset.range_mono hn)) a b hsm

theorem gaussian_mutualAC_of_summable (a b : ℕ → ℝ)
    (hs : Summable (fun n => (a n - b n) ^ 2)) :
    gaussianProduct a ≪ gaussianProduct b ∧ gaussianProduct b ≪ gaussianProduct a := by
  exact ⟨gaussian_absolutelyContinuous_of_summable a b hs,
    gaussian_absolutelyContinuous_of_summable b a (hs.congr (fun n => by ring))⟩

def blockTest (I : Finset ℕ) (a b : ℕ → ℝ) : Set (ℕ → ℝ) :=
  {x | 1 ≤ blockRoot I a b x}

lemma measurableSet_blockTest (I : Finset ℕ) (a b : ℕ → ℝ) :
    MeasurableSet (blockTest I a b) :=
  measurableSet_le measurable_const (continuous_blockRoot I a b).measurable

lemma blockTest_error_Q (I : Finset ℕ) (a b : ℕ → ℝ) :
    gaussianProduct b (blockTest I a b) ≤
      ENNReal.ofReal (∫ x, blockRoot I a b x ∂gaussianProduct b) := by
  have hu := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (gaussian_product_block_memLp I a b)
  exact hu.measure_le_integral (ae_of_all _ (blockRoot_nonneg I a b)) (fun _ hx => hx)

lemma blockTest_error_P (I : Finset ℕ) (a b : ℕ → ℝ) :
    gaussianProduct a (blockTest I a b)ᶜ ≤
      ENNReal.ofReal (∫ x, blockRoot I a b x ∂gaussianProduct b) := by
  let s : Set (I → ℝ) := {y | 1 ≤ ∏ i : I, rootLikelihood (a i) (b i) (y i)}
  have hs : MeasurableSet s := by
    apply measurableSet_le measurable_const
    unfold rootLikelihood
    fun_prop
  have heq : gaussianProduct a (blockTest I a b)ᶜ =
      ENNReal.ofReal (∫ x in (blockTest I a b)ᶜ, blockRoot I a b x ^ 2
        ∂gaussianProduct b) :=
    (block_cylinder_density (I := I) (J := I) (by rfl) a b hs.compl).symm
  rw [heq]
  apply ENNReal.ofReal_le_ofReal
  have hu := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (gaussian_product_block_memLp I a b)
  calc
    _ ≤ ∫ x in (blockTest I a b)ᶜ, blockRoot I a b x ∂gaussianProduct b := by
      apply setIntegral_mono_on (gaussian_product_block_memLp I a b).integrable_sq.restrict
        hu.restrict (measurableSet_blockTest I a b).compl
      intro x hx
      have hx' : blockRoot I a b x ≤ 1 := le_of_lt (lt_of_not_ge hx)
      simpa only [pow_two, mul_one] using
        mul_le_mul_of_nonneg_left hx' (blockRoot_nonneg I a b x)
    _ ≤ _ := integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ (blockRoot_nonneg I a b)) hu

lemma gaussian_affinity_tendsto_zero_of_not_summable (a b : ℕ → ℝ)
    (hs : ¬Summable (fun n => (a n - b n) ^ 2)) :
    Tendsto (fun n => Real.exp (-energy a b n / 8)) atTop (𝓝 0) := by
  have hV : Tendsto (energy a b) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => sq_nonneg (a n - b n))).mp hs
  exact Real.tendsto_exp_atBot.comp
    (Filter.Tendsto.atBot_div_const (by norm_num : (0 : ℝ) < 8)
      (tendsto_neg_atTop_atBot.comp hV))

theorem gaussian_mutuallySingular_of_not_summable (a b : ℕ → ℝ)
    (hs : ¬Summable (fun n => (a n - b n) ^ 2)) :
    gaussianProduct a ⟂ₘ gaussianProduct b := by
  have ht := gaussian_affinity_tendsto_zero_of_not_summable a b hs
  have hex : ∀ k : ℕ, ∃ n : ℕ, Real.exp (-energy a b n / 8) ≤ (1 / 2 : ℝ) ^ k := by
    intro k
    obtain ⟨n, hn⟩ := ((tendsto_order.mp ht).2 ((1 / 2 : ℝ) ^ k)
      (pow_pos (by norm_num) k)).exists
    exact ⟨n, hn.le⟩
  choose N hN using hex
  let A : ℕ → Set (ℕ → ℝ) := fun k => blockTest (Finset.range (N k)) a b
  have hA : ∀ k, MeasurableSet (A k) := fun k => measurableSet_blockTest _ a b
  have hint (k : ℕ) : ENNReal.ofReal
      (∫ x, blockRoot (Finset.range (N k)) a b x ∂gaussianProduct b) ≤
      (2⁻¹ : ℝ≥0∞) ^ k := by
    rw [gaussian_product_block_affinity,
      Finset.sum_coe_sort (Finset.range (N k)) (fun i : ℕ => (a i - b i) ^ 2)]
    calc
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := ENNReal.ofReal_le_ofReal (hN k)
      _ = _ := by simp [ENNReal.inv_pow]
  have hQ : (∑' k, gaussianProduct b (A k)) ≠ ∞ := by
    apply ne_top_of_le_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    calc
      _ ≤ ∑' k, (2⁻¹ : ℝ≥0∞) ^ k := ENNReal.tsum_le_tsum
        (fun k => (blockTest_error_Q _ a b).trans (hint k))
      _ = 2 := ENNReal.tsum_geometric_two
  have hP : (∑' k, gaussianProduct a (A k)ᶜ) ≠ ∞ := by
    apply ne_top_of_le_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    calc
      _ ≤ ∑' k, (2⁻¹ : ℝ≥0∞) ^ k := ENNReal.tsum_le_tsum
        (fun k => (blockTest_error_P _ a b).trans (hint k))
      _ = 2 := ENNReal.tsum_geometric_two
  exact (MeasureEquivalenceProductAffinity.mutuallySingular_of_summable_tests A hA hQ hP).symm

theorem gaussian_absolutelyContinuous_iff_summable (a b : ℕ → ℝ) :
    gaussianProduct a ≪ gaussianProduct b ↔ Summable (fun n => (a n - b n) ^ 2) := by
  refine ⟨fun hac => ?_, gaussian_absolutelyContinuous_of_summable a b⟩
  by_contra hs
  have hz := Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular hac
    (gaussian_mutuallySingular_of_not_summable a b hs)
  have hm := congrArg (fun μ : Measure (ℕ → ℝ) => μ Set.univ) hz
  simp at hm

theorem gaussian_mutualAC_iff_summable (a b : ℕ → ℝ) :
    (gaussianProduct a ≪ gaussianProduct b ∧ gaussianProduct b ≪ gaussianProduct a) ↔
      Summable (fun n => (a n - b n) ^ 2) :=
  ⟨fun h => (gaussian_absolutelyContinuous_iff_summable a b).mp h.1,
    gaussian_mutualAC_of_summable a b⟩

end MeasureEquivalenceGaussian

#print axioms MeasureEquivalenceGaussian.block_cylinder_density
#print axioms MeasureEquivalenceGaussian.blockRootLp_inner_of_subset
#print axioms MeasureEquivalenceGaussian.gaussian_mutualAC_of_summable
#print axioms MeasureEquivalenceGaussian.gaussian_mutuallySingular_of_not_summable
#print axioms MeasureEquivalenceGaussian.gaussian_mutualAC_iff_summable
