import DensitySquare
import DensityExtension
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! A positive affinity criterion with actual measures and L2 functions.
Unit-norm L2 approximations whose pairwise affinities tend to one are
Cauchy. If their squared densities match the target measure eventually
on a generating pi-system, the target is absolutely continuous.
No Gaussian instantiation or singular alternative is claimed here.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace

namespace MeasureEquivalenceProductAffinity

theorem cauchySeq_of_unit_inner_tendsto_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u : ℕ → E) (hunit : ∀ n, ‖u n‖ = 1)
    (haff : Tendsto (fun p : ℕ × ℕ => ⟪u p.1, u p.2⟫_ℝ) atTop (𝓝 1)) :
    CauchySeq u := by
  have hdist (p : ℕ × ℕ) :
      dist (u p.1) (u p.2) = Real.sqrt (2 - 2 * ⟪u p.1, u p.2⟫_ℝ) := by
    have hs : ‖u p.1 - u p.2‖ ^ 2 = 2 - 2 * ⟪u p.1, u p.2⟫_ℝ := by
      rw [norm_sub_sq_real, hunit, hunit]
      ring
    rw [← hs, Real.sqrt_sq (norm_nonneg _), dist_eq_norm]
  have hsq : Tendsto (fun p : ℕ × ℕ => 2 - 2 * ⟪u p.1, u p.2⟫_ℝ)
      atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_nhds.sub (haff.const_mul 2)) using 1
    norm_num
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have ht' := ht.congr' (Eventually.of_forall (fun p => (hdist p).symm))
  simpa only [Real.sqrt_zero] using ht'

variable {α : Type*} [m : MeasurableSpace α]
  {μ ν : Measure α} [IsFiniteMeasure ν]

theorem absolutelyContinuous_of_L2_cauchy_cylinder_densities
    (C : Set (Set α)) (hgen : m = MeasurableSpace.generateFrom C)
    (hpi : IsPiSystem C) (huniv : Set.univ ∈ C)
    (u : ℕ → Lp ℝ 2 μ) (hcauchy : CauchySeq u)
    (hmatch : ∀ s ∈ C, ∀ᶠ n in atTop,
      ENNReal.ofReal (∫ x in s, (u n x) ^ 2 ∂μ) = ν s) :
    ν ≪ μ := by
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hcauchy
  let f : ℕ → Lp ℝ 1 μ := fun n => MeasureEquivalenceDensity.square μ (u n)
  have hpos : ∀ n, 0 ≤ f n := by
    intro n
    apply (Lp.coeFn_nonneg (f n)).mp
    filter_upwards [MeasureEquivalenceDensity.square_coe μ (u n)] with x hx
    change 0 ≤ (MeasureEquivalenceDensity.square μ (u n)) x
    rw [hx]
    exact sq_nonneg _
  apply MeasureEquivalenceDensityExtension.absolutelyContinuous_of_L1_approx
    C hgen hpi huniv f (MeasureEquivalenceDensity.square μ g) hpos
    ((MeasureEquivalenceDensity.square_continuous μ).tendsto g |>.comp hg)
  intro s hs
  filter_upwards [hmatch s hs] with n hn
  have hi : (∫ x in s, f n x ∂μ) = ∫ x in s, (u n x) ^ 2 ∂μ :=
    integral_congr_ae (ae_restrict_of_ae (MeasureEquivalenceDensity.square_coe μ (u n)))
  rw [hi]
  exact hn

theorem absolutelyContinuous_of_affinity_tendsto_one
    (C : Set (Set α)) (hgen : m = MeasurableSpace.generateFrom C)
    (hpi : IsPiSystem C) (huniv : Set.univ ∈ C)
    (u : ℕ → Lp ℝ 2 μ) (hunit : ∀ n, ‖u n‖ = 1)
    (haff : Tendsto (fun p : ℕ × ℕ => ⟪u p.1, u p.2⟫_ℝ) atTop (𝓝 1))
    (hmatch : ∀ s ∈ C, ∀ᶠ n in atTop,
      ENNReal.ofReal (∫ x in s, (u n x) ^ 2 ∂μ) = ν s) :
    ν ≪ μ :=
  absolutelyContinuous_of_L2_cauchy_cylinder_densities C hgen hpi huniv u
    (cauchySeq_of_unit_inner_tendsto_one u hunit haff) hmatch

theorem product_absolutelyContinuous_of_affinity_tendsto_one
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {μ ν : Measure (∀ i, X i)} [IsFiniteMeasure ν]
    (u : ℕ → Lp ℝ 2 μ) (hunit : ∀ n, ‖u n‖ = 1)
    (haff : Tendsto (fun p : ℕ × ℕ => ⟪u p.1, u p.2⟫_ℝ) atTop (𝓝 1))
    (hmatch : ∀ (I : Finset ι) (s : Set (∀ i : I, X i)), MeasurableSet s →
      ∀ᶠ n in atTop,
        ENNReal.ofReal (∫ x in cylinder I s, (u n x) ^ 2 ∂μ) = ν (cylinder I s)) :
    ν ≪ μ := by
  apply absolutelyContinuous_of_affinity_tendsto_one (measurableCylinders X)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
    (univ_mem_measurableCylinders X) u hunit haff
  intro s hs
  obtain ⟨I, t, ht, rfl⟩ := (mem_measurableCylinders s).mp hs
  exact hmatch I t ht

theorem mutuallySingular_of_summable_tests
    {μ ν : Measure α} (A : ℕ → Set α) (hA : ∀ n, MeasurableSet (A n))
    (hμ : (∑' n, μ (A n)) ≠ ∞) (hν : (∑' n, ν (A n)ᶜ) ≠ ∞) :
    μ ⟂ₘ ν := by
  refine ⟨Filter.liminf A atTop, MeasurableSet.measurableSet_liminf hA,
    measure_liminf_atTop_eq_zero hμ, ?_⟩
  rw [Filter.liminf_compl]
  exact measure_limsup_atTop_eq_zero hν

end MeasureEquivalenceProductAffinity

#print axioms MeasureEquivalenceProductAffinity.cauchySeq_of_unit_inner_tendsto_one
#print axioms MeasureEquivalenceProductAffinity.absolutelyContinuous_of_affinity_tendsto_one
#print axioms MeasureEquivalenceProductAffinity.product_absolutelyContinuous_of_affinity_tendsto_one
#print axioms MeasureEquivalenceProductAffinity.mutuallySingular_of_summable_tests
