import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Data.Real.Basic

/-!
The countable-roots step in the manuscript's quasi-invariance rigidity argument.

This module is a helper for Theorems 1.3 and 1.4. It does not assert the
ergodic decomposition, affinity estimate, or representation construction.
The hypotheses below are precisely the quantitative component estimates
needed after those analytic steps have been established.
-/

open Filter MeasureTheory
open scoped Topology ENNReal

namespace MeasureEquivalenceRigidity

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}

/-- A bounded component affinity that vanishes on the bad set bounds its
probability by its mean deficit. This uses actual Bochner integrals and
the actual measure of the bad set. -/
theorem measureReal_bad_set_le_of_mean_affinity
    [IsProbabilityMeasure μ] (A : Y → ℝ) (B : Set Y)
    (hB : MeasurableSet B) (hA : Integrable A μ)
    (hA_le : ∀ᵐ y ∂μ, A y ≤ 1)
    (hzero : ∀ᵐ y ∂μ, y ∈ B → A y = 0)
    (ε : ℝ) (hmean : 1 - ε ≤ ∫ y, A y ∂μ) :
    μ.real B ≤ ε := by
  have hI : Integrable (B.indicator (fun _ : Y => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB
  have hdef : Integrable (fun y => 1 - A y) μ :=
    (integrable_const (1 : ℝ)).sub hA
  have hcomp : B.indicator (fun _ : Y => (1 : ℝ)) ≤ᵐ[μ] fun y => 1 - A y := by
    filter_upwards [hA_le, hzero] with y hy hz
    by_cases hmem : y ∈ B
    · simp [Set.indicator_of_mem hmem, hz hmem]
    · simp only [Set.indicator_of_notMem hmem]
      exact sub_nonneg.mpr hy
  have hle := integral_mono_ae hI hdef hcomp
  rw [integral_indicator_const (1 : ℝ) hB,
    integral_sub (integrable_const (1 : ℝ)) hA] at hle
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hle
  linarith

/-- In particular, the zero set of a measurable affinity in `[0,1]`
has measure bounded by the deficit in the mean affinity. -/
theorem measureReal_affinity_zero_set_le
    [IsProbabilityMeasure μ] (A : Y → ℝ) (hA : Measurable A)
    (hA_nonneg : ∀ y, 0 ≤ A y) (hA_le : ∀ y, A y ≤ 1)
    (ε : ℝ) (hmean : 1 - ε ≤ ∫ y, A y ∂μ) :
    μ.real {y | A y = 0} ≤ ε := by
  apply measureReal_bad_set_le_of_mean_affinity A _
    (hA (measurableSet_singleton 0)) _
    (Eventually.of_forall hA_le) (Eventually.of_forall (fun _ h => h)) ε hmean
  exact Integrable.mono' (integrable_const (1 : ℝ)) hA.aestronglyMeasurable
    (Eventually.of_forall (fun y => by simpa [abs_of_nonneg (hA_nonneg y)] using hA_le y))

/-- A set bounded in measure by a sequence tending to zero is null.
No measurability of the set is needed, since the assertion uses outer measure. -/
theorem measure_eq_zero_of_le_vanishing
    (B : Set Y) (ε : ℕ → ℝ≥0∞)
    (hbound : ∀ n, μ B ≤ ε n)
    (hε : Tendsto ε atTop (𝓝 0)) : μ B = 0 := by
  apply le_antisymm
  · exact ge_of_tendsto hε (Filter.Eventually.of_forall hbound)
  · exact bot_le

variable {K : Type*} [AddCommGroup K]

omit [MeasurableSpace Y] in
/-- Failure of membership in an additive subgroup implies failure for
every specified root. This is the bad-set inclusion used in the paper. -/
theorem bad_set_subset_root_bad_set
    (S : Y → AddSubgroup K) (x z : K) (m : ℕ)
    (hroot : m • z = x) :
    {y | x ∉ S y} ⊆ {y | z ∉ S y} := by
  intro y hy hz
  exact hy (hroot ▸ (S y).nsmul_mem hz m)

/-- If each root has a vanishing bad-set measure, the original element
belongs to the component subgroups almost everywhere. The roots may
vary with the component only through the subgroup, not through a choice
of a component-dependent exceptional set. -/
theorem ae_mem_of_root_bad_set_bound
    (S : Y → AddSubgroup K) (x : K) (root : ℕ → K)
    (multiplicity : ℕ → ℕ)
    (hroot : ∀ n, multiplicity n • root n = x)
    (ε : ℕ → ℝ≥0∞)
    (hbound : ∀ n, μ {y | root n ∉ S y} ≤ ε n)
    (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ᵐ y ∂μ, x ∈ S y := by
  rw [ae_iff]
  apply measure_eq_zero_of_le_vanishing _ ε _ hε
  intro n
  exact (measure_mono
    (bad_set_subset_root_bad_set S x (root n) (multiplicity n) (hroot n))).trans
      (hbound n)

/-- The concrete roots `g (a / (n+1))` of `g a` used in the manuscript.
The map `g` is an actual additive homomorphism from the real line. -/
theorem ae_mem_of_real_root_bad_set_bound
    (g : ℝ →+ K) (S : Y → AddSubgroup K) (a : ℝ)
    (ε : ℕ → ℝ≥0∞)
    (hbound : ∀ n, μ {y | g (a / ((n + 1 : ℕ) : ℝ)) ∉ S y} ≤ ε n)
    (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ᵐ y ∂μ, g a ∈ S y := by
  apply ae_mem_of_root_bad_set_bound S (g a)
    (fun n => g (a / ((n + 1 : ℕ) : ℝ))) (fun n => n + 1) _ ε hbound hε
  intro n
  rw [← map_nsmul, nsmul_eq_mul]
  congr 1
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  exact mul_div_cancel₀ a hn

/-- The roots step with its analytic input expressed as mean affinities,
rather than an assumed bad-set measure bound. Each component affinity
lies in `[0,1]` and vanishes whenever the root misses its component
subgroup. Their mean deficits tend to zero. The conclusion is actual
almost-everywhere membership of the original element. -/
theorem ae_mem_of_root_mean_affinity
    [IsProbabilityMeasure μ]
    (S : Y → AddSubgroup K) (x : K) (root : ℕ → K)
    (multiplicity : ℕ → ℕ)
    (hroot : ∀ n, multiplicity n • root n = x)
    (A : ℕ → Y → ℝ)
    (hbad : ∀ n, MeasurableSet {y | root n ∉ S y})
    (hA : ∀ n, Measurable (A n))
    (hA_nonneg : ∀ n y, 0 ≤ A n y)
    (hA_le : ∀ n y, A n y ≤ 1)
    (hzero : ∀ n, ∀ᵐ y ∂μ, root n ∉ S y → A n y = 0)
    (ε : ℕ → ℝ)
    (hmean : ∀ n, 1 - ε n ≤ ∫ y, A n y ∂μ)
    (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ᵐ y ∂μ, x ∈ S y := by
  have hbound : ∀ n, μ.real {y | root n ∉ S y} ≤ ε n := by
    intro n
    apply measureReal_bad_set_le_of_mean_affinity (A n) _ (hbad n) _
      (Eventually.of_forall (hA_le n)) (hzero n) (ε n) (hmean n)
    exact Integrable.mono' (integrable_const (1 : ℝ)) (hA n).aestronglyMeasurable
      (Eventually.of_forall (fun y => by
        simpa [abs_of_nonneg (hA_nonneg n y)] using hA_le n y))
  rw [ae_iff]
  apply (measureReal_eq_zero_iff).mp
  apply le_antisymm
  · apply ge_of_tendsto hε
    apply Eventually.of_forall
    intro n
    exact (measureReal_mono
      (bad_set_subset_root_bad_set S x (root n) (multiplicity n) (hroot n))).trans
        (hbound n)
  · exact measureReal_nonneg

/-- Concrete real-line form of the affinity roots argument. In the
manuscript `S y` is the quasi-invariance subgroup of the conditional
ergodic measure, and `A n y` is its affinity with its translate by the
`(n+1)`st root of `g a`. -/
theorem ae_mem_of_real_root_mean_affinity
    [IsProbabilityMeasure μ]
    (g : ℝ →+ K) (S : Y → AddSubgroup K) (a : ℝ)
    (A : ℕ → Y → ℝ)
    (hbad : ∀ n, MeasurableSet {y | g (a / ((n + 1 : ℕ) : ℝ)) ∉ S y})
    (hA : ∀ n, Measurable (A n))
    (hA_nonneg : ∀ n y, 0 ≤ A n y)
    (hA_le : ∀ n y, A n y ≤ 1)
    (hzero : ∀ n, ∀ᵐ y ∂μ, g (a / ((n + 1 : ℕ) : ℝ)) ∉ S y → A n y = 0)
    (ε : ℕ → ℝ)
    (hmean : ∀ n, 1 - ε n ≤ ∫ y, A n y ∂μ)
    (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ᵐ y ∂μ, g a ∈ S y := by
  apply ae_mem_of_root_mean_affinity S (g a)
    (fun n => g (a / ((n + 1 : ℕ) : ℝ))) (fun n => n + 1) _ A
    hbad hA hA_nonneg hA_le hzero ε hmean hε
  intro n
  rw [← map_nsmul, nsmul_eq_mul]
  congr 1
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  exact mul_div_cancel₀ a hn

end MeasureEquivalenceRigidity

#print axioms MeasureEquivalenceRigidity.measure_eq_zero_of_le_vanishing
#print axioms MeasureEquivalenceRigidity.ae_mem_of_root_bad_set_bound
#print axioms MeasureEquivalenceRigidity.ae_mem_of_real_root_bad_set_bound
#print axioms MeasureEquivalenceRigidity.measureReal_bad_set_le_of_mean_affinity
#print axioms MeasureEquivalenceRigidity.measureReal_affinity_zero_set_le
#print axioms MeasureEquivalenceRigidity.ae_mem_of_root_mean_affinity
#print axioms MeasureEquivalenceRigidity.ae_mem_of_real_root_mean_affinity
