import RationalFiberErgodic
import RestrictedFiniteNull

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

/-- A measurable event which is constant on almost every fiber has a measurable base event.
The probability measure `ρ` is only a device for choosing the value on each fiber. -/
theorem exists_base_event_of_ae_fiber_const
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν ρ : Measure β) [SFinite μ] [SFinite ν] [IsProbabilityMeasure ρ]
    (hρ : ρ ≪ ν) (E : Set (α × β)) (hE : MeasurableSet E)
    (hc : ∀ᵐ x ∂μ, EventuallyConst (Prod.mk x ⁻¹' E) (ae ν)) :
    ∃ A : Set α, MeasurableSet A ∧ E =ᵐ[μ.prod ν] Prod.fst ⁻¹' A := by
  let A : Set α := {x | ρ (Prod.mk x ⁻¹' E) = 1}
  have hA : MeasurableSet A :=
    (measurable_measure_prodMk_left hE) (measurableSet_singleton 1)
  refine ⟨A, hA, ?_⟩
  change ∀ᵐ z ∂μ.prod ν, E z = (z.1 ∈ A)
  simp only [eq_iff_iff]
  apply (Measure.ae_prod_iff_ae_ae (hE.iff (measurable_fst hA))).2
  filter_upwards [hc] with x hx
  rcases eventuallyConst_set.mp hx with hx | hx
  · have hp : ρ (Prod.mk x ⁻¹' E) = 1 := by
      exact (mem_ae_iff_prob_eq_one (measurable_prodMk_left hE)).mp (hρ.ae_le hx)
    filter_upwards [hx] with y hy
    exact ⟨fun _ => hp, fun _ => hy⟩
  · have hp : ρ (Prod.mk x ⁻¹' E) = 0 := by
      have hz := mem_ae_iff.mp (hρ.ae_le hx)
      have he : {y | y ∉ Prod.mk x ⁻¹' E}ᶜ = Prod.mk x ⁻¹' E := by ext y; simp
      rw [he] at hz
      exact hz
    have hn : x ∉ A := by change ρ (Prod.mk x ⁻¹' E) ≠ 1; rw [hp]; exact zero_ne_one
    filter_upwards [hx] with y hy
    exact ⟨fun he => (hy he).elim, fun ha => (hn ha).elim⟩

theorem ae_fiber_const_of_rational_invariant
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ] (n : ℕ)
    (E : Set (α × (Fin n → ℝ))) (hE : MeasurableSet E)
    (hinv : ∀ q : Fin n → ℚ,
      (fun z : α × (Fin n → ℝ) => (z.1, z.2 + fun i => (q i : ℝ))) ⁻¹' E
        =ᵐ[μ.prod volume] E) :
    ∀ᵐ x ∂μ, EventuallyConst (Prod.mk x ⁻¹' E) (ae volume) := by
  have hh : ∀ q : Fin n → ℚ, ∀ᵐ x ∂μ, ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)),
      E (x, y + fun i => (q i : ℝ)) = E (x, y) := fun q =>
    Measure.ae_ae_of_ae_prod (hinv q)
  have hall : ∀ᵐ x ∂μ, ∀ q : Fin n → ℚ, ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)),
      E (x, y + fun i => (q i : ℝ)) = E (x, y) := ae_all_iff.mpr hh
  filter_upwards [hall] with x hx
  exact finite_real_aeconst_of_rational_invariant n (Prod.mk x ⁻¹' E)
    (measurable_prodMk_left hE) hx

theorem finite_base_ac_volume (n : ℕ) :
    Measure.pi (fun _ : Fin n => baseMeasure) ≪ (volume : Measure (Fin n → ℝ)) := by
  have he : Measure.pi (fun _ : Fin n => baseMeasure) =
      (Measure.pi (fun _ : Fin n => exponentialMeasure)).restrict
        (univ.pi (fun _ => baseInterval)) :=
    (Measure.restrict_pi_pi (fun _ : Fin n => exponentialMeasure) (fun _ => baseInterval)).symm
  rw [he]
  exact Measure.restrict_le_self.absolutelyContinuous.trans (finite_exponential_ac_volume n)

theorem exists_base_event_of_rational_fiber_invariant
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ] (n : ℕ)
    (E : Set (α × (Fin n → ℝ))) (hE : MeasurableSet E)
    (hinv : ∀ q : Fin n → ℚ,
      (fun z : α × (Fin n → ℝ) => (z.1, z.2 + fun i => (q i : ℝ))) ⁻¹' E
        =ᵐ[μ.prod volume] E) :
    ∃ A : Set α, MeasurableSet A ∧ E =ᵐ[μ.prod volume] Prod.fst ⁻¹' A :=
  exists_base_event_of_ae_fiber_const μ volume (Measure.pi (fun _ : Fin n => baseMeasure))
    (finite_base_ac_volume n) E hE (ae_fiber_const_of_rational_invariant μ n E hE hinv)

end MeasureEquivalenceRestrictedProduct

#print axioms MeasureEquivalenceRestrictedProduct.exists_base_event_of_ae_fiber_const
#print axioms MeasureEquivalenceRestrictedProduct.ae_fiber_const_of_rational_invariant
#print axioms MeasureEquivalenceRestrictedProduct.exists_base_event_of_rational_fiber_invariant
