import SumFiberCoordinates

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

theorem exists_sum_event_of_zeroSum_invariant
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ] (n : ℕ)
    (E : Set ((Fin (n + 1) → ℝ) × α)) (hE : MeasurableSet E)
    (hinv : ∀ q : Fin (n + 1) → ℚ, (∑ i, q i) = 0 →
      (fun z : (Fin (n + 1) → ℝ) × α => (z.1 + fun i => (q i : ℝ), z.2)) ⁻¹' E
        =ᵐ[(volume : Measure (Fin (n + 1) → ℝ)).prod μ] E) :
    ∃ A : Set (ℝ × α), MeasurableSet A ∧ E =ᵐ[(volume : Measure (Fin (n + 1) → ℝ)).prod μ]
      (fun z => (∑ i, z.1 i, z.2)) ⁻¹' A := by
  let e := sumFiberEquiv n α
  let F := e.symm ⁻¹' E
  have hF : MeasurableSet F := e.symm.measurable hE
  have hm := measurePreserving_sumFiberEquiv n μ
  have hFinv (q : Fin n → ℚ) :
      (fun z : (ℝ × α) × (Fin n → ℝ) => (z.1, z.2 + fun i => (q i : ℝ))) ⁻¹' F
        =ᵐ[((volume : Measure ℝ).prod μ).prod volume] F := by
    let r : Fin (n + 1) → ℚ := Fin.cons (-∑ i, q i) q
    have hr : (∑ i, r i) = 0 := by simp [r, Fin.sum_univ_succ]
    have he (z : (ℝ × α) × (Fin n → ℝ)) :
        (e.symm z).1 + (fun i => (r i : ℝ)) =
          (e.symm (z.1, z.2 + fun i => (q i : ℝ))).1 := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [e, sumFiberEquiv_symm_apply, r, Pi.add_apply, Finset.sum_add_distrib]
        push_cast
        ring
      · simp [e, sumFiberEquiv_symm_apply, r, Pi.add_apply]
    have hh := (hm.symm e).quasiMeasurePreserving.ae (hinv r hr)
    filter_upwards [hh] with z hz
    change E (e.symm (z.1, z.2 + fun i => (q i : ℝ))) = E (e.symm z)
    change E ((e.symm z).1 + (fun i => (r i : ℝ)), (e.symm z).2) = E (e.symm z) at hz
    rw [he] at hz
    exact hz
  obtain ⟨A, hA, hFA⟩ := exists_base_event_of_rational_fiber_invariant
    ((volume : Measure ℝ).prod μ) n F hF hFinv
  refine ⟨A, hA, ?_⟩
  have hh := hm.quasiMeasurePreserving.ae_eq hFA
  filter_upwards [hh] with z hz
  change E (e.symm (e z)) = A (e z).1 at hz
  rw [e.symm_apply_apply] at hz
  exact hz

theorem finite_permutation_invariant_of_zeroSum_invariant
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ] (n : ℕ)
    (E : Set ((Fin (n + 1) → ℝ) × α)) (hE : MeasurableSet E)
    (hinv : ∀ q : Fin (n + 1) → ℚ, (∑ i, q i) = 0 →
      (fun z : (Fin (n + 1) → ℝ) × α => (z.1 + fun i => (q i : ℝ), z.2)) ⁻¹' E
        =ᵐ[(volume : Measure (Fin (n + 1) → ℝ)).prod μ] E)
    (p : Equiv.Perm (Fin (n + 1))) :
    (fun z : (Fin (n + 1) → ℝ) × α => (fun i => z.1 (p i), z.2)) ⁻¹' E
      =ᵐ[(volume : Measure (Fin (n + 1) → ℝ)).prod μ] E := by
  obtain ⟨A, hA, he⟩ := exists_sum_event_of_zeroSum_invariant μ n E hE hinv
  have hp : MeasurePreserving
      (fun z : (Fin (n + 1) → ℝ) × α => (fun i => z.1 (p i), z.2))
      ((volume : Measure (Fin (n + 1) → ℝ)).prod μ)
      ((volume : Measure (Fin (n + 1) → ℝ)).prod μ) := by
    convert (volume_measurePreserving_piCongrLeft (fun _ : Fin (n + 1) => ℝ) p.symm).prod
        (MeasurePreserving.id μ) using 1
    funext z
    apply Prod.ext
    · funext i
      simp [Prod.map, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    · rfl
  have hh := hp.quasiMeasurePreserving.ae_eq he
  filter_upwards [hh, he] with z hz hz'
  change E (fun i => z.1 (p i), z.2) = A (∑ i, z.1 (p i), z.2) at hz
  change E z = A (∑ i, z.1 i, z.2) at hz'
  change E (fun i => z.1 (p i), z.2) = E z
  rw [hz, hz']
  congr 2
  exact Equiv.sum_comp p z.1

end MeasureEquivalenceRestrictedProduct

#print axioms MeasureEquivalenceRestrictedProduct.exists_sum_event_of_zeroSum_invariant
#print axioms MeasureEquivalenceRestrictedProduct.finite_permutation_invariant_of_zeroSum_invariant
