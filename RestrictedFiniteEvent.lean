import ZeroSumFiberEvent
import RestrictedPropagation

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

theorem head_event_zeroSum_invariant (N : ℕ)
    (E : Set RealSequences) (hE : MeasurableSet E)
    (hinv : ∀ q : rationalZeroSumGroup,
      (rationalTranslation q) ⁻¹' E =ᵐ[restrictedProductMeasure] E)
    (r : Fin N → ℚ) (hr : (∑ i, r i) = 0) :
    (fun z : (Fin N → ℝ) × RealSequences =>
      (z.1 + fun i => (r i : ℝ), z.2)) ⁻¹' ((headTailEquiv N).symm ⁻¹' E)
      =ᵐ[(volume : Measure (Fin N → ℝ)).prod tailProbability]
        (headTailEquiv N).symm ⁻¹' E := by
  let q : rationalZeroSumGroup := ⟨headFinsupp N r, by
    change rationalTotal (headFinsupp N r) = 0
    rw [rationalTotal_headFinsupp, hr]⟩
  have hstage : stageMeasure N ≪ restrictedProductMeasure := by
    rw [← restrictedProductMeasure_restrict N]
    exact Measure.restrict_le_self.absolutelyContinuous
  have hm : MeasurePreserving (headTailEquiv N).symm
      ((Measure.pi (fun _ : Fin N => exponentialMeasure)).prod tailProbability) (stageMeasure N) :=
    ⟨(headTailEquiv N).symm.measurable, rfl⟩
  have hh := hm.quasiMeasurePreserving.ae_eq (hstage.ae_eq (hinv q))
  have hzero : ∀ᵐ z ∂(Measure.pi (fun _ : Fin N => exponentialMeasure)).prod tailProbability,
      E ((headTailEquiv N).symm (z.1 + fun i => (r i : ℝ), z.2)) =
        E ((headTailEquiv N).symm z) := by
    filter_upwards [hh] with z hz
    change E (rationalTranslation q ((headTailEquiv N).symm z)) =
      E ((headTailEquiv N).symm z) at hz
    have he : rationalTranslation q ((headTailEquiv N).symm z) =
        (headTailEquiv N).symm (z.1 + fun i => (r i : ℝ), z.2) := by
      apply (headTailEquiv N).injective
      apply Prod.ext
      · funext i
        simp only [headTailEquiv_head, rationalTranslation, Pi.add_apply,
          rationalRealShift, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
          headTailEquiv_symm_head, MeasurableEquiv.apply_symm_apply]
        exact congrArg (fun a : ℚ => z.1 i + (a : ℝ)) (headFinsupp_head N r i)
      · funext k
        simp only [headTailEquiv_tail, rationalTranslation, Pi.add_apply,
          rationalRealShift, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
          headTailEquiv_symm_tail, MeasurableEquiv.apply_symm_apply]
        have heq := headFinsupp_tail N r (N + k) (by omega)
        change z.2 k + (headFinsupp N r (N + k) : ℝ) = z.2 k
        rw [heq, Rat.cast_zero, add_zero]
    rw [he] at hz
    exact hz
  exact ((finite_volume_ac_exponential N).prod Measure.AbsolutelyContinuous.rfl).ae_eq hzero

end MeasureEquivalenceRestrictedProduct

#print axioms MeasureEquivalenceRestrictedProduct.head_event_zeroSum_invariant
