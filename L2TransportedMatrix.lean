import L2LocalizedOperators

/-! Actual transported matrix operators: Koopman transport of genuine
restricted-space coefficients gives ambient module operators supported
on the translated finite sets, and hence genuine finite-local multipliers. -/

open MeasureTheory Filter Set
open scoped ENNReal

namespace MeasureEquivalenceL2Transport

open MeasureEquivalenceL2Restriction MeasureEquivalenceEquidecomposition MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def pullbackEquiv (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  pullbackUnitary μ μ e e.symm he he.symm
    (Eventually.of_forall (fun x => e.symm_apply_apply x))

theorem pullback_coe (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (f : Lp ℂ 2 μ) :
    pullbackEquiv μ e he f =ᵐ[μ] fun x => f (e x) :=
  Lp.coeFn_compMeasurePreserving f he

theorem pullback_indicator (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    pullbackEquiv μ e he (indicatorL2 μ hs f) =
      indicatorL2 μ (hs.preimage e.measurable) (pullbackEquiv μ e he f) := by
  apply Lp.ext
  filter_upwards [pullback_coe μ e he (indicatorL2 μ hs f), pullback_coe μ e he f,
    he.quasiMeasurePreserving.ae (indicatorL2_coe μ hs f),
    indicatorL2_coe μ (hs.preimage e.measurable) (pullbackEquiv μ e he f)]
    with x hp hf hi ho
  rw [hp, hi, ho]
  by_cases hx : e x ∈ s <;> simp [hx, hf]

theorem preimage_symm_eq_image (e : X ≃ᵐ X) (A : Set X) : e.symm ⁻¹' A = e '' A := by
  ext x
  constructor
  · intro hx
    exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [mem_preimage, MeasurableEquiv.symm_apply_apply] using hy

theorem measure_image (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (A : Set X) (hA : MeasurableSet A) : μ (e '' A) = μ A := by
  rw [← preimage_symm_eq_image]
  exact he.symm.measure_preimage hA.nullMeasurableSet

def transportedOperator (d e : X ≃ᵐ X) (hd : MeasurePreserving d μ μ)
    (he : MeasurePreserving e μ μ) (A B : Set X) (hB : MeasurableSet B)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B)) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (pullbackEquiv μ d.symm hd.symm).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((globalizeOperator μ A B hB T).comp
      (pullbackEquiv μ e he).toContinuousLinearEquiv.toContinuousLinearMap)

theorem globalize_twisted_indicator (d e : X ≃ᵐ X)
    (A B : Set X) (hB : MeasurableSet B)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B))
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (μ.restrict A)),
      T (indicatorL2 (μ.restrict A) (hs.preimage e.measurable) f) =
        indicatorL2 (μ.restrict B) (hs.preimage d.measurable) (T f))
    (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    globalizeOperator μ A B hB T (indicatorL2 μ (hs.preimage e.measurable) f) =
      indicatorL2 μ (hs.preimage d.measurable) (globalizeOperator μ A B hB T f) := by
  change zeroExtend μ B hB (T (restrictMap μ A (indicatorL2 μ (hs.preimage e.measurable) f))) =
    indicatorL2 μ (hs.preimage d.measurable) (zeroExtend μ B hB (T (restrictMap μ A f)))
  rw [restrict_indicator, hT s hs, zeroExtend_indicator]

theorem transported_commutes_indicator (d e : X ≃ᵐ X)
    (hd : MeasurePreserving d μ μ) (he : MeasurePreserving e μ μ)
    (A B : Set X) (hB : MeasurableSet B)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B))
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (μ.restrict A)),
      T (indicatorL2 (μ.restrict A) (hs.preimage e.measurable) f) =
        indicatorL2 (μ.restrict B) (hs.preimage d.measurable) (T f))
    (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    transportedOperator μ d e hd he A B hB T (indicatorL2 μ hs f) =
      indicatorL2 μ hs (transportedOperator μ d e hd he A B hB T f) := by
  change pullbackEquiv μ d.symm hd.symm
      (globalizeOperator μ A B hB T (pullbackEquiv μ e he (indicatorL2 μ hs f))) =
    indicatorL2 μ hs (pullbackEquiv μ d.symm hd.symm
      (globalizeOperator μ A B hB T (pullbackEquiv μ e he f)))
  rw [pullback_indicator, globalize_twisted_indicator μ d e A B hB T hT s hs,
    pullback_indicator]
  have hset : d.symm ⁻¹' (d ⁻¹' s) = s := by
    ext x
    simp only [mem_preimage, MeasurableEquiv.apply_symm_apply]
  simp only [hset]

theorem transported_input_supported (d e : X ≃ᵐ X)
    (hd : MeasurePreserving d μ μ) (he : MeasurePreserving e μ μ)
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B)) (f : Lp ℂ 2 μ) :
    transportedOperator μ d e hd he A B hB T
      (indicatorL2 μ (e.measurableEmbedding.measurableSet_image.mpr hA) f) =
        transportedOperator μ d e hd he A B hB T f := by
  change pullbackEquiv μ d.symm hd.symm
      (globalizeOperator μ A B hB T (pullbackEquiv μ e he
        (indicatorL2 μ (e.measurableEmbedding.measurableSet_image.mpr hA) f))) =
    pullbackEquiv μ d.symm hd.symm (globalizeOperator μ A B hB T (pullbackEquiv μ e he f))
  rw [pullback_indicator]
  have hset : e ⁻¹' (e '' A) = A := Set.preimage_image_eq _ e.injective
  simp only [hset]
  rw [globalize_input_supported μ A B hA hB T]

theorem transported_output_supported (d e : X ≃ᵐ X)
    (hd : MeasurePreserving d μ μ) (he : MeasurePreserving e μ μ)
    (A B : Set X) (hB : MeasurableSet B)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B)) (f : Lp ℂ 2 μ) :
    indicatorL2 μ (d.measurableEmbedding.measurableSet_image.mpr hB)
      (transportedOperator μ d e hd he A B hB T f) =
        transportedOperator μ d e hd he A B hB T f := by
  have h := congrArg (pullbackEquiv μ d.symm hd.symm)
    (globalize_output_supported μ A B hB T (pullbackEquiv μ e he f))
  rw [pullback_indicator] at h
  simpa only [preimage_symm_eq_image] using h

theorem exists_transported_local_multiplier (d e : X ≃ᵐ X)
    (hd : MeasurePreserving d μ μ) (he : MeasurePreserving e μ μ)
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : μ A ≠ ∞) (hfinB : μ B ≠ ∞)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B))
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (μ.restrict A)),
      T (indicatorL2 (μ.restrict A) (hs.preimage e.measurable) f) =
        indicatorL2 (μ.restrict B) (hs.preimage d.measurable) (T f)) :
    ∃ b : Lp ℂ ∞ (μ.restrict (e '' A ∪ d '' B)),
      localizeOperator μ (e '' A ∪ d '' B)
        ((e.measurableEmbedding.measurableSet_image.mpr hA).union
          (d.measurableEmbedding.measurableSet_image.mpr hB))
        (transportedOperator μ d e hd he A B hB T) =
          boundedMultiplierL2 (μ.restrict (e '' A ∪ d '' B)) b := by
  have hmC : MeasurableSet (e '' A ∪ d '' B) :=
    (e.measurableEmbedding.measurableSet_image.mpr hA).union
      (d.measurableEmbedding.measurableSet_image.mpr hB)
  have hfC : μ (e '' A ∪ d '' B) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (measure_union_le _ _)
    rw [measure_image μ e he A hA, measure_image μ d hd B hB]
    exact ENNReal.add_ne_top.mpr ⟨hfinA,hfinB⟩
  exact exists_localized_multiplier μ _ hmC hfC _
    (transported_commutes_indicator μ d e hd he A B hB T hT)

end
end MeasureEquivalenceL2Transport

#print axioms MeasureEquivalenceL2Transport.transported_commutes_indicator
#print axioms MeasureEquivalenceL2Transport.transported_input_supported
#print axioms MeasureEquivalenceL2Transport.transported_output_supported
#print axioms MeasureEquivalenceL2Transport.exists_transported_local_multiplier
