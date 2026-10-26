import L2CountInjections

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceL2Coefficients

open MeasureUnitary

variable {X Y D Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace D] [Countable D] [MeasurableSingletonClass D] [MeasurableSpace Z]
  (μ : Measure X) [SigmaFinite μ]

theorem coefficient_indicator (q : X × D → Z) (hq : Measurable q)
    (s : Set Z) (hs : MeasurableSet s) (d : D)
    (u : Lp ℂ 2 (μ.prod (Measure.count : Measure D))) :
    coefficient μ d (indicatorL2 (μ.prod Measure.count) (hq hs) u) =
      indicatorL2 μ ((hq.comp (measurable_id.prodMk (measurable_const (a := d)))) hs) (coefficient μ d u) := by
  apply Lp.ext
  filter_upwards [coefficient_coe μ d (indicatorL2 (μ.prod Measure.count) (hq hs) u),
    ae_slice_of_ae μ (indicatorL2_coe (μ.prod Measure.count) (hq hs) u) d,
    indicatorL2_coe μ ((hq.comp (measurable_id.prodMk (measurable_const (a := d)))) hs) (coefficient μ d u),
    coefficient_coe μ d u] with x hc hi ho hu
  rw [hc, hi, ho]
  by_cases hx : q (x,d) ∈ s <;> simp [hx, hu]

theorem injection_indicator (q : X × D → Z) (hq : Measurable q)
    (s : Set Z) (hs : MeasurableSet s) (d : D) (u : Lp ℂ 2 μ) :
    injection μ d (indicatorL2 μ ((hq.comp (measurable_id.prodMk (measurable_const (a := d)))) hs) u) =
      indicatorL2 (μ.prod Measure.count) (hq hs) (injection μ d u) := by
  classical
  apply Lp.ext
  filter_upwards [injection_coe μ d
      (indicatorL2 μ ((hq.comp (measurable_id.prodMk (measurable_const (a := d)))) hs) u),
    indicatorL2_coe (μ.prod Measure.count) (hq hs) (injection μ d u), injection_coe μ d u,
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := (Measure.count : Measure D))).ae
      (indicatorL2_coe μ ((hq.comp (measurable_id.prodMk (measurable_const (a := d)))) hs) u)]
      with p hleft hright hinj hbase
  rw [hleft, hright]
  simp only [Set.indicator_apply]
  rw [hinj]
  by_cases hd : p.2 = d
  · have hp' : p = (p.1, d) := Prod.ext rfl hd
    rw [hp'] at *
    simp only [injectionFun, if_pos rfl]
    rw [hbase]
    by_cases hp : q (p.1, d) ∈ s
    · simp [hp]
    · simp [hp]
  · by_cases hp : q p ∈ s <;> simp [injectionFun, hd, hp]

variable (ν : Measure Y) [SigmaFinite ν]

/-- Matrix coefficients of an actual intertwiner satisfy the twisted
measurable-projection relation on their source and target slices. -/
theorem matrixCoefficient_intertwines_projections
    (q : X × D → Z) (r : Y × D → Z) (hq : Measurable q) (hr : Measurable r)
    (T : Lp ℂ 2 (μ.prod (Measure.count : Measure D)) →L[ℂ]
      Lp ℂ 2 (ν.prod (Measure.count : Measure D)))
    (hT : ∀ (s : Set Z) (hs : MeasurableSet s)
      (u : Lp ℂ 2 (μ.prod (Measure.count : Measure D))),
      T (indicatorL2 (μ.prod Measure.count) (hq hs) u) =
        indicatorL2 (ν.prod Measure.count) (hr hs) (T u))
    (s : Set Z) (hs : MeasurableSet s) (d e : D) (u : Lp ℂ 2 μ) :
    matrixCoefficient μ ν T d e
      (indicatorL2 μ ((hq.comp (measurable_id.prodMk (measurable_const (a := e)))) hs) u) =
        indicatorL2 ν ((hr.comp (measurable_id.prodMk (measurable_const (a := d)))) hs)
          (matrixCoefficient μ ν T d e u) := by
  change coefficient ν d (T (injection μ e
    (indicatorL2 μ ((hq.comp (measurable_id.prodMk (measurable_const (a := e)))) hs) u))) =
      indicatorL2 ν ((hr.comp (measurable_id.prodMk (measurable_const (a := d)))) hs)
        (coefficient ν d (T (injection μ e u)))
  rw [injection_indicator μ q hq s hs e u, hT s hs, coefficient_indicator ν r hr s hs d]

end MeasureEquivalenceL2Coefficients

#print axioms MeasureEquivalenceL2Coefficients.coefficient_indicator
#print axioms MeasureEquivalenceL2Coefficients.injection_indicator
#print axioms MeasureEquivalenceL2Coefficients.matrixCoefficient_intertwines_projections
