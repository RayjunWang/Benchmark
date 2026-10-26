import InducedCornerTransport

/-! Actual multiplication and group-shift unitaries on the induced L2
corner modules, and their simultaneous intertwining for equal finite mass. -/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace MeasureEquivalenceInducedCorners

open MeasureEquivalenceEquidecomposition MeasureUnitary

noncomputable section

variable {G Z : Type*} [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    [MeasurableSpace Z] [MulAction G Z] [MeasurableConstSMul G Z]
    (μ : Measure Z) [SigmaFinite μ]

def inducedPhaseUnitary (A : Set Z) (f : Z → ℂ) (hf : Measurable f)
    (hnorm : ∀ z, ‖f z‖ = 1) :
    Lp ℂ 2 (cornerMeasure (G := G) μ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (cornerMeasure (G := G) μ A) :=
  phaseEquiv (cornerMeasure (G := G) μ A) (fun p => f (orbitPoint p))
    (hf.comp orbitPoint_measurable) (fun p => hnorm (orbitPoint p))

omit [SigmaFinite μ] in
theorem inducedPhaseUnitary_coe (A : Set Z) (f : Z → ℂ) (hf : Measurable f)
    (hnorm : ∀ z, ‖f z‖ = 1) (u : Lp ℂ 2 (cornerMeasure (G := G) μ A)) :
    inducedPhaseUnitary μ A f hf hnorm u =ᵐ[cornerMeasure (G := G) μ A]
      (fun p => f (orbitPoint p) • u p) :=
  phaseMap_coe (cornerMeasure (G := G) μ A) (fun p => f (orbitPoint p))
    (hf.comp orbitPoint_measurable) (fun p => hnorm (orbitPoint p)) u

def inducedShiftUnitary (A : Set Z) (h : G) :
    Lp ℂ 2 (cornerMeasure (G := G) μ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (cornerMeasure (G := G) μ A) :=
  pullbackUnitary (cornerMeasure (G := G) μ A) (cornerMeasure (G := G) μ A)
    (indexShift h⁻¹) (indexShift h)
    (indexShift_preserving μ A h⁻¹) (indexShift_preserving μ A h)
    (Eventually.of_forall (fun p => by
      change (p.1, h*(h⁻¹*p.2)) = p
      simp only [mul_inv_cancel_left, Prod.mk.eta]))

omit [MulAction G Z] [MeasurableConstSMul G Z] in
theorem inducedShiftUnitary_coe (A : Set Z) (h : G)
    (u : Lp ℂ 2 (cornerMeasure (G := G) μ A)) :
    inducedShiftUnitary μ A h u =ᵐ[cornerMeasure (G := G) μ A]
      (fun p => u (indexShift h⁻¹ p)) :=
  Lp.coeFn_compMeasurePreserving u (indexShift_preserving μ A h⁻¹)

omit [MulAction G Z] [MeasurableConstSMul G Z] in
theorem inducedShift_one_apply (A : Set Z)
    (u : Lp ℂ 2 (cornerMeasure (G := G) μ A)) :
    inducedShiftUnitary μ A (1 : G) u = u := by
  apply Lp.ext
  filter_upwards [inducedShiftUnitary_coe μ A (1 : G) u] with p hp
  have heq : indexShift (1 : G) p = p := by
    change (p.1, 1*p.2) = p
    simp only [one_mul, Prod.mk.eta]
  simpa only [inv_one, heq] using hp

omit [MulAction G Z] [MeasurableConstSMul G Z] in
theorem inducedShift_mul_apply (A : Set Z) (h k : G)
    (u : Lp ℂ 2 (cornerMeasure (G := G) μ A)) :
    inducedShiftUnitary μ A (h*k) u =
      inducedShiftUnitary μ A h (inducedShiftUnitary μ A k u) := by
  apply Lp.ext
  filter_upwards [inducedShiftUnitary_coe μ A (h*k) u,
    inducedShiftUnitary_coe μ A h (inducedShiftUnitary μ A k u),
    (indexShift_preserving μ A h⁻¹).quasiMeasurePreserving.ae
      (inducedShiftUnitary_coe μ A k u)] with p hleft hright hinner
  rw [hleft, hright, hinner]
  congr 1
  change (p.1, (h*k)⁻¹*p.2) = (p.1, k⁻¹*(h⁻¹*p.2))
  simp only [mul_inv_rev, mul_assoc]

omit [MulAction G Z] [MeasurableConstSMul G Z] in
/-- The group generators form an actual unitary representation. -/
def inducedShiftRepresentation (A : Set Z) : G →*
    (Lp ℂ 2 (cornerMeasure (G := G) μ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (cornerMeasure (G := G) μ A)) where
  toFun := inducedShiftUnitary μ A
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro u
    exact inducedShift_one_apply μ A u
  map_mul' h k := by
    apply LinearIsometryEquiv.ext
    intro u
    exact inducedShift_mul_apply μ A h k u

variable (hmp : ∀ g : G, MeasurePreserving (fun z : Z => g • z) μ μ)

include hmp in
/-- Equal finite mass gives a genuine complex Hilbert-space unitary
intertwining all bounded measurable phase multipliers and all group
generators of the induced finite-corner representation. -/
theorem exists_induced_corner_unitary
    (herg : ∀ s : Set Z, MeasurableSet s →
      (∀ g : G, (fun z : Z => g • z) ⁻¹' s = s) → μ s = 0 ∨ μ sᶜ = 0)
    (A B : Set Z) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfin : μ A ≠ ∞) (hmass : μ A = μ B) :
    ∃ U : Lp ℂ 2 (cornerMeasure (G := G) μ B) ≃ₗᵢ[ℂ] Lp ℂ 2 (cornerMeasure (G := G) μ A),
      (∀ (f : Z → ℂ) (hf : Measurable f) (hnorm : ∀ z, ‖f z‖ = 1)
        (u : Lp ℂ 2 (cornerMeasure (G := G) μ B)),
        U (inducedPhaseUnitary μ B f hf hnorm u) =
          inducedPhaseUnitary μ A f hf hnorm (U u)) ∧
      (∀ (h : G) (u : Lp ℂ 2 (cornerMeasure (G := G) μ B)),
        U (inducedShiftUnitary μ B h u) = inducedShiftUnitary μ A h (U u)) := by
  obtain ⟨F,H,hF,hH,hHF,_hFH,horbit,hcomm⟩ :=
    exists_induced_corner_transport μ hmp herg A B hA hB hfin hmass
  let U := pullbackUnitary (cornerMeasure (G := G) μ A) (cornerMeasure (G := G) μ B) F H hF hH hHF
  have hU (u : Lp ℂ 2 (cornerMeasure (G := G) μ B)) :
      U u =ᵐ[cornerMeasure (G := G) μ A] (fun p => u (F p)) :=
    Lp.coeFn_compMeasurePreserving u hF
  refine ⟨U, ?_, ?_⟩
  · intro f hf hnorm u
    apply Lp.ext
    filter_upwards [hU (inducedPhaseUnitary μ B f hf hnorm u),
      hF.quasiMeasurePreserving.ae (inducedPhaseUnitary_coe μ B f hf hnorm u),
      inducedPhaseUnitary_coe μ A f hf hnorm (U u), hU u, horbit]
      with p hleft hBphase hright hUp horbitp
    rw [hleft, hBphase, hright, hUp, horbitp]
  · intro h u
    apply Lp.ext
    filter_upwards [hU (inducedShiftUnitary μ B h u),
      hF.quasiMeasurePreserving.ae (inducedShiftUnitary_coe μ B h u),
      inducedShiftUnitary_coe μ A h (U u),
      (indexShift_preserving μ A h⁻¹).quasiMeasurePreserving.ae (hU u), hcomm h⁻¹]
      with p hleft hBshift hright hUp hcommp
    rw [hleft, hBshift, hright, hUp, hcommp]

end
end MeasureEquivalenceInducedCorners

#print axioms MeasureEquivalenceInducedCorners.inducedPhaseUnitary
#print axioms MeasureEquivalenceInducedCorners.inducedShiftUnitary
#print axioms MeasureEquivalenceInducedCorners.exists_induced_corner_unitary
#print axioms MeasureEquivalenceInducedCorners.inducedShiftRepresentation
