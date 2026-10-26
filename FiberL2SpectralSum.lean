import FiberL2HilbertSum
import FiberMultiplicityClassification

/-! The Hilbert-sum/fiber identification respects the actual coordinate unitary. -/

open MeasureTheory Set Filter
open scoped ENNReal

set_option maxHeartbeats 2000000

namespace MeasureUnitary

open MeasureEquivalenceL2Coefficients MeasureEquivalenceL2Restriction

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

 theorem restrict_phase (A : Set X) (c : X → ℂ) (hc : Measurable c)
    (hnorm : ∀ x, ‖c x‖ = 1) (f : Lp ℂ 2 μ) :
    restrictMap μ A (phaseEquiv μ c hc hnorm f) =
      phaseEquiv (μ.restrict A) c hc hnorm (restrictMap μ A f) := by
  apply Lp.ext
  filter_upwards [restrict_coe μ A (phaseEquiv μ c hc hnorm f),
    ae_restrict_of_ae (phaseMap_coe μ c hc hnorm f),
    phaseMap_coe (μ.restrict A) c hc hnorm (restrictMap μ A f),
    restrict_coe μ A f] with x hleft hphase hright hf
  change ((phaseEquiv μ c hc hnorm) f) x = _ at hphase
  change ((phaseEquiv (μ.restrict A) c hc hnorm) (restrictMap μ A f)) x = _ at hright
  rw [hleft, hphase, hright, hf]

theorem zeroExtend_phase (A : Set X) (hA : MeasurableSet A)
    (c : X → ℂ) (hc : Measurable c) (hnorm : ∀ x, ‖c x‖ = 1)
    (f : Lp ℂ 2 (μ.restrict A)) :
    zeroExtend μ A hA (phaseEquiv (μ.restrict A) c hc hnorm f) =
      phaseEquiv μ c hc hnorm (zeroExtend μ A hA f) := by
  apply Lp.ext
  have hsource := (ae_eq_restrict_iff_indicator_ae_eq hA).mp
    (phaseMap_coe (μ.restrict A) c hc hnorm f)
  filter_upwards [zeroExtend_coe μ A hA (phaseEquiv (μ.restrict A) c hc hnorm f),
    hsource, phaseMap_coe μ c hc hnorm (zeroExtend μ A hA f),
    zeroExtend_coe μ A hA f] with x hleft hs hright hf
  change A.indicator ((phaseEquiv (μ.restrict A) c hc hnorm) f) x = _ at hs
  change ((phaseEquiv μ c hc hnorm) (zeroExtend μ A hA f)) x = _ at hright
  rw [hleft, hs, hright, hf]
  by_cases hx : x ∈ A <;> simp [hx]

variable [IsFiniteMeasure μ]

theorem injection_phase (i : ℕ) (c : X → ℂ) (hc : Measurable c)
    (hnorm : ∀ x, ‖c x‖ = 1) (f : Lp ℂ 2 μ) :
    injection μ i (phaseEquiv μ c hc hnorm f) =
      phaseEquiv (fiberAmbientMeasure μ) (fun p => c p.1) (hc.comp measurable_fst)
        (fun p => hnorm p.1) (injection μ i f) := by
  apply Lp.ext
  filter_upwards [injection_coe μ i (phaseEquiv μ c hc hnorm f),
    phaseMap_coe (fiberAmbientMeasure μ) (fun p => c p.1) (hc.comp measurable_fst)
      (fun p => hnorm p.1) (injection μ i f), injection_coe μ i f,
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := (Measure.count : Measure ℕ))).ae
      (phaseMap_coe μ c hc hnorm f)] with p hleft hright hinj hphase
  change ((phaseEquiv (fiberAmbientMeasure μ) (fun p => c p.1) (hc.comp measurable_fst)
    (fun p => hnorm p.1)) (injection μ i f)) p = _ at hright
  change ((phaseEquiv μ c hc hnorm) f) p.1 = _ at hphase
  rw [hleft, hright, hinj]
  by_cases hp : p.2 = i <;> simp [injectionFun,hp,hphase]

theorem fiberComponentInjection_phase (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (i : ℕ) (c : X → ℂ) (hc : Measurable c) (hnorm : ∀ x, ‖c x‖ = 1)
    (f : Lp ℂ 2 (μ.restrict (A i))) :
    fiberComponentInjection μ A hA i (phaseEquiv (μ.restrict (A i)) c hc hnorm f) =
      phaseEquiv (fiberRestrictedMeasure μ A) (fun p => c p.1) (hc.comp measurable_fst)
        (fun p => hnorm p.1) (fiberComponentInjection μ A hA i f) := by
  apply (zeroExtendLI (fiberAmbientMeasure μ) (measureFiberSet A)
    (measureFiberSet_measurable A hA)).injective
  change zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA)
    (fiberComponentInjection μ A hA i (phaseEquiv (μ.restrict (A i)) c hc hnorm f)) =
    zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA)
      (phaseEquiv (fiberRestrictedMeasure μ A) (fun p => c p.1) (hc.comp measurable_fst)
        (fun p => hnorm p.1) (fiberComponentInjection μ A hA i f))
  rw [fiberComponentInjection_zeroExtend, zeroExtend_phase, zeroExtend_phase,
    fiberComponentInjection_zeroExtend, injection_phase]

def fiberSumPhaseUnitary (A : ℕ → Set X) (c : X → ℂ) (hc : Measurable c)
    (hnorm : ∀ x, ‖c x‖ = 1) :
    lp (fun i => Lp ℂ 2 (μ.restrict (A i))) 2 ≃ₗᵢ[ℂ]
      lp (fun i => Lp ℂ 2 (μ.restrict (A i))) 2 :=
  hilbertFamilyCongr (fun i => phaseEquiv (μ.restrict (A i)) c hc hnorm)

theorem fiberL2SumEquiv_single (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (i : ℕ) (f : Lp ℂ 2 (μ.restrict (A i))) :
    fiberL2SumEquiv μ A hA (lp.single 2 i f) = fiberComponentInjection μ A hA i f :=
  (fiberL2HilbertSum μ A hA).linearIsometryEquiv_symm_apply_single f

theorem fiberL2SumEquiv_intertwines_phase (A : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (c : X → ℂ) (hc : Measurable c)
    (hnorm : ∀ x, ‖c x‖ = 1) (f : lp (fun i => Lp ℂ 2 (μ.restrict (A i))) 2) :
    fiberL2SumEquiv μ A hA (fiberSumPhaseUnitary μ A c hc hnorm f) =
      phaseEquiv (fiberRestrictedMeasure μ A) (fun p => c p.1) (hc.comp measurable_fst)
        (fun p => hnorm p.1) (fiberL2SumEquiv μ A hA f) := by
  have hmaps : (fiberL2SumEquiv μ A hA).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (fiberSumPhaseUnitary μ A c hc hnorm).toContinuousLinearEquiv.toContinuousLinearMap =
      (phaseEquiv (fiberRestrictedMeasure μ A) (fun p => c p.1) (hc.comp measurable_fst)
        (fun p => hnorm p.1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fiberL2SumEquiv μ A hA).toContinuousLinearEquiv.toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    intro i
    apply ContinuousLinearMap.ext
    intro g
    change fiberL2SumEquiv μ A hA
      (hilbertFamilyCongr (fun j => phaseEquiv (μ.restrict (A j)) c hc hnorm) (lp.single 2 i g)) =
      phaseEquiv (fiberRestrictedMeasure μ A) (fun p => c p.1) (hc.comp measurable_fst)
        (fun p => hnorm p.1) (fiberL2SumEquiv μ A hA (lp.single 2 i g))
    rw [hilbertFamilyCongr_single, fiberL2SumEquiv_single, fiberL2SumEquiv_single]
    exact fiberComponentInjection_phase μ A hA i c hc hnorm g
  exact congrArg (fun T => T f) hmaps

end
end MeasureUnitary

#print axioms MeasureUnitary.fiberL2SumEquiv_intertwines_phase

