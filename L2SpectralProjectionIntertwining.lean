import VectorContinuousState
import L2RestrictionExtension
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! Intertwining all continuous multipliers implies intertwining all
measurable spectral projections, by equality of the actual vector-state
measures and complex polarization. -/

open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 1000000

namespace MeasureUnitary

open MeasureEquivalenceL2Restriction

noncomputable section

variable {Ω Ψ K : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]

def indicatorCLM (μ : Measure Ω) {s : Set Ω} (hs : MeasurableSet s) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (zeroExtendLI μ s hs).toContinuousLinearMap.comp (restrictCLM μ s)

theorem indicatorCLM_apply (μ : Measure Ω) {s : Set Ω} (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    indicatorCLM μ hs f = indicatorL2 μ hs f := zeroExtend_restrict μ s hs f

theorem inner_indicatorL2_self (μ : Measure Ω) {s : Set Ω} (hs : MeasurableSet s)
    (f : Lp ℂ 2 μ) :
    inner ℂ (indicatorL2 μ hs f) f = (‖indicatorL2 μ hs f‖ ^ 2 : ℂ) := by
  have hin : inner ℂ (indicatorL2 μ hs f) (indicatorL2 μ hs f) =
      (‖indicatorL2 μ hs f‖ ^ 2 : ℂ) := by
    simpa only [Complex.ofReal_pow] using
      (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (indicatorL2 μ hs f))
  rw [← hin]
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [indicatorL2_coe μ hs f] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

theorem projections_intertwine_of_vectorSpectralState_eq
    [MeasurableSpace K] (μ : Measure Ω) (ν : Measure Ψ)
    (q : Ω → K) (r : Ψ → K) (hq : Measurable q) (hr : Measurable r)
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hU : ∀ f, vectorSpectralState μ q f = vectorSpectralState ν r (U f))
    (s : Set K) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    U (indicatorL2 μ (hs.preimage hq) f) = indicatorL2 ν (hs.preimage hr) (U f) := by
  let P := indicatorCLM μ (hs.preimage hq)
  let Q := indicatorCLM ν (hs.preimage hr)
  let S := U.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (Q.comp U.toContinuousLinearEquiv.toContinuousLinearMap)
  have hnorm (g : Lp ℂ 2 μ) : ‖P g‖ ^ 2 = ‖Q (U g)‖ ^ 2 := by
    have h := congrArg (fun M : Measure K => M s) (hU g)
    change vectorSpectralState μ q g s = vectorSpectralState ν r (U g) s at h
    rw [vectorSpectralState_apply μ q hq g hs,
      vectorSpectralState_apply ν r hr (U g) hs] at h
    have hh := (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (sq_nonneg _)).mp h
    simpa only [P, Q, indicatorCLM_apply] using hh
  have hSP : S.toLinearMap = P.toLinearMap := by
    apply (ext_inner_map _ _).mp
    intro g
    change inner ℂ (U.symm (Q (U g))) g = inner ℂ (P g) g
    calc
      inner ℂ (U.symm (Q (U g))) g = inner ℂ (Q (U g)) (U g) := by
        simpa only [LinearIsometryEquiv.apply_symm_apply] using
          (U.inner_map_map (U.symm (Q (U g))) g).symm
      _ = (‖Q (U g)‖ ^ 2 : ℂ) := by
        simpa only [Q, indicatorCLM_apply] using inner_indicatorL2_self ν (hs.preimage hr) (U g)
      _ = (‖P g‖ ^ 2 : ℂ) := by
        simpa only [Complex.ofReal_pow] using congrArg Complex.ofReal (hnorm g).symm
      _ = inner ℂ (P g) g := by
        simpa only [P, indicatorCLM_apply] using (inner_indicatorL2_self μ (hs.preimage hq) g).symm
  have h := congrArg U (LinearMap.congr_fun hSP f)
  change U (U.symm (Q (U f))) = U (P f) at h
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  simpa only [P, Q, indicatorCLM_apply] using h.symm

theorem projections_intertwine_of_continuous_multipliers
    [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure Ω) (ν : Measure Ψ) (q : Ω → K) (r : Ψ → K)
    (hq : Measurable q) (hr : Measurable r)
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hU : ∀ (c : C(K,ℂ)) (f : Lp ℂ 2 μ),
      U (pullbackMultiplierL2 μ q hq c f) = pullbackMultiplierL2 ν r hr c (U f)) :
    ∀ (s : Set K) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      U (indicatorL2 μ (hs.preimage hq) f) = indicatorL2 ν (hs.preimage hr) (U f) :=
  projections_intertwine_of_vectorSpectralState_eq μ ν q r hq hr U
    (vectorSpectralState_eq_of_intertwines_continuous μ ν q r hq hr U hU)

end
end MeasureUnitary

#print axioms MeasureUnitary.projections_intertwine_of_continuous_multipliers
