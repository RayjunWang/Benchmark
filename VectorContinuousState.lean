import VectorSpectralState
import MeasurePullbackMultipliers
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! Genuine continuous multiplication intertwiners preserve all finite
vector-state measures and hence the maximal pushforward measure class. -/

open MeasureTheory Filter Set
open scoped ENNReal

namespace MeasureUnitary

variable {Ω Λ K : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

theorem vectorSpectralState_continuous_integral (μ : Measure Ω) (q : Ω → K)
    (hq : Measurable q) (f : Lp ℂ 2 μ) (c : C(K,ℂ)) :
    (∫ x, c x ∂vectorSpectralState μ q f) =
      inner ℂ f (pullbackMultiplierL2 μ q hq c f) := by
  have heq : boundedMultiplierL2 μ (pullbackContinuousSymbol μ q hq c) =
      pullbackMultiplierL2 (E := ℂ) μ q hq c := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [boundedMultiplierL2_coe μ (pullbackContinuousSymbol μ q hq c) f,
      pullbackContinuousSymbol_coe μ q hq c, pullbackMultiplierL2_coe μ q hq c f]
      with x hleft hs hright
    rw [hleft,hs,hright]
    rfl
  rw [← heq]
  exact vectorSpectralState_integral μ q hq f c c.continuous.measurable
    (pullbackContinuousSymbol μ q hq c) (pullbackContinuousSymbol_coe μ q hq c)

theorem vectorSpectralState_eq_of_intertwines_continuous
    (μ : Measure Ω) (ν : Measure Λ) (q : Ω → K) (r : Λ → K)
    (hq : Measurable q) (hr : Measurable r)
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hU : ∀ (c : C(K,ℂ)) (f : Lp ℂ 2 μ),
      U (pullbackMultiplierL2 μ q hq c f) = pullbackMultiplierL2 ν r hr c (U f))
    (f : Lp ℂ 2 μ) : vectorSpectralState μ q f = vectorSpectralState ν r (U f) := by
  have hm (c : C(K,ℂ)) : (∫ x,c x ∂vectorSpectralState μ q f) =
      ∫ x,c x ∂vectorSpectralState ν r (U f) := by
    rw [vectorSpectralState_continuous_integral μ q hq,
      vectorSpectralState_continuous_integral ν r hr, ← hU, U.inner_map_map]
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro c
  let z : C(K,ℂ) := ⟨fun x => (c x : ℂ), Complex.continuous_ofReal.comp c.continuous⟩
  apply Complex.ofReal_injective
  simpa only [z, ContinuousMap.coe_mk, integral_complex_ofReal] using hm z

theorem push_measures_equivalent_of_intertwines_continuous
    (μ : Measure Ω) (ν : Measure Λ) [SigmaFinite μ] [SigmaFinite ν]
    (q : Ω → K) (r : Λ → K) (hq : Measurable q) (hr : Measurable r)
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hU : ∀ (c : C(K,ℂ)) (f : Lp ℂ 2 μ),
      U (pullbackMultiplierL2 μ q hq c f) = pullbackMultiplierL2 ν r hr c (U f)) :
    μ.map q ≪ ν.map r ∧ ν.map r ≪ μ.map q := by
  constructor
  · obtain ⟨f,hf⟩ := exists_faithful_L2 μ
    exact absolutelyContinuous_push_of_faithful_state μ ν q r hq hr f (U f) hf
      (vectorSpectralState_eq_of_intertwines_continuous μ ν q r hq hr U hU f)
  · obtain ⟨g,hg⟩ := exists_faithful_L2 ν
    have hV (c : C(K,ℂ)) (f : Lp ℂ 2 ν) :
        U.symm (pullbackMultiplierL2 ν r hr c f) =
          pullbackMultiplierL2 μ q hq c (U.symm f) := by
      apply U.injective
      simpa using (hU c (U.symm f)).symm
    exact absolutelyContinuous_push_of_faithful_state ν μ r q hr hq g (U.symm g) hg
      (vectorSpectralState_eq_of_intertwines_continuous ν μ r q hr hq U.symm hV g)

end MeasureUnitary

#print axioms MeasureUnitary.vectorSpectralState_eq_of_intertwines_continuous
#print axioms MeasureUnitary.push_measures_equivalent_of_intertwines_continuous
