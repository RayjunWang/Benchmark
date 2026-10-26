import MeasurePullbackMultipliers
import SeparatingMultiplierIntertwining

/-! Genuine unitary intertwiners of a separating continuous family
intertwine every pulled-back continuous multiplier. The two underlying
measure spaces may be arbitrary and have different Hilbert coefficient fibers. -/

open MeasureTheory

namespace MeasureUnitary

noncomputable section

variable {Ω Ψ K : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
  [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [CompactSpace K] [SecondCountableTopology K]
  (μ : Measure Ω) (ν : Measure Ψ) (q : Ω → K) (r : Ψ → K) (hq : Measurable q) (hr : Measurable r)
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem pullbackMultiplierL2_phase (c : C(K, ℂ)) (hc : ∀ x, ‖c x‖ = 1) (f : Lp E 2 μ) :
    pullbackMultiplierL2 μ q hq c f = phaseEquiv μ (fun x => c (q x))
      (c.continuous.measurable.comp hq) (fun x => hc (q x)) f := by
  apply Lp.ext
  exact (pullbackMultiplierL2_coe μ q hq c f).trans
    (phaseMap_coe μ (fun x => c (q x)) (c.continuous.measurable.comp hq) (fun x => hc (q x)) f).symm

theorem continuous_intertwines_of_separating_family {I : Type*}
    (c : I → C(K, ℂ)) (hsep : ∀ x y : K, x ≠ y → ∃ i, c i x ≠ c i y)
    (U : Lp E 2 μ ≃ₗᵢ[ℂ] Lp F 2 ν)
    (hU : ∀ i f, U (pullbackMultiplierL2 μ q hq (c i) f) =
      pullbackMultiplierL2 ν r hr (c i) (U f)) :
    ∀ g f, U (pullbackMultiplierL2 μ q hq g f) = pullbackMultiplierL2 ν r hr g (U f) := by
  let φ : C(K, ℂ) →⋆ₐ[ℂ] (Lp F 2 ν →L[ℂ] Lp F 2 ν) :=
    (U.conjStarAlgEquiv : (Lp E 2 μ →L[ℂ] Lp E 2 μ) →⋆ₐ[ℂ]
      (Lp F 2 ν →L[ℂ] Lp F 2 ν)).comp (pullbackMultiplierStarAlgHom (E := E) μ q hq)
  let ψ : C(K, ℂ) →⋆ₐ[ℂ] (Lp F 2 ν →L[ℂ] Lp F 2 ν) := pullbackMultiplierStarAlgHom ν r hr
  have heq : φ = ψ := by
    apply MeasureEquivalenceRestrictedPhase.starAlgHom_eq_of_separating_family φ ψ
      (U.toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous.comp (pullbackMultiplierL2 μ q hq).continuous)
      (pullbackMultiplierL2 ν r hr).continuous c hsep
    intro i
    apply ContinuousLinearMap.ext
    intro f
    change U (pullbackMultiplierL2 μ q hq (c i) (U.symm f)) = pullbackMultiplierL2 ν r hr (c i) f
    simpa using hU i (U.symm f)
  intro g f
  have h := congrArg (fun H : C(K, ℂ) →⋆ₐ[ℂ] (Lp F 2 ν →L[ℂ] Lp F 2 ν) => H g (U f)) heq
  change U (pullbackMultiplierL2 μ q hq g (U.symm (U f))) = pullbackMultiplierL2 ν r hr g (U f) at h
  simpa using h

theorem continuous_intertwines_of_separating_phases {I : Type*}
    (c : I → C(K, ℂ)) (hc : ∀ i x, ‖c i x‖ = 1)
    (hsep : ∀ x y : K, x ≠ y → ∃ i, c i x ≠ c i y)
    (U : Lp E 2 μ ≃ₗᵢ[ℂ] Lp F 2 ν)
    (hU : ∀ i f, U (phaseEquiv μ (fun x => c i (q x))
        ((c i).continuous.measurable.comp hq) (fun x => hc i (q x)) f) =
      phaseEquiv ν (fun x => c i (r x)) ((c i).continuous.measurable.comp hr)
        (fun x => hc i (r x)) (U f)) :
    ∀ g f, U (pullbackMultiplierL2 μ q hq g f) = pullbackMultiplierL2 ν r hr g (U f) := by
  apply continuous_intertwines_of_separating_family μ ν q r hq hr c hsep U
  intro i f
  simpa only [pullbackMultiplierL2_phase _ _ _ _ (hc i)] using hU i f

end

end MeasureUnitary

#print axioms MeasureUnitary.continuous_intertwines_of_separating_phases
