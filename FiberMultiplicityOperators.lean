import L2MatrixProjection
import L2LocalizedAdjoints
import L2ProjectionCommutantNormal
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-! Actual ambient operators and Parseval identities obtained from a
unitary between measurable finite-base/counting-fiber L² subspaces. -/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

set_option maxHeartbeats 1500000

namespace MeasureUnitary

open MeasureEquivalenceL2Coefficients MeasureEquivalenceL2Restriction

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

def measureFiberSet (A : ℕ → Set X) : Set (X × ℕ) := {p | p.1 ∈ A p.2}

theorem measureFiberSet_measurable (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    MeasurableSet (measureFiberSet A) := by
  have heq : measureFiberSet A = ⋃ i : ℕ, A i ×ˢ {i} := by
    ext p
    simp only [measureFiberSet, mem_setOf_eq, mem_iUnion, mem_prod, mem_singleton_iff]
    constructor
    · intro hp
      exact ⟨p.2,hp,rfl⟩
    · rintro ⟨i,hp,hi⟩
      simpa only [hi] using hp
  rw [heq]
  exact MeasurableSet.iUnion (fun i => (hA i).prod (measurableSet_singleton i))

abbrev fiberAmbientMeasure := μ.prod (Measure.count : Measure ℕ)
abbrev fiberRestrictedMeasure (A : ℕ → Set X) := (fiberAmbientMeasure μ).restrict (measureFiberSet A)

def fiberGlobalOperator (A B : ℕ → Set X) (hB : ∀ i, MeasurableSet (B i))
    (U : Lp ℂ 2 (fiberRestrictedMeasure μ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure μ B)) :
    Lp ℂ 2 (fiberAmbientMeasure μ) →L[ℂ] Lp ℂ 2 (fiberAmbientMeasure μ) :=
  globalizeOperator (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet B)
    (measureFiberSet_measurable B hB) U.toContinuousLinearEquiv.toContinuousLinearMap

theorem fiberGlobalOperator_adjoint (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (U : Lp ℂ 2 (fiberRestrictedMeasure μ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure μ B)) :
    (fiberGlobalOperator μ A B hB U).adjoint = fiberGlobalOperator μ B A hA U.symm := by
  rw [fiberGlobalOperator, globalize_adjoint _ _ _ (measureFiberSet_measurable A hA), U.adjoint_eq_symm]
  rfl

theorem fiberGlobalOperator_norm (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (U : Lp ℂ 2 (fiberRestrictedMeasure μ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure μ B))
    (f : Lp ℂ 2 (fiberAmbientMeasure μ)) :
    ‖fiberGlobalOperator μ A B hB U f‖ =
      ‖indicatorL2 (fiberAmbientMeasure μ) (measureFiberSet_measurable A hA) f‖ := by
  change ‖zeroExtend (fiberAmbientMeasure μ) (measureFiberSet B)
    (measureFiberSet_measurable B hB)
    (U (restrictMap (fiberAmbientMeasure μ) (measureFiberSet A) f))‖ = _
  rw [zeroExtend_norm, U.norm_map, ← zeroExtend_norm (fiberAmbientMeasure μ)
    (measureFiberSet A) (measureFiberSet_measurable A hA), zeroExtend_restrict]

theorem fiber_injection_indicator (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (e : ℕ) (f : Lp ℂ 2 μ) :
    injection μ e (indicatorL2 μ (hA e) f) =
      indicatorL2 (fiberAmbientMeasure μ) (measureFiberSet_measurable A hA) (injection μ e f) :=
  injection_indicator μ id measurable_id (measureFiberSet A) (measureFiberSet_measurable A hA) e f

theorem fiberGlobalOperator_column_norm_sq (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (U : Lp ℂ 2 (fiberRestrictedMeasure μ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure μ B))
    (e : ℕ) (f : Lp ℂ 2 μ) :
    (∑' d : ℕ, ‖matrixCoefficient μ μ (fiberGlobalOperator μ A B hB U) d e f‖ ^ 2) =
      ‖indicatorL2 μ (hA e) f‖ ^ 2 := by
  change (∑' d : ℕ, ‖coefficient μ d
    (fiberGlobalOperator μ A B hB U (injection μ e f))‖ ^ 2) = _
  rw [← norm_sq_eq_tsum_coefficient_norm_sq, fiberGlobalOperator_norm μ A B hA hB U,
    ← fiber_injection_indicator μ A hA e f, injection_norm]

theorem fiberGlobalOperator_commutes_base_projections (A B : ℕ → Set X)
    (hB : ∀ i, MeasurableSet (B i))
    (U : Lp ℂ 2 (fiberRestrictedMeasure μ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure μ B))
    (hU : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (fiberRestrictedMeasure μ A)),
      U (indicatorL2 (fiberRestrictedMeasure μ A) (hs.preimage measurable_fst) f) =
        indicatorL2 (fiberRestrictedMeasure μ B) (hs.preimage measurable_fst) (U f))
    (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (fiberAmbientMeasure μ)) :
    fiberGlobalOperator μ A B hB U
      (indicatorL2 (fiberAmbientMeasure μ) (hs.preimage measurable_fst) f) =
      indicatorL2 (fiberAmbientMeasure μ) (hs.preimage measurable_fst)
        (fiberGlobalOperator μ A B hB U f) := by
  change zeroExtend (fiberAmbientMeasure μ) (measureFiberSet B) (measureFiberSet_measurable B hB)
    (U (restrictMap (fiberAmbientMeasure μ) (measureFiberSet A)
      (indicatorL2 (fiberAmbientMeasure μ) (hs.preimage measurable_fst) f))) = _
  rw [restrict_indicator, hU s hs, zeroExtend_indicator]
  rfl

end
end MeasureUnitary

#print axioms MeasureUnitary.fiberGlobalOperator_column_norm_sq
