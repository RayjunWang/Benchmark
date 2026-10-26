import FiberMultiplicityOperators
import L2ModuleEntryMass

/-! Actual base-projection intertwiners preserve pointwise Hilbert-fiber
multiplicity. Parseval and adjoint transposition supply both stochastic
matrix identities; no matrix or dimension hypothesis is postulated. -/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

set_option maxHeartbeats 2000000

namespace MeasureUnitary

open MeasureEquivalenceL2Coefficients

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

def fiberMultiplicity (A : ℕ → Set X) (x : X) : ℝ≥0∞ :=
  ∑' i : ℕ, (A i).indicator (fun _ => (1 : ℝ≥0∞)) x

theorem fiberMultiplicity_measurable (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    Measurable (fiberMultiplicity A) :=
  Measurable.ennreal_tsum (fun i => measurable_const.indicator (hA i))

theorem fiberMatrixCoefficient_commutes (A B : ℕ → Set X)
    (hB : ∀ i, MeasurableSet (B i))
    (U : Lp ℂ 2 (fiberRestrictedMeasure μ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure μ B))
    (hU : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (fiberRestrictedMeasure μ A)),
      U (indicatorL2 (fiberRestrictedMeasure μ A) (hs.preimage measurable_fst) f) =
        indicatorL2 (fiberRestrictedMeasure μ B) (hs.preimage measurable_fst) (U f))
    (d e : ℕ) (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    matrixCoefficient μ μ (fiberGlobalOperator μ A B hB U) d e (indicatorL2 μ hs f) =
      indicatorL2 μ hs (matrixCoefficient μ μ (fiberGlobalOperator μ A B hB U) d e f) :=
  matrixCoefficient_intertwines_projections μ μ Prod.fst Prod.fst measurable_fst measurable_fst
    (fiberGlobalOperator μ A B hB U) (fiberGlobalOperator_commutes_base_projections μ A B hB U hU)
      s hs d e f

theorem fiberMultiplicity_eq_of_intertwiner
    (A B : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (U : Lp ℂ 2 (fiberRestrictedMeasure μ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure μ B))
    (hU : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (fiberRestrictedMeasure μ A)),
      U (indicatorL2 (fiberRestrictedMeasure μ A) (hs.preimage measurable_fst) f) =
        indicatorL2 (fiberRestrictedMeasure μ B) (hs.preimage measurable_fst) (U f)) :
    fiberMultiplicity A =ᵐ[μ] fiberMultiplicity B := by
  let T := fiberGlobalOperator μ A B hB U
  let V := fiberGlobalOperator μ B A hA U.symm
  have hInv : ∀ (s : Set X) (hs : MeasurableSet s)
      (f : Lp ℂ 2 (fiberRestrictedMeasure μ B)),
      U.symm (indicatorL2 (fiberRestrictedMeasure μ B) (hs.preimage measurable_fst) f) =
        indicatorL2 (fiberRestrictedMeasure μ A) (hs.preimage measurable_fst) (U.symm f) := by
    intro s hs f
    apply U.injective
    rw [LinearIsometryEquiv.apply_symm_apply, hU s hs, LinearIsometryEquiv.apply_symm_apply]
  have hcol (e : ℕ) : (fun x => ∑' d : ℕ,
      moduleEntryMass μ (matrixCoefficient μ μ T d e) x) =ᵐ[μ]
      (A e).indicator (fun _ => (1 : ℝ≥0∞)) := by
    apply module_column_mass_ae_eq μ (fun d => matrixCoefficient μ μ T d e)
      (fun d => fiberMatrixCoefficient_commutes μ A B hB U hU d e) (A e) (hA e)
    · intro f
      exact summable_coefficient_norm_sq μ (T (injection μ e f))
    · exact fiberGlobalOperator_column_norm_sq μ A B hA hB U e
  have hcolV (d : ℕ) : (fun x => ∑' e : ℕ,
      moduleEntryMass μ (matrixCoefficient μ μ V e d) x) =ᵐ[μ]
      (B d).indicator (fun _ => (1 : ℝ≥0∞)) := by
    apply module_column_mass_ae_eq μ (fun e => matrixCoefficient μ μ V e d)
      (fun e => fiberMatrixCoefficient_commutes μ B A hA U.symm hInv e d) (B d) (hB d)
    · intro f
      exact summable_coefficient_norm_sq μ (V (injection μ d f))
    · exact fiberGlobalOperator_column_norm_sq μ B A hB hA U.symm d
  have hentry (d e : ℕ) : moduleEntryMass μ (matrixCoefficient μ μ T d e) =ᵐ[μ]
      moduleEntryMass μ (matrixCoefficient μ μ V e d) := by
    have h := moduleEntryMass_adjoint_ae_eq μ (matrixCoefficient μ μ T d e)
      (fiberMatrixCoefficient_commutes μ A B hB U hU d e)
    rw [matrixCoefficient_adjoint] at h
    have hAdj : T.adjoint = V := fiberGlobalOperator_adjoint μ A B hA hB U
    rw [hAdj] at h
    exact h
  have hrow (d : ℕ) : (fun x => ∑' e : ℕ,
      moduleEntryMass μ (matrixCoefficient μ μ T d e) x) =ᵐ[μ]
      (B d).indicator (fun _ => (1 : ℝ≥0∞)) := by
    filter_upwards [ae_all_iff.mpr (fun e => hentry d e), hcolV d] with x hx hv
    exact (tsum_congr (fun e => hx e)).trans hv
  filter_upwards [ae_all_iff.mpr hcol, ae_all_iff.mpr hrow] with x hc hr
  change (∑' e : ℕ, (A e).indicator (fun _ => (1 : ℝ≥0∞)) x) =
    ∑' d : ℕ, (B d).indicator (fun _ => (1 : ℝ≥0∞)) x
  calc
    (∑' e : ℕ, (A e).indicator (fun _ => (1 : ℝ≥0∞)) x) =
        ∑' e : ℕ, ∑' d : ℕ, moduleEntryMass μ (matrixCoefficient μ μ T d e) x :=
      tsum_congr (fun e => (hc e).symm)
    _ = ∑' d : ℕ, ∑' e : ℕ, moduleEntryMass μ (matrixCoefficient μ μ T d e) x := ENNReal.tsum_comm
    _ = ∑' d : ℕ, (B d).indicator (fun _ => (1 : ℝ≥0∞)) x := tsum_congr hr

end
end MeasureUnitary

#print axioms MeasureUnitary.fiberMultiplicity_eq_of_intertwiner
