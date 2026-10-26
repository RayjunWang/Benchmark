import L2ProjectionCommutantNormal
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Pointwise squared-mass identities of actual finite-base L² module
operators, obtained from their localized Parseval identities. -/

open MeasureTheory Filter Set
open scoped ENNReal

set_option maxHeartbeats 1500000

namespace MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

def moduleEntryMass (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal (‖T (constantOneL2 μ) x‖ ^ 2)

theorem moduleEntryMass_measurable (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    Measurable (moduleEntryMass μ T) :=
  (((Lp.stronglyMeasurable (T (constantOneL2 μ))).measurable.norm).pow_const 2).ennreal_ofReal

theorem moduleEntryMass_setLIntegral (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (s : Set X) (hs : MeasurableSet s) :
    (∫⁻ x in s, moduleEntryMass μ T x ∂μ) =
      ENNReal.ofReal (‖indicatorL2 μ hs (T (constantOneL2 μ))‖ ^ 2) := by
  rw [← vectorDensityMeasure_apply μ hs (T (constantOneL2 μ))]
  exact (withDensity_apply _ hs).symm

theorem moduleEntryMass_adjoint_ae_eq (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f)) :
    moduleEntryMass μ T =ᵐ[μ] moduleEntryMass μ T.adjoint := by
  apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (moduleEntryMass_measurable μ T) (moduleEntryMass_measurable μ T.adjoint)
  intro s hs _hfin
  rw [moduleEntryMass_setLIntegral μ T s hs, moduleEntryMass_setLIntegral μ T.adjoint s hs,
    ← hT s hs, ← projectionCommutant_adjoint μ T hT s hs,
    projectionCommutant_norm_adjoint μ T hT]

theorem indicatorL2_commute (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (f : Lp ℂ 2 μ) :
    indicatorL2 μ hs (indicatorL2 μ ht f) = indicatorL2 μ ht (indicatorL2 μ hs f) := by
  apply Lp.ext
  filter_upwards [indicatorL2_coe μ hs (indicatorL2 μ ht f), indicatorL2_coe μ ht f,
    indicatorL2_coe μ ht (indicatorL2 μ hs f), indicatorL2_coe μ hs f]
      with x hst ht' hts hs'
  rw [hst, hts]
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp [hxs,hxt,ht',hs']

theorem indicatorOne_squareMass (A : Set X) (hA : MeasurableSet A) :
    (fun x => ENNReal.ofReal (‖indicatorL2 μ hA (constantOneL2 μ) x‖ ^ 2)) =ᵐ[μ]
      A.indicator (fun _ => (1 : ℝ≥0∞)) := by
  filter_upwards [indicatorL2_coe μ hA (constantOneL2 μ), constantOneL2_coe μ] with x hi h1
  rw [hi]
  by_cases hx : x ∈ A <;> simp [hx,h1]

theorem module_column_mass_ae_eq
    (T : ℕ → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ d (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T d (indicatorL2 μ hs f) = indicatorL2 μ hs (T d f))
    (A : Set X) (hA : MeasurableSet A)
    (hsum : ∀ f : Lp ℂ 2 μ, Summable (fun d => ‖T d f‖ ^ 2))
    (hnorm : ∀ f : Lp ℂ 2 μ, (∑' d, ‖T d f‖ ^ 2) = ‖indicatorL2 μ hA f‖ ^ 2) :
    (fun x => ∑' d : ℕ, moduleEntryMass μ (T d) x) =ᵐ[μ]
      A.indicator (fun _ => (1 : ℝ≥0∞)) := by
  apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (Measurable.ennreal_tsum (fun d => moduleEntryMass_measurable μ (T d)))
    (measurable_const.indicator hA)
  intro s hs _hfin
  calc
    (∫⁻ x in s, ∑' d : ℕ, moduleEntryMass μ (T d) x ∂μ) =
        ∑' d : ℕ, ∫⁻ x in s, moduleEntryMass μ (T d) x ∂μ :=
      lintegral_tsum (fun d => (moduleEntryMass_measurable μ (T d)).aemeasurable)
    _ = ∑' d : ℕ, ENNReal.ofReal (‖T d (indicatorL2 μ hs (constantOneL2 μ))‖ ^ 2) := by
      apply tsum_congr
      intro d
      rw [moduleEntryMass_setLIntegral μ (T d) s hs, ← hT d s hs]
    _ = ENNReal.ofReal (∑' d : ℕ, ‖T d (indicatorL2 μ hs (constantOneL2 μ))‖ ^ 2) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hsum _)).symm
    _ = ENNReal.ofReal (‖indicatorL2 μ hA (indicatorL2 μ hs (constantOneL2 μ))‖ ^ 2) := by rw [hnorm]
    _ = ENNReal.ofReal (‖indicatorL2 μ hs (indicatorL2 μ hA (constantOneL2 μ))‖ ^ 2) := by
      rw [indicatorL2_commute]
    _ = ∫⁻ x in s, ENNReal.ofReal (‖indicatorL2 μ hA (constantOneL2 μ) x‖ ^ 2) ∂μ := by
      rw [← vectorDensityMeasure_apply μ hs]
      exact withDensity_apply _ hs
    _ = ∫⁻ x in s, A.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ :=
      lintegral_congr_ae (ae_restrict_of_ae (indicatorOne_squareMass μ A hA))

end
end MeasureUnitary

#print axioms MeasureUnitary.moduleEntryMass_adjoint_ae_eq
#print axioms MeasureUnitary.module_column_mass_ae_eq
