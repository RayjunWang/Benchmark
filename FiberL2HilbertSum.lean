import FiberMultiplicityOperators
import HilbertFamilyCongr

/-! Actual identification of the Hilbert sum of L²(μ|A_i) with the L²
space of the corresponding measurable counting fibers. -/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 2000000

namespace MeasureUnitary

open MeasureEquivalenceL2Coefficients MeasureEquivalenceL2Restriction

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem fiberInjection_supported (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (i : ℕ) (f : Lp ℂ 2 (μ.restrict (A i))) :
    indicatorL2 (fiberAmbientMeasure μ) (measureFiberSet_measurable A hA)
      (injection μ i (zeroExtend μ (A i) (hA i) f)) =
        injection μ i (zeroExtend μ (A i) (hA i) f) := by
  rw [← fiber_injection_indicator μ A hA i]
  have hsupport : indicatorL2 μ (hA i) (zeroExtend μ (A i) (hA i) f) =
      zeroExtend μ (A i) (hA i) f := by
    rw [← zeroExtend_restrict μ (A i) (hA i), restrict_zeroExtend]
  rw [hsupport]

def fiberComponentInjection (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i)) (i : ℕ) :
    Lp ℂ 2 (μ.restrict (A i)) →ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure μ A) where
  toLinearMap := ((restrictCLM (fiberAmbientMeasure μ) (measureFiberSet A)).comp
    ((injectionLI μ i).toContinuousLinearMap.comp
      (zeroExtendLI μ (A i) (hA i)).toContinuousLinearMap)).toLinearMap
  norm_map' f := by
    change ‖restrictMap (fiberAmbientMeasure μ) (measureFiberSet A)
      (injection μ i (zeroExtend μ (A i) (hA i) f))‖ = ‖f‖
    rw [← zeroExtend_norm (fiberAmbientMeasure μ) (measureFiberSet A)
      (measureFiberSet_measurable A hA), zeroExtend_restrict,
      fiberInjection_supported μ A hA i f, injection_norm, zeroExtend_norm]

theorem fiberComponentInjection_zeroExtend (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (i : ℕ) (f : Lp ℂ 2 (μ.restrict (A i))) :
    zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA)
      (fiberComponentInjection μ A hA i f) = injection μ i (zeroExtend μ (A i) (hA i) f) := by
  change zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA)
    (restrictMap (fiberAmbientMeasure μ) (measureFiberSet A)
      (injection μ i (zeroExtend μ (A i) (hA i) f))) = _
  rw [zeroExtend_restrict, fiberInjection_supported μ A hA i f]

theorem fiberComponentInjection_inner (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (i : ℕ) (f : Lp ℂ 2 (μ.restrict (A i))) (g : Lp ℂ 2 (fiberRestrictedMeasure μ A)) :
    inner ℂ (fiberComponentInjection μ A hA i f) g =
      inner ℂ f (restrictMap μ (A i)
        (coefficient μ i (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A)
          (measureFiberSet_measurable A hA) g))) := by
  rw [← (zeroExtendLI (fiberAmbientMeasure μ) (measureFiberSet A)
    (measureFiberSet_measurable A hA)).inner_map_map,
    ]
  change inner ℂ (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA)
    (fiberComponentInjection μ A hA i f)) (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A)
    (measureFiberSet_measurable A hA) g) = _
  rw [fiberComponentInjection_zeroExtend, inner_injection_coefficient, inner_zeroExtend_restrict]

theorem fiberComponents_orthogonal (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    OrthogonalFamily ℂ (fun i => Lp ℂ 2 (μ.restrict (A i))) (fiberComponentInjection μ A hA) := by
  intro i j hij f g
  rw [← (zeroExtendLI (fiberAmbientMeasure μ) (measureFiberSet A)
    (measureFiberSet_measurable A hA)).inner_map_map,
    ]
  change inner ℂ (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA)
    (fiberComponentInjection μ A hA i f)) (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A)
    (measureFiberSet_measurable A hA) (fiberComponentInjection μ A hA j g)) = 0
  rw [fiberComponentInjection_zeroExtend, fiberComponentInjection_zeroExtend,
    inner_injection_coefficient, coefficient_injection, if_neg hij, inner_zero_right]

theorem fiberCoefficient_supported (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (i : ℕ) (g : Lp ℂ 2 (fiberRestrictedMeasure μ A)) :
    indicatorL2 μ (hA i) (coefficient μ i
      (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA) g)) =
    coefficient μ i
      (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA) g) := by
  have hsupport : indicatorL2 (fiberAmbientMeasure μ) (measureFiberSet_measurable A hA)
      (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA) g) =
      zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA) g := by
    rw [← zeroExtend_restrict (fiberAmbientMeasure μ) (measureFiberSet A)
      (measureFiberSet_measurable A hA), restrict_zeroExtend]
  have h := coefficient_indicator μ id measurable_id (measureFiberSet A)
    (measureFiberSet_measurable A hA) i
    (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA) g)
  change coefficient μ i (indicatorL2 (fiberAmbientMeasure μ) (measureFiberSet_measurable A hA)
    (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA) g)) = _ at h
  rw [hsupport] at h
  exact h.symm

theorem fiberComponents_total (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    ⊤ ≤ (⨆ i : ℕ, (fiberComponentInjection μ A hA i).toLinearMap.range).topologicalClosure := by
  let S := (⨆ i : ℕ, (fiberComponentInjection μ A hA i).toLinearMap.range).topologicalClosure
  letI : CompleteSpace S := (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe
  have hbot : Sᗮ = ⊥ := by
    apply le_antisymm _ bot_le
    intro g hg
    have hcoeff (i : ℕ) : coefficient μ i
        (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA) g) = 0 := by
      let z := restrictMap μ (A i) (coefficient μ i
        (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA) g))
      have hz : z = 0 := by
        have hmem : fiberComponentInjection μ A hA i z ∈ S :=
          Submodule.le_topologicalClosure _ (le_iSup
            (fun j => (fiberComponentInjection μ A hA j).toLinearMap.range) i ⟨z,rfl⟩)
        have hip := hg _ hmem
        rw [fiberComponentInjection_inner] at hip
        exact inner_self_eq_zero.mp hip
      calc
        coefficient μ i (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A)
            (measureFiberSet_measurable A hA) g) = zeroExtend μ (A i) (hA i) z := by
          rw [zeroExtend_restrict, fiberCoefficient_supported μ A hA i g]
        _ = 0 := by
          rw [hz]
          exact (zeroExtendLI μ (A i) (hA i)).map_zero
    have hzero : zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A)
        (measureFiberSet_measurable A hA) g = 0 := by
      apply coefficient_ext μ
      intro i
      rw [hcoeff]
      exact ((coefficientCLM μ i).map_zero).symm
    have hn : ‖g‖ = 0 := by
      rw [← zeroExtend_norm (fiberAmbientMeasure μ) (measureFiberSet A)
        (measureFiberSet_measurable A hA), hzero, norm_zero]
    exact norm_eq_zero.mp hn
  exact le_of_eq (Submodule.orthogonal_eq_bot_iff.mp hbot).symm

def fiberL2HilbertSum (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    IsHilbertSum ℂ (fun i => Lp ℂ 2 (μ.restrict (A i))) (fiberComponentInjection μ A hA) :=
  IsHilbertSum.mk (fiberComponents_orthogonal μ A hA) (fiberComponents_total μ A hA)

def fiberL2SumEquiv (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    lp (fun i => Lp ℂ 2 (μ.restrict (A i))) 2 ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure μ A) :=
  (fiberL2HilbertSum μ A hA).linearIsometryEquiv.symm

end
end MeasureUnitary

#print axioms MeasureUnitary.fiberL2SumEquiv

