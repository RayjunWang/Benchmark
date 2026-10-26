import L2ModuleCommutant
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The finite-measure multiplication algebra is commutative and closed
under adjoints. In particular, a projection-commuting operator is normal.
This avoids introducing any abstract semifinite trace in the corner proof. -/

open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace

namespace MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem inner_indicatorL2 (s : Set X) (hs : MeasurableSet s) (f g : Lp ℂ 2 μ) :
    inner ℂ (indicatorL2 μ hs f) g = inner ℂ f (indicatorL2 μ hs g) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [indicatorL2_coe μ hs f, indicatorL2_coe μ hs g] with x hf hg
  rw [hf, hg]
  by_cases hx : x ∈ s <;> simp [hx]

theorem projectionCommutant_adjoint (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f)) :
    ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T.adjoint (indicatorL2 μ hs f) = indicatorL2 μ hs (T.adjoint f) := by
  intro s hs f
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_indicatorL2,
    ← hT, ← ContinuousLinearMap.adjoint_inner_right, inner_indicatorL2]

variable [IsFiniteMeasure μ]

theorem projectionCommutant_commute
    (T S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f))
    (hS : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      S (indicatorL2 μ hs f) = indicatorL2 μ hs (S f)) :
    T.comp S = S.comp T := by
  have hTm := projectionCommutant_eq_multiplier μ T hT
  have hSm := projectionCommutant_eq_multiplier μ S hS
  apply ContinuousLinearMap.ext
  intro f
  change T (S f) = S (T f)
  apply Lp.ext
  filter_upwards [boundedMultiplierL2_coe μ (projectionCommutantSymbol μ T hT) (S f),
    boundedMultiplierL2_coe μ (projectionCommutantSymbol μ S hS) f,
    boundedMultiplierL2_coe μ (projectionCommutantSymbol μ S hS) (T f),
    boundedMultiplierL2_coe μ (projectionCommutantSymbol μ T hT) f]
      with x hTS hSf hST hTf
  rw [← hTm] at hTS hTf
  rw [← hSm] at hSf hST
  rw [hTS, hST, hSf, hTf]
  ring

theorem projectionCommutant_norm_adjoint
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f)) (f : Lp ℂ 2 μ) :
    ‖T f‖ = ‖T.adjoint f‖ := by
  have hcomm := projectionCommutant_commute μ T T.adjoint hT
    (projectionCommutant_adjoint μ T hT)
  have hnormal : IsStarNormal T := ⟨by
    change T.adjoint.comp T = T.comp T.adjoint
    exact hcomm.symm⟩
  exact (ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint.mp hnormal) f

end
end MeasureUnitary

#print axioms MeasureUnitary.projectionCommutant_norm_adjoint
