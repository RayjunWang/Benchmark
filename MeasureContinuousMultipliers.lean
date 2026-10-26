import MeasureCantorGram
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-! The genuine continuous-function multiplication representation on
Hilbert-valued L², including its bounded linear and star-algebra structures. -/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureUnitary

noncomputable section

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [CompactSpace α] [SecondCountableTopology α]
  (μ : Measure α) [IsFiniteMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def continuousMultiplierL2 : C(α, ℂ) →L[ℂ] (Lp E 2 μ →L[ℂ] Lp E 2 μ) :=
  ((ContinuousLinearMap.lsmul ℂ ℂ (E := E)).holderL μ ∞ 2 2).comp
    (ContinuousMap.toLp ∞ μ ℂ)

theorem continuousMultiplierL2_coe (g : C(α, ℂ)) (f : Lp E 2 μ) :
    continuousMultiplierL2 μ g f =ᵐ[μ] fun x => g x • f x := by
  have hh := (ContinuousLinearMap.lsmul ℂ ℂ (E := E)).coeFn_holder (r := 2)
    (ContinuousMap.toLp ∞ μ ℂ g) f
  filter_upwards [hh, ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) μ g] with x hh hg
  exact hh.trans (by rw [hg]; rfl)

theorem continuousMultiplierL2_one : continuousMultiplierL2 (E := E) μ (1 : C(α, ℂ)) = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [continuousMultiplierL2_coe μ (1 : C(α, ℂ)) f] with x hx
  simpa using hx

theorem continuousMultiplierL2_mul (g h : C(α, ℂ)) :
    continuousMultiplierL2 (E := E) μ (g * h) = continuousMultiplierL2 μ g * continuousMultiplierL2 μ h := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [continuousMultiplierL2_coe μ (g * h) f,
    continuousMultiplierL2_coe μ g (continuousMultiplierL2 μ h f), continuousMultiplierL2_coe μ h f]
    with x hgh hg hh
  change (continuousMultiplierL2 μ (g * h) f) x =
    (continuousMultiplierL2 μ g (continuousMultiplierL2 μ h f)) x
  rw [hgh, hg, hh]
  exact mul_smul _ _ _

theorem continuousMultiplierL2_algebraMap (c : ℂ) :
    continuousMultiplierL2 (E := E) μ (algebraMap ℂ C(α, ℂ) c) =
      algebraMap ℂ (Lp E 2 μ →L[ℂ] Lp E 2 μ) c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, continuousMultiplierL2_one,
    Algebra.algebraMap_eq_smul_one]

theorem continuousMultiplierL2_star (g : C(α, ℂ)) :
    continuousMultiplierL2 (E := E) μ (star g) = star (continuousMultiplierL2 (E := E) μ g) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f h
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [continuousMultiplierL2_coe μ (star g) f,
    continuousMultiplierL2_coe μ g h] with x hf hh
  rw [hf, hh]
  simp only [ContinuousMap.star_apply, inner_smul_left, inner_smul_right, starRingEnd_apply, star_star]

def continuousMultiplierStarAlgHom : C(α, ℂ) →⋆ₐ[ℂ] (Lp E 2 μ →L[ℂ] Lp E 2 μ) where
  toFun := continuousMultiplierL2 μ
  map_zero' := map_zero _
  map_one' := continuousMultiplierL2_one μ
  map_add' := map_add _
  map_mul' := continuousMultiplierL2_mul μ
  commutes' := continuousMultiplierL2_algebraMap μ
  map_star' := continuousMultiplierL2_star μ

theorem continuousMultiplierL2_phase (c : C(α, ℂ)) (hnorm : ∀ x, ‖c x‖ = 1) (f : Lp E 2 μ) :
    continuousMultiplierL2 μ c f = phaseEquiv μ c c.continuous.measurable hnorm f := by
  apply Lp.ext
  exact (continuousMultiplierL2_coe μ c f).trans (phaseMap_coe μ c c.continuous.measurable hnorm f).symm

end

end MeasureUnitary

#print axioms MeasureUnitary.continuousMultiplierStarAlgHom
