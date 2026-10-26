import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
A stationary coupling gives an actual contraction of L2. The operator
is the adjoint of the first-coordinate pullback followed by the
second-coordinate pullback. Its fixed vectors are precisely the
functions with equal pullbacks on the coupling.
-/

open MeasureTheory Filter
open scoped InnerProduct

namespace MeasureEquivalenceMarkov

section Hilbert

variable {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The contraction determined by two isometric embeddings into one
Hilbert space. -/
noncomputable def isometryTransition (i j : E →ₗᵢ[ℝ] F) : E →L[ℝ] E :=
  i.toContinuousLinearMap.adjoint ∘L j.toContinuousLinearMap

theorem isometryTransition_norm_le_one (i j : E →ₗᵢ[ℝ] F) :
    ‖isometryTransition i j‖ ≤ 1 := by
  have hi : ‖i.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  have hj : ‖j.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  calc
    _ ≤ ‖i.toContinuousLinearMap.adjoint‖ * ‖j.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul (by simpa using hi) hj (norm_nonneg _) zero_le_one
    _ = 1 := by norm_num

theorem isometryTransition_fixed_iff (i j : E →ₗᵢ[ℝ] F) (x : E) :
    isometryTransition i j x = x ↔ i x = j x := by
  constructor
  · intro hx
    have hip : inner ℝ (i x) (j x) = ‖x‖ ^ 2 := by
      change inner ℝ (i.toContinuousLinearMap x) (j.toContinuousLinearMap x) = ‖x‖ ^ 2
      rw [← ContinuousLinearMap.adjoint_inner_right]
      change inner ℝ x (isometryTransition i j x) = ‖x‖ ^ 2
      rw [hx, real_inner_self_eq_norm_sq]
    have hnorm : ‖i x - j x‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, i.norm_map, j.norm_map, hip]
      ring
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm))
  · intro hx
    change i.toContinuousLinearMap.adjoint (j x) = x
    rw [← hx]
    exact congrArg (fun A : E →L[ℝ] E => A x) i.adjoint_comp_self

end Hilbert

section Coupling

variable {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (J : Measure (Z × Z))
    (hfst : J.map Prod.fst = μ) (hsnd : J.map Prod.snd = μ)

/-- First-coordinate L2 pullback for an actual coupling with marginal μ. -/
noncomputable def couplingFirst : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 J :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.fst ⟨measurable_fst, hfst⟩

/-- Second-coordinate L2 pullback. -/
noncomputable def couplingSecond : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 J :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.snd ⟨measurable_snd, hsnd⟩

/-- The actual L2 transition operator determined by a stationary coupling. -/
noncomputable def couplingTransition : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  isometryTransition (couplingFirst μ J hfst) (couplingSecond μ J hsnd)

theorem couplingTransition_norm_le_one : ‖couplingTransition μ J hfst hsnd‖ ≤ 1 :=
  isometryTransition_norm_le_one _ _

/-- Its fixed functions are precisely those equal on the coupling's edges. -/
theorem couplingTransition_fixed_iff (f : Lp ℝ 2 μ) :
    couplingTransition μ J hfst hsnd f = f ↔
      ∀ᵐ z ∂J, f z.1 = f z.2 := by
  rw [couplingTransition, isometryTransition_fixed_iff]
  constructor
  · intro h
    have hae : couplingFirst μ J hfst f =ᵐ[J] couplingSecond μ J hsnd f :=
      Eventually.of_forall (fun z => congrArg (fun u : Lp ℝ 2 J => u z) h)
    filter_upwards [hae,
      Lp.coeFn_compMeasurePreserving f (show MeasurePreserving Prod.fst J μ from ⟨measurable_fst, hfst⟩),
      Lp.coeFn_compMeasurePreserving f (show MeasurePreserving Prod.snd J μ from ⟨measurable_snd, hsnd⟩)]
      with z hz h1 h2
    exact h1.symm.trans (hz.trans h2)
  · intro h
    apply Lp.ext
    filter_upwards [h,
      Lp.coeFn_compMeasurePreserving f (show MeasurePreserving Prod.fst J μ from ⟨measurable_fst, hfst⟩),
      Lp.coeFn_compMeasurePreserving f (show MeasurePreserving Prod.snd J μ from ⟨measurable_snd, hsnd⟩)]
      with z hz h1 h2
    exact h1.trans (hz.trans h2.symm)

end Coupling

end MeasureEquivalenceMarkov

#print axioms MeasureEquivalenceMarkov.isometryTransition_norm_le_one
#print axioms MeasureEquivalenceMarkov.isometryTransition_fixed_iff
#print axioms MeasureEquivalenceMarkov.couplingTransition_fixed_iff
