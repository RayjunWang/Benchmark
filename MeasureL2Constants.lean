import MeasureCantorAmplified
import HilbertSequenceTopology
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.LinearAlgebra.Dimension.Finite

/-! A genuine isometric copy of the coefficient Hilbert space inside
Hilbert-valued L² of a probability measure. This proves that the amplified
Cantor representation has infinite-dimensional fibers, including at atoms. -/

open MeasureTheory Set
open scoped ENNReal

namespace MeasureUnitary

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem constantVectorL2_norm (v : E) : ‖constantVectorL2 μ v‖ = ‖v‖ := by
  rw [constantVectorL2, Lp.norm_toLp,
    eLpNorm_const' v (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
  simp

noncomputable def constantVectorLI : E →ₗᵢ[ℂ] Lp E 2 μ where
  toFun := constantVectorL2 μ
  map_add' := by
    intro v w
    apply Lp.ext
    filter_upwards [constantVectorL2_coe μ (v + w), constantVectorL2_coe μ v,
      constantVectorL2_coe μ w, Lp.coeFn_add (constantVectorL2 μ v) (constantVectorL2 μ w)]
      with x hvw hv hw ha
    simp only [Pi.add_apply] at ha
    rw [hvw, ha, hv, hw]
  map_smul' := by
    intro c v
    apply Lp.ext
    filter_upwards [constantVectorL2_coe μ (c • v), constantVectorL2_coe μ v,
      Lp.coeFn_smul c (constantVectorL2 μ v)] with x hcv hv hs
    simp only [Pi.smul_apply] at hs
    simp only [RingHom.id_apply]
    rw [hcv, hs, hv]
  norm_map' := constantVectorL2_norm μ

theorem constantVectorL2_linearIndependent {ι : Type*} {v : ι → E}
    (hv : LinearIndependent ℂ v) :
    LinearIndependent ℂ (fun i => constantVectorL2 μ (v i)) :=
  hv.map' (constantVectorLI μ).toLinearMap
    (LinearMap.ker_eq_bot.mpr (constantVectorLI μ).injective)

theorem canonicalHilbert_single_linearIndependent :
    LinearIndependent ℂ (fun i : ℕ => (lp.single 2 i (1 : ℂ) : OperatorCoding.CanonicalHilbert)) := by
  let b : HilbertBasis ℕ ℂ OperatorCoding.CanonicalHilbert :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hb : (fun i => b i) = fun i => (lp.single 2 i (1 : ℂ) : OperatorCoding.CanonicalHilbert) := by
    funext i
    rw [← b.repr_symm_single]
    rfl
  rw [← hb]
  exact b.orthonormal.linearIndependent

theorem amplifiedL2_not_finiteDimensional :
    ¬ FiniteDimensional ℂ (Lp OperatorCoding.CanonicalHilbert 2 μ) := by
  intro h
  letI := h
  have hi := constantVectorL2_linearIndependent μ canonicalHilbert_single_linearIndependent
  exact Module.Finite.not_linearIndependent_of_infinite _ hi

instance cantor_countablyGenerated : MeasurableSpace.CountablyGenerated CantorSpace where
  isCountablyGenerated :=
    ⟨Set.range cantorCylinder, Set.countable_range _, cantorCylinder_generates.symm⟩

instance amplifiedL2_secondCountable (ν : Measure CantorSpace) [SFinite ν] :
    SecondCountableTopology (Lp OperatorCoding.CanonicalHilbert 2 ν) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  infer_instance

end MeasureUnitary

#print axioms MeasureUnitary.amplifiedL2_not_finiteDimensional
