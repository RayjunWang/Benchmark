import OperatorNormalization
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.Semicontinuity.Basic

/-! The operator norm is lower semicontinuous in SOT, and the reversible
normalization T ↦ T/(1+‖T‖) is Borel for the correct strong Borel structure. -/

open Set MeasureTheory

namespace OperatorCoding

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

noncomputable abbrev operatorStrongTopologyOn : TopologicalSpace (H →L[ℂ] H) :=
  TopologicalSpace.induced (fun T : H →L[ℂ] H => fun x : H => T x) inferInstance

noncomputable abbrev operatorStrongBorel : MeasurableSpace (H →L[ℂ] H) :=
  @borel (H →L[ℂ] H) (operatorStrongTopologyOn H)

variable {H}

theorem operatorNorm_measurable :
    @Measurable (H →L[ℂ] H) ℝ (operatorStrongBorel H) inferInstance (fun T => ‖T‖) := by
  letI : TopologicalSpace (H →L[ℂ] H) := operatorStrongTopologyOn H
  letI : MeasurableSpace (H →L[ℂ] H) := operatorStrongBorel H
  letI : BorelSpace (H →L[ℂ] H) := ⟨rfl⟩
  change Measurable (fun T : H →L[ℂ] H => ‖T‖)
  have hlsc : LowerSemicontinuous (fun T : H →L[ℂ] H => ‖T‖) := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro r
    by_cases hr : 0 ≤ r
    · have hset : (fun T : H →L[ℂ] H => ‖T‖) ⁻¹' Iic r =
          ⋂ x : H, {T : H →L[ℂ] H | ‖T x‖ ≤ r * ‖x‖} := by
        ext T
        simp only [mem_preimage, mem_Iic, mem_iInter, mem_setOf_eq,
          ContinuousLinearMap.opNorm_le_iff hr]
      rw [hset]
      apply isClosed_iInter
      intro x
      have he : Continuous (fun T : H →L[ℂ] H => T x) :=
        (continuous_apply x).comp continuous_induced_dom
      exact isClosed_le he.norm continuous_const
    · have hset : (fun T : H →L[ℂ] H => ‖T‖) ⁻¹' Iic r = ∅ := by
        ext T
        simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
        exact not_le.mpr (lt_of_lt_of_le (lt_of_not_ge hr) (norm_nonneg T))
      rw [hset]
      exact isClosed_empty
  exact hlsc.measurable

theorem normalizeOperator_measurable :
    @Measurable (H →L[ℂ] H) (H →L[ℂ] H)
      (operatorStrongBorel H) (operatorStrongBorel H) normalizeOperator := by
  letI : TopologicalSpace (H →L[ℂ] H) := operatorStrongTopologyOn H
  letI : MeasurableSpace (H →L[ℂ] H) := operatorStrongBorel H
  letI : BorelSpace (H →L[ℂ] H) := ⟨rfl⟩
  have hn : Measurable (fun T : H →L[ℂ] H => ‖T‖) := operatorNorm_measurable
  have hc : Measurable (fun T : H →L[ℂ] H => (((1 + ‖T‖)⁻¹ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp ((measurable_const.add hn).inv)
  have hsmul : Continuous (fun p : ℂ × (H →L[ℂ] H) => p.1 • p.2) := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro x
    have he : Continuous (fun p : ℂ × (H →L[ℂ] H) => p.2 x) :=
      ((continuous_apply x).comp continuous_induced_dom).comp continuous_snd
    exact continuous_fst.smul he
  exact hsmul.measurable.comp (hc.prodMk measurable_id)

end OperatorCoding

#print axioms OperatorCoding.normalizeOperator_measurable
