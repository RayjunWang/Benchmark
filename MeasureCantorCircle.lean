import MeasureCantorTuple
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Real.Pi.Bounds

/-! An explicit continuous injection of Cantor space into a short circle
arc, with an actual continuous inverse on its image. -/

open MeasureTheory Set

namespace MeasureUnitary

noncomputable section

def cantorRealCoordinate (x : CantorSpace) : ℝ := cantorSetHomeomorphNatToBool.symm x

theorem cantorRealCoordinate_continuous : Continuous cantorRealCoordinate :=
  continuous_subtype_val.comp cantorSetHomeomorphNatToBool.symm.continuous

theorem cantorRealCoordinate_bounds (x : CantorSpace) :
    0 ≤ cantorRealCoordinate x ∧ cantorRealCoordinate x ≤ 1 :=
  cantorSet_subset_unitInterval (cantorSetHomeomorphNatToBool.symm x).property

theorem cantorRealCoordinate_injective : Function.Injective cantorRealCoordinate := by
  intro x y h
  apply cantorSetHomeomorphNatToBool.symm.injective
  exact Subtype.ext h

def cantorCirclePhase (x : CantorSpace) : ℂ := Complex.exp (cantorRealCoordinate x * Complex.I)

theorem cantorCirclePhase_continuous : Continuous cantorCirclePhase :=
  Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp cantorRealCoordinate_continuous).mul continuous_const)

theorem cantorCirclePhase_norm (x : CantorSpace) : ‖cantorCirclePhase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem cantorCirclePhase_arg (x : CantorSpace) : (cantorCirclePhase x).arg = cantorRealCoordinate x := by
  rw [cantorCirclePhase, Complex.arg_exp_mul_I]
  apply (toIocMod_eq_self Real.two_pi_pos).mpr
  obtain ⟨h0, h1⟩ := cantorRealCoordinate_bounds x
  constructor <;> linarith [Real.pi_gt_three]

theorem cantorCirclePhase_injective : Function.Injective cantorCirclePhase := by
  intro x y h
  apply cantorRealCoordinate_injective
  simpa only [cantorCirclePhase_arg] using congrArg Complex.arg h

def cantorCircleContinuousMap : C(CantorSpace, ℂ) := ⟨cantorCirclePhase, cantorCirclePhase_continuous⟩

end

end MeasureUnitary

#print axioms MeasureUnitary.cantorCirclePhase_injective
