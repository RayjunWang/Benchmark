import UnitaryCircleFunctionalCalculus
import OperatorStrongExponential
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.UniformSpace.UniformApproximation

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace CStarAlgebra

set_option maxHeartbeats 1500000

noncomputable section

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]

def stronglyContinuousFunctions : Set C(SpectralCircle, ℂ) :=
  {f | ∀ x : H, Continuous (fun U : StrongUnitary H => unitaryCircleRepresentation U f x)}

theorem stronglyContinuousFunctions_closed :
    IsClosed (stronglyContinuousFunctions (H := H)) := by
  apply isClosed_of_closure_subset
  intro f hf x
  apply continuous_of_uniform_approx_of_continuous
  intro V hV
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_uniformity_dist.mp hV
  have hxpos : 0 < ‖x‖ + 1 := by positivity
  obtain ⟨g,hg,hgf⟩ := Metric.mem_closure_iff.mp hf (ε / (‖x‖+1)) (by positivity)
  have hfg : ‖f-g‖ < ε / (‖x‖+1) := by simpa only [dist_eq_norm, norm_sub_rev] using hgf
  refine ⟨fun U : StrongUnitary H => unitaryCircleRepresentation U g x, hg x, ?_⟩
  intro U
  apply hεV
  change dist (unitaryCircleRepresentation U f x) (unitaryCircleRepresentation U g x) < ε
  calc
    dist (unitaryCircleRepresentation U f x) (unitaryCircleRepresentation U g x) =
        ‖unitaryCircleRepresentation U (f-g) x‖ := by
          rw [dist_eq_norm,map_sub,ContinuousLinearMap.sub_apply]
    _ ≤ ‖unitaryCircleRepresentation U (f-g)‖ * ‖x‖ :=
      (unitaryCircleRepresentation U (f-g)).le_opNorm x
    _ ≤ ‖f-g‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_right (unitaryCircleRepresentation_norm_le U (f-g)) (norm_nonneg x)
    _ ≤ ‖f-g‖ * (‖x‖+1) :=
      mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    _ < (ε/(‖x‖+1)) * (‖x‖+1) := mul_lt_mul_of_pos_right hfg hxpos
    _ = ε := div_mul_cancel₀ _ (ne_of_gt hxpos)

def stronglyContinuousStarAlgebra : StarSubalgebra ℂ C(SpectralCircle, ℂ) where
  carrier := {f | f ∈ stronglyContinuousFunctions (H := H) ∧
    star f ∈ stronglyContinuousFunctions (H := H)}
  zero_mem' := by
    constructor <;> intro x <;>
      simpa only [map_zero,ContinuousLinearMap.zero_apply,star_zero] using
        (continuous_const (y := (0 : H)) : Continuous (fun _ : StrongUnitary H => (0 : H)))
  one_mem' := by
    constructor <;> intro x <;>
      simpa only [map_one,ContinuousLinearMap.one_apply,star_one] using
        (continuous_const (y := x) : Continuous (fun _ : StrongUnitary H => x))
  add_mem' := by
    intro f g hf hg
    constructor
    · intro x
      simpa only [map_add,ContinuousLinearMap.add_apply] using (hf.1 x).add (hg.1 x)
    · intro x
      simpa only [star_add,map_add,ContinuousLinearMap.add_apply] using (hf.2 x).add (hg.2 x)
  mul_mem' := by
    intro f g hf hg
    constructor
    · intro x
      simpa only [map_mul,ContinuousLinearMap.mul_apply] using
        strongOperator_continuous_action (A := fun U : StrongUnitary H => unitaryCircleRepresentation U f)
          hf.1 (fun U => unitaryCircleRepresentation_norm_le U f) (hg.1 x)
    · intro x
      simpa only [star_mul,map_mul,ContinuousLinearMap.mul_apply] using
        strongOperator_continuous_action (A := fun U : StrongUnitary H => unitaryCircleRepresentation U (star g))
          hg.2 (fun U => unitaryCircleRepresentation_norm_le U (star g)) (hf.2 x)
  algebraMap_mem' := by
    intro c
    constructor
    · intro x
      simpa only [Algebra.algebraMap_eq_smul_one,map_smul,map_one,
        ContinuousLinearMap.smul_apply,ContinuousLinearMap.one_apply] using
        (continuous_const (y := c • x) : Continuous (fun _ : StrongUnitary H => c • x))
    · intro x
      simpa only [Algebra.algebraMap_eq_smul_one,star_smul,star_one,map_smul,map_one,
        ContinuousLinearMap.smul_apply,ContinuousLinearMap.one_apply] using
        (continuous_const (y := star c • x) : Continuous (fun _ : StrongUnitary H => star c • x))
  star_mem' := by intro f hf; exact ⟨hf.2,by simpa only [star_star] using hf.1⟩

theorem stronglyContinuousStarAlgebra_closed :
    IsClosed (stronglyContinuousStarAlgebra (H := H) : Set C(SpectralCircle, ℂ)) :=
  stronglyContinuousFunctions_closed.inter (stronglyContinuousFunctions_closed.preimage continuous_star)

theorem circleCoordinate_mem_stronglyContinuousStarAlgebra :
    circleCoordinate ∈ stronglyContinuousStarAlgebra (H := H) := by
  constructor
  · intro x
    simpa only [unitaryCircleRepresentation_coordinate] using strongUnitary_continuous_eval x
  · intro x
    have hc : Continuous (fun U : StrongUnitary H => U⁻¹ x) :=
      (strongUnitary_continuous_eval x).comp continuous_inv
    simpa only [unitaryCircleRepresentation_star_coordinate,LinearIsometryEquiv.adjoint_eq_symm] using hc

theorem unitaryCircleRepresentation_strong_continuous (f : C(SpectralCircle, ℂ)) (x : H) :
    Continuous (fun U : StrongUnitary H => unitaryCircleRepresentation U f x) := by
  let A := stronglyContinuousStarAlgebra (H := H)
  have hsep : A.SeparatesPoints := by
    intro z w hzw
    refine ⟨circleCoordinate,⟨circleCoordinate,circleCoordinate_mem_stronglyContinuousStarAlgebra,rfl⟩,?_⟩
    intro he
    exact hzw (Subtype.ext he)
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have hf : f ∈ closure (A : Set C(SpectralCircle, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe,htop]
    trivial
  exact ((stronglyContinuousStarAlgebra_closed (H := H)).closure_subset hf).1 x

theorem unitaryCircleRepresentation_joint_continuous (f : C(SpectralCircle, ℂ)) :
    Continuous (fun p : StrongUnitary H × H => unitaryCircleRepresentation p.1 f p.2) :=
  strongOperator_continuous_action
    (fun x => (unitaryCircleRepresentation_strong_continuous f x).comp continuous_fst)
    (fun p => unitaryCircleRepresentation_norm_le p.1 f) continuous_snd

end OperatorCoding

#print axioms OperatorCoding.unitaryCircleRepresentation_joint_continuous
