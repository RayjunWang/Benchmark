import UnitaryCircleFunctionalCalculus
import UnitaryCyclicProjectionBorel
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! The continuous functional calculus preserves the actual closed
Laurent-orbit cyclic subspace. The proof uses a closed star subalgebra
and Stone--Weierstrass, with no spectral theorem assumed. -/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace CStarAlgebra

set_option maxHeartbeats 2000000

namespace OperatorCoding

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]

def cyclicPreservingFunctions (U : StrongUnitary H) (v : H) :
    StarSubalgebra ℂ C(SpectralCircle, ℂ) where
  carrier := {f | (∀ x ∈ cyclicSpan U v, unitaryCircleRepresentation U f x ∈ cyclicSpan U v) ∧
    (∀ x ∈ cyclicSpan U v, unitaryCircleRepresentation U (star f) x ∈ cyclicSpan U v)}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro f g hf hg
    constructor
    · intro x hx
      simpa only [map_add, ContinuousLinearMap.add_apply] using
        (cyclicSpan U v).add_mem (hf.1 x hx) (hg.1 x hx)
    · intro x hx
      simpa only [star_add, map_add, ContinuousLinearMap.add_apply] using
        (cyclicSpan U v).add_mem (hf.2 x hx) (hg.2 x hx)
  mul_mem' := by
    intro f g hf hg
    constructor
    · intro x hx
      simpa only [map_mul, ContinuousLinearMap.mul_apply] using hf.1 _ (hg.1 x hx)
    · intro x hx
      simpa only [star_mul, map_mul, ContinuousLinearMap.mul_apply] using hg.2 _ (hf.2 x hx)
  algebraMap_mem' := by
    intro c
    constructor
    · intro x hx
      simpa only [Algebra.algebraMap_eq_smul_one, map_smul, map_one,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] using
        (cyclicSpan U v).smul_mem c hx
    · intro x hx
      simpa only [Algebra.algebraMap_eq_smul_one, star_smul, star_one, map_smul, map_one,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] using
        (cyclicSpan U v).smul_mem (star c) hx
  star_mem' := by
    intro f hf
    exact ⟨hf.2, by simpa only [star_star] using hf.1⟩

theorem cyclicPreservingFunctions_closed (U : StrongUnitary H) (v : H) :
    IsClosed (cyclicPreservingFunctions U v : Set C(SpectralCircle, ℂ)) := by
  have heval (x : H) : Continuous (fun f : C(SpectralCircle, ℂ) => unitaryCircleRepresentation U f x) :=
    (ContinuousLinearMap.apply ℂ H x).continuous.comp (unitaryCircleRepresentation_continuous U)
  have hc := cyclicSpan_isClosed U v
  have hfirst : IsClosed {f : C(SpectralCircle, ℂ) |
      ∀ x ∈ cyclicSpan U v, unitaryCircleRepresentation U f x ∈ cyclicSpan U v} := by
    simpa only [Set.setOf_forall] using
      isClosed_iInter (fun x : H => isClosed_iInter (fun _hx : x ∈ cyclicSpan U v => hc.preimage (heval x)))
  have hsecond : IsClosed {f : C(SpectralCircle, ℂ) |
      ∀ x ∈ cyclicSpan U v, unitaryCircleRepresentation U (star f) x ∈ cyclicSpan U v} := by
    simpa only [Set.setOf_forall] using
      isClosed_iInter (fun x : H => isClosed_iInter (fun _hx : x ∈ cyclicSpan U v =>
        hc.preimage ((heval x).comp continuous_star)))
  exact hfirst.inter hsecond

theorem circleCoordinate_mem_cyclicPreservingFunctions (U : StrongUnitary H) (v : H) :
    circleCoordinate ∈ cyclicPreservingFunctions U v := by
  constructor
  · intro x hx
    rw [unitaryCircleRepresentation_coordinate]
    simpa only [zpow_one] using cyclicSpan_zpow_invariant U v 1 x hx
  · intro x hx
    rw [unitaryCircleRepresentation_star_coordinate, U.adjoint_eq_symm]
    simpa only [zpow_neg_one] using cyclicSpan_zpow_invariant U v (-1) x hx

theorem unitaryCircleRepresentation_cyclicSpan_invariant (U : StrongUnitary H) (v : H)
    (f : C(SpectralCircle, ℂ)) (x : H) (hx : x ∈ cyclicSpan U v) :
    unitaryCircleRepresentation U f x ∈ cyclicSpan U v := by
  let A := cyclicPreservingFunctions U v
  have hsep : A.SeparatesPoints := by
    intro z w hzw
    refine ⟨circleCoordinate, ⟨circleCoordinate,
      circleCoordinate_mem_cyclicPreservingFunctions U v, rfl⟩, ?_⟩
    intro he
    exact hzw (Subtype.ext he)
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have hf : f ∈ closure (A : Set C(SpectralCircle, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe, htop]
    trivial
  exact ((cyclicPreservingFunctions_closed U v).closure_subset hf).1 x hx

end
end OperatorCoding

#print axioms OperatorCoding.unitaryCircleRepresentation_cyclicSpan_invariant
