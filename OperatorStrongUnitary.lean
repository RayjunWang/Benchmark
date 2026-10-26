import OperatorFreeGroup
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
The strong topology on the actual group of unitary operators.  A unitary is
represented by a surjective complex-linear isometry; the induced topology is
pointwise norm convergence on vectors, not the operator-norm topology.
-/

open Filter Topology

namespace OperatorCoding

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

abbrev StrongUnitary := H ≃ₗᵢ[ℂ] H

instance : TopologicalSpace (StrongUnitary H) :=
  TopologicalSpace.induced (fun u : StrongUnitary H => (u : H → H)) inferInstance

variable {H}

theorem strongUnitary_continuous_eval (x : H) :
    Continuous (fun u : StrongUnitary H => u x) :=
  (continuous_apply x).comp continuous_induced_dom

theorem strongUnitary_continuous_iff {α : Type*} [TopologicalSpace α]
    (f : α → StrongUnitary H) :
    Continuous f ↔ ∀ x, Continuous (fun a => f a x) := by
  constructor
  · intro h x
    exact (strongUnitary_continuous_eval x).comp h
  · intro h
    exact continuous_induced_rng.mpr (continuous_pi h)

theorem strongUnitary_continuous_action {α : Type*} [TopologicalSpace α]
    {u : α → StrongUnitary H} {x : α → H} (hu : Continuous u) (hx : Continuous x) :
    Continuous (fun a => u a (x a)) := by
  rw [continuous_iff_continuousAt]
  intro a
  apply tendsto_iff_dist_tendsto_zero.mpr
  have h₁ : Tendsto (fun b => dist (x b) (x a)) (𝓝 a) (𝓝 0) := by
    simpa using (hx.dist (continuous_const (y := x a))).tendsto a
  have h₂ : Tendsto (fun b => dist (u b (x a)) (u a (x a))) (𝓝 a) (𝓝 0) := by
    simpa using (((strongUnitary_continuous_eval (x a)).comp hu).dist
      (continuous_const (y := u a (x a)))).tendsto a
  apply squeeze_zero (fun b => dist_nonneg) (fun b => ?_) (by simpa using h₁.add h₂)
  calc
    dist (u b (x b)) (u a (x a)) ≤
        dist (u b (x b)) (u b (x a)) + dist (u b (x a)) (u a (x a)) := dist_triangle _ _ _
    _ = dist (x b) (x a) + dist (u b (x a)) (u a (x a)) := by
      congr 1
      exact (u b).toIsometryEquiv.dist_eq _ _

instance strongUnitary_topologicalGroup : IsTopologicalGroup (StrongUnitary H) where
  continuous_mul := by
    apply (strongUnitary_continuous_iff _).mpr
    intro x
    change Continuous (fun p : StrongUnitary H × StrongUnitary H => p.1 (p.2 x))
    exact strongUnitary_continuous_action
      (u := fun p : StrongUnitary H × StrongUnitary H => p.1)
      (x := fun p : StrongUnitary H × StrongUnitary H => p.2 x) continuous_fst
      ((strongUnitary_continuous_eval x).comp continuous_snd)
  continuous_inv := by
    apply (strongUnitary_continuous_iff _).mpr
    intro x
    rw [continuous_iff_continuousAt]
    intro u₀
    apply tendsto_iff_dist_tendsto_zero.mpr
    have h : Tendsto (fun u : StrongUnitary H => dist x (u (u₀⁻¹ x))) (𝓝 u₀) (𝓝 0) := by
      simpa using ((continuous_const (y := x)).dist
        (strongUnitary_continuous_eval (u₀⁻¹ x))).tendsto u₀
    convert h using 1
    funext u
    change dist ((u : H ≃ₗᵢ[ℂ] H).symm x) ((u₀ : H ≃ₗᵢ[ℂ] H).symm x) = _
    rw [← u.toIsometryEquiv.dist_eq]
    simp

/-- The free-group coding in the topology used by the manuscript. -/
def strongUnitaryRepresentationHomeomorph :
    (ℕ → StrongUnitary H) ≃ₜ (FreeGroup ℕ →* StrongUnitary H) :=
  freeGroupRepresentationHomeomorph

theorem strongUnitary_representation_conjugate_iff (u v : ℕ → StrongUnitary H) :
    RepresentationConjugate (FreeGroup.lift u) (FreeGroup.lift v) ↔
      TupleConjugate u v := lift_conjugate_iff u v

end OperatorCoding

#print axioms OperatorCoding.strongUnitary_topologicalGroup
#print axioms OperatorCoding.strongUnitaryRepresentationHomeomorph
