import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
The free-group step in the representation coding argument.  The topology on
homomorphisms is pointwise convergence, and this file applies to every
topological group, including the strong unitary group of a Hilbert space.
-/

namespace OperatorCoding

variable {ι G : Type*} [Group G]

/-- Simultaneous conjugacy of an indexed family in a group. -/
def TupleConjugate (u v : ι → G) : Prop :=
  ∃ w : G, ∀ i, w * u i * w⁻¹ = v i

/-- Conjugacy of group homomorphisms, by one fixed element of the target. -/
def RepresentationConjugate (ρ σ : FreeGroup ι →* G) : Prop :=
  ∃ w : G, ∀ g, w * ρ g * w⁻¹ = σ g

theorem lift_conjugate_iff (u v : ι → G) :
    RepresentationConjugate (FreeGroup.lift u) (FreeGroup.lift v) ↔
      TupleConjugate u v := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, fun i => by simpa using hw (FreeGroup.of i)⟩
  · rintro ⟨w, hw⟩
    refine ⟨w, fun g => ?_⟩
    induction g using FreeGroup.induction_on with
    | C1 => simp
    | of i => simpa using hw i
    | inv_of i hi =>
      simpa [mul_assoc] using congrArg Inv.inv hi
    | mul a b ha hb =>
      simp only [map_mul]
      rw [← ha, ← hb]
      simp [mul_assoc]

theorem conjugate_iff_generators (ρ σ : FreeGroup ι →* G) :
    RepresentationConjugate ρ σ ↔
      TupleConjugate (fun i => ρ (FreeGroup.of i)) (fun i => σ (FreeGroup.of i)) := by
  simpa only [FreeGroup.lift.apply_symm_apply] using
    lift_conjugate_iff (FreeGroup.lift.symm ρ) (FreeGroup.lift.symm σ)

section Topological

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The pointwise topology on group representations. -/
instance representationTopology : TopologicalSpace (FreeGroup ι →* G) :=
  TopologicalSpace.induced (fun ρ : FreeGroup ι →* G => (ρ : FreeGroup ι → G)) inferInstance

theorem continuous_lift_evaluation (g : FreeGroup ι) :
    Continuous (fun u : ι → G => FreeGroup.lift u g) := by
  induction g using FreeGroup.induction_on with
  | C1 => simpa using (continuous_const : Continuous (fun _ : ι → G => (1 : G)))
  | of i => simpa using (continuous_apply i : Continuous (fun u : ι → G => u i))
  | inv_of i hi => simpa using hi.inv
  | mul a b ha hb => simpa using ha.mul hb

theorem continuous_lift : Continuous (FreeGroup.lift : (ι → G) → (FreeGroup ι →* G)) := by
  apply continuous_induced_rng.mpr
  exact continuous_pi continuous_lift_evaluation

theorem continuous_generator_evaluation :
    Continuous (fun ρ : FreeGroup ι →* G => fun i => ρ (FreeGroup.of i)) := by
  apply continuous_pi
  intro i
  exact (continuous_apply (FreeGroup.of i)).comp continuous_induced_dom

/-- A tuple of group elements and its free-group representation carry exactly
the same pointwise topology. -/
def freeGroupRepresentationHomeomorph : (ι → G) ≃ₜ (FreeGroup ι →* G) where
  toEquiv := FreeGroup.lift
  continuous_toFun := continuous_lift
  continuous_invFun := continuous_generator_evaluation

end Topological

end OperatorCoding

#print axioms OperatorCoding.lift_conjugate_iff
#print axioms OperatorCoding.freeGroupRepresentationHomeomorph
