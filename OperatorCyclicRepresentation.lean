import OperatorTargets
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Algebra.Group.Conj

/-! Representations of the infinite cyclic group are exactly one unitary,
with the pointwise strong topology and exact conjugacy preserved. -/

namespace OperatorCoding

section General

variable {G : Type*} [Group G]

def ElementConjugate (u v : G) : Prop := ∃ w : G, w*u*w⁻¹ = v

theorem cyclic_conjugate_iff (u v : G) :
    (∃ w : G, ∀ n : Multiplicative ℤ,
      w * zpowersHom G u n * w⁻¹ = zpowersHom G v n) ↔ ElementConjugate u v := by
  constructor
  · rintro ⟨w,hw⟩
    exact ⟨w,by simpa using hw (Multiplicative.ofAdd 1)⟩
  · rintro ⟨w,hw⟩
    refine ⟨w,fun n => ?_⟩
    simp only [zpowersHom_apply]
    rw [← conj_zpow, hw]

variable [TopologicalSpace G] [IsTopologicalGroup G]

instance cyclicRepresentationTopology : TopologicalSpace (Multiplicative ℤ →* G) :=
  TopologicalSpace.induced
    (fun ρ : Multiplicative ℤ →* G => (ρ : Multiplicative ℤ → G)) inferInstance

theorem continuous_zpowersHom : Continuous (zpowersHom G) := by
  apply continuous_induced_rng.mpr
  exact continuous_pi (fun n => continuous_id.zpow n.toAdd)

theorem continuous_cyclic_generator :
    Continuous (fun ρ : Multiplicative ℤ →* G => ρ (Multiplicative.ofAdd 1)) :=
  (continuous_apply (Multiplicative.ofAdd 1)).comp continuous_induced_dom

def cyclicRepresentationHomeomorph : G ≃ₜ (Multiplicative ℤ →* G) where
  toEquiv := zpowersHom G
  continuous_toFun := continuous_zpowersHom
  continuous_invFun := continuous_cyclic_generator

end General

theorem cyclicRepresentations_borelBireducible_unitaries :
    BorelBireducibleWith (unitaryRepresentationBorel (Multiplicative ℤ))
      (borel (StrongUnitary CanonicalHilbert))
      UnitaryRepresentationEquivalent ElementConjugate := by
  constructor
  · refine ⟨(zpowersHom (StrongUnitary CanonicalHilbert)).symm,
      continuous_cyclic_generator.borel_measurable,fun ρ σ => ?_⟩
    simpa only [Equiv.apply_symm_apply] using
      cyclic_conjugate_iff ((zpowersHom _).symm ρ) ((zpowersHom _).symm σ)
  · exact ⟨zpowersHom _, continuous_zpowersHom.borel_measurable,
      fun u v => (cyclic_conjugate_iff u v).symm⟩

end OperatorCoding

#print axioms OperatorCoding.cyclicRepresentationHomeomorph
#print axioms OperatorCoding.cyclicRepresentations_borelBireducible_unitaries
