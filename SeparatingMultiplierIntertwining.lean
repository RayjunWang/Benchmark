import RestrictedSpectralClass
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.InnerProductSpace.Adjoint

open MeasureTheory Set Filter

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

theorem starAlgHom_eq_of_separating_family
    {K B ι : Type*} [TopologicalSpace K] [CompactSpace K]
    [Semiring B] [StarRing B] [Algebra ℂ B]
    [TopologicalSpace B] [T2Space B]
    (φ ψ : C(K, ℂ) →⋆ₐ[ℂ] B) (hφ : Continuous φ) (hψ : Continuous ψ)
    (c : ι → C(K, ℂ))
    (hsep : ∀ x y : K, x ≠ y → ∃ i, c i x ≠ c i y)
    (heq : ∀ i, φ (c i) = ψ (c i)) : φ = ψ := by
  let A := StarAlgHom.equalizer φ ψ
  have hclosed : IsClosed (A : Set C(K, ℂ)) := isClosed_eq hφ hψ
  have hAsep : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ := hsep x y hxy
    exact ⟨c i, ⟨c i, heq i, rfl⟩, hi⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hAsep
  apply DFunLike.ext
  intro f
  have hf : f ∈ closure (A : Set C(K, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe, htop]
    trivial
  exact hclosed.closure_subset hf

def characterContinuousMap (i : CharacterIndex) : C(MeasureEquivalenceSolenoid.CompactSequences, ℂ) :=
  ⟨character i, character_continuous i⟩

theorem characterContinuousMap_separates (x y : MeasureEquivalenceSolenoid.CompactSequences)
    (hxy : x ≠ y) : ∃ i, characterContinuousMap i x ≠ characterContinuousMap i y := by
  by_contra h
  apply hxy
  apply characterFamily_injective
  funext i
  exact not_ne_iff.mp (not_exists.mp h i)

theorem starAlgHom_eq_of_characters
    {B : Type*} [Semiring B] [StarRing B] [Algebra ℂ B]
    [TopologicalSpace B] [T2Space B]
    (φ ψ : C(MeasureEquivalenceSolenoid.CompactSequences, ℂ) →⋆ₐ[ℂ] B)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (heq : ∀ i, φ (characterContinuousMap i) = ψ (characterContinuousMap i)) : φ = ψ :=
  starAlgHom_eq_of_separating_family φ ψ hφ hψ characterContinuousMap
    characterContinuousMap_separates heq

end MeasureEquivalenceRestrictedPhase

#print axioms MeasureEquivalenceRestrictedPhase.starAlgHom_eq_of_characters
