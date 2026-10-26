import UnitaryCyclicRiesz

open MeasureTheory Filter Set
open scoped ENNReal NNReal InnerProductSpace

set_option maxHeartbeats 1000000

noncomputable section

namespace MeasureUnitary

variable {K H : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def representationCyclicSubspace
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) : Submodule ℂ H :=
  (representationVectorLinearMap π v).range.topologicalClosure

theorem representationVectorLpIsometry_toLp
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) (f : C(K, ℂ)) :
    representationVectorLpIsometry π v
      (ContinuousMap.toLp 2 (representationVectorMeasure π v) ℂ f) = π f v :=
  representationVectorLpOperator_toLp π v f

theorem representationVectorLpIsometry_mem
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
    (f : Lp ℂ 2 (representationVectorMeasure π v)) :
    representationVectorLpIsometry π v f ∈ representationCyclicSubspace π v := by
  have hd := ContinuousMap.toLp_denseRange (p := 2) ℂ (representationVectorMeasure π v) ℂ (by norm_num)
  refine hd.induction ?_ ?_ f
  · rintro z ⟨g,rfl⟩
    rw [representationVectorLpIsometry_toLp]
    exact (representationVectorLinearMap π v).range.le_topologicalClosure ⟨g,rfl⟩
  · exact (representationVectorLinearMap π v).range.isClosed_topologicalClosure.preimage
      (representationVectorLpIsometry π v).continuous

theorem representationCyclicSubspace_le_range
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    representationCyclicSubspace π v ≤ (representationVectorLpIsometry π v).toLinearMap.range := by
  apply Submodule.topologicalClosure_minimal
  · rintro z ⟨g,rfl⟩
    refine ⟨ContinuousMap.toLp 2 (representationVectorMeasure π v) ℂ g, ?_⟩
    exact representationVectorLpIsometry_toLp π v g
  · exact (representationVectorLpIsometry π v).isometry.isClosedEmbedding.isClosed_range

def representationCyclicLpIsometry
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    Lp ℂ 2 (representationVectorMeasure π v) →ₗᵢ[ℂ] representationCyclicSubspace π v where
  toLinearMap := (representationVectorLpIsometry π v).toLinearMap.codRestrict
    (representationCyclicSubspace π v) (representationVectorLpIsometry_mem π v)
  norm_map' := (representationVectorLpIsometry π v).norm_map

def representationCyclicLpEquiv
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    Lp ℂ 2 (representationVectorMeasure π v) ≃ₗᵢ[ℂ] representationCyclicSubspace π v :=
  LinearIsometryEquiv.ofSurjective (representationCyclicLpIsometry π v) (by
    intro z
    obtain ⟨f,hf⟩ := representationCyclicSubspace_le_range π v z.property
    refine ⟨f,Subtype.ext hf⟩)

end MeasureUnitary

#print axioms MeasureUnitary.representationCyclicLpEquiv
