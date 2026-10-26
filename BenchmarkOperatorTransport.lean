import Definitions.Def_BenchmarkRelations
import OperatorBireduction
import MeasureCyclicReduction
import OperatorStrictSeparation
import UnitarySpectralReduction

open MeasureTheory

noncomputable section

namespace BenchmarkComparisons

def representationToHom {Γ : Type*} [Group Γ] (ρ : Representation Γ) :
    OperatorCoding.UnitaryRepresentation Γ where
  toFun := ρ.operator
  map_one' := by apply LinearIsometryEquiv.ext; intro v; exact ρ.map_one v
  map_mul' := by intro g h; apply LinearIsometryEquiv.ext; intro v; exact ρ.map_mul g h v

def representationFromHom {Γ : Type*} [Group Γ] (ρ : OperatorCoding.UnitaryRepresentation Γ) :
    Representation Γ where
  operator := ρ
  map_one := by intro v; simp
  map_mul := by intro g h v; simp

def representationEquiv (Γ : Type*) [Group Γ] :
    Representation Γ ≃ OperatorCoding.UnitaryRepresentation Γ where
  toFun := representationToHom
  invFun := representationFromHom
  left_inv := by intro ρ; cases ρ; rfl
  right_inv := by intro ρ; ext g v; rfl

theorem continuous_representationToHom (Γ : Type*) [Group Γ] :
    @Continuous (Representation Γ) (OperatorCoding.UnitaryRepresentation Γ)
      (representationStrongTopology Γ) (OperatorCoding.unitaryRepresentationTopology Γ)
      representationToHom := by
  letI : TopologicalSpace (Representation Γ) := representationStrongTopology Γ
  letI : TopologicalSpace (OperatorCoding.UnitaryRepresentation Γ) :=
    OperatorCoding.unitaryRepresentationTopology Γ
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro g
  apply (OperatorCoding.strongUnitary_continuous_iff _).mpr
  intro v
  have hc : Continuous (fun ρ : Representation Γ => fun g : Γ => fun v : Hilbert => ρ.operator g v) :=
    continuous_induced_dom
  exact (continuous_apply v).comp ((continuous_apply g).comp hc)

theorem continuous_representationFromHom (Γ : Type*) [Group Γ] :
    @Continuous (OperatorCoding.UnitaryRepresentation Γ) (Representation Γ)
      (OperatorCoding.unitaryRepresentationTopology Γ) (representationStrongTopology Γ)
      representationFromHom := by
  letI : TopologicalSpace (Representation Γ) := representationStrongTopology Γ
  letI : TopologicalSpace (OperatorCoding.UnitaryRepresentation Γ) :=
    OperatorCoding.unitaryRepresentationTopology Γ
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro g
  apply continuous_pi
  intro v
  exact (OperatorCoding.strongUnitary_continuous_eval v).comp
    ((continuous_apply g).comp continuous_induced_dom)

theorem representationEquivalent_iff {Γ : Type*} [Group Γ] (ρ σ : Representation Γ) :
    RepresentationEquivalent ρ σ ↔
      OperatorCoding.UnitaryRepresentationEquivalent (representationToHom ρ) (representationToHom σ) := by
  constructor
  · rintro ⟨U,hU⟩
    refine ⟨U,fun g => ?_⟩
    apply LinearIsometryEquiv.ext
    intro v
    change U (ρ.operator g (U.symm v)) = σ.operator g v
    rw [hU]
    simp
  · rintro ⟨U,hU⟩
    refine ⟨U,fun g v => ?_⟩
    have h := congrArg (fun W : OperatorCoding.StrongUnitary OperatorCoding.CanonicalHilbert => W (U v)) (hU g)
    simpa using h

theorem representations_borelBireducible (Γ : Type*) [Group Γ] :
    BorelBireducibleWith (representationBorel Γ) (OperatorCoding.unitaryRepresentationBorel Γ)
      RepresentationEquivalent OperatorCoding.UnitaryRepresentationEquivalent := by
  constructor
  · refine ⟨representationToHom, ?_, representationEquivalent_iff⟩
    exact @Continuous.borel_measurable _ _ (representationStrongTopology Γ)
      (OperatorCoding.unitaryRepresentationTopology Γ) _ (continuous_representationToHom Γ)
  · refine ⟨representationFromHom, ?_, ?_⟩
    · exact @Continuous.borel_measurable _ _ (OperatorCoding.unitaryRepresentationTopology Γ)
        (representationStrongTopology Γ) _ (continuous_representationFromHom Γ)
    · intro ρ σ
      simpa only [(representationEquiv Γ).apply_symm_apply] using
        (representationEquivalent_iff (representationFromHom ρ) (representationFromHom σ)).symm

theorem measure_borelReduces_cyclic_representations :
    BorelReducesWith inferInstance (representationBorel (Multiplicative ℤ))
      MeasureEquivalent RepresentationEquivalent := by
  exact OperatorCoding.borelReducesWith_trans
    MeasureUnitary.measureEquivalence_borelReduce_cyclicRepresentations
    (representations_borelBireducible (Multiplicative ℤ)).2

theorem free_representations_borelBireducible_operators :
    BorelBireducibleWith (representationBorel (FreeGroup ℕ)) operatorBorel
      RepresentationEquivalent OperatorEquivalent := by
  constructor
  · exact OperatorCoding.borelReducesWith_trans
      (representations_borelBireducible (FreeGroup ℕ)).1
      OperatorCoding.freeRepresentations_borelReduce_boundedOperators
  · exact OperatorCoding.borelReducesWith_trans
      OperatorCoding.boundedOperators_borelReduce_freeRepresentations
      (representations_borelBireducible (FreeGroup ℕ)).2

theorem measure_borelStrictlyReduces_free_representations :
    BorelStrictlyReducesWith inferInstance (representationBorel (FreeGroup ℕ))
      MeasureEquivalent RepresentationEquivalent := by
  constructor
  · exact OperatorCoding.borelReducesWith_trans
      OperatorCoding.measureEquivalence_borelStrictlyReduce_freeRepresentations.1
      (representations_borelBireducible (FreeGroup ℕ)).2
  · intro h
    exact OperatorCoding.freeRepresentations_not_borelReduce_measureEquivalence
      (OperatorCoding.borelReducesWith_trans
        (representations_borelBireducible (FreeGroup ℕ)).2 h)

/-- All parts of Theorem 1.6 except the reverse cyclic comparison. -/
theorem representation_comparisons_except_cyclic_reverse :
    BorelReducesWith inferInstance (representationBorel (Multiplicative ℤ))
      MeasureEquivalent RepresentationEquivalent ∧
    BorelStrictlyReducesWith inferInstance (representationBorel (FreeGroup ℕ))
      MeasureEquivalent RepresentationEquivalent ∧
    BorelBireducibleWith (representationBorel (FreeGroup ℕ)) operatorBorel
      RepresentationEquivalent OperatorEquivalent :=
  ⟨measure_borelReduces_cyclic_representations,
    measure_borelStrictlyReduces_free_representations,
    free_representations_borelBireducible_operators⟩

theorem cyclic_representations_borelReduces_measure :
    BorelReducesWith (representationBorel (Multiplicative ℤ)) inferInstance
      RepresentationEquivalent MeasureEquivalent :=
  OperatorCoding.borelReducesWith_trans
    (representations_borelBireducible (Multiplicative ℤ)).1
    OperatorCoding.cyclicRepresentations_borelReduce_measureEquivalence

/-- The complete comparison chain, including arbitrary cyclic-group representations. -/
theorem representation_comparisons_proved : RepresentationComparisons :=
  ⟨⟨cyclic_representations_borelReduces_measure, measure_borelReduces_cyclic_representations⟩,
    measure_borelStrictlyReduces_free_representations,
    free_representations_borelBireducible_operators⟩

end BenchmarkComparisons

#print axioms BenchmarkComparisons.representations_borelBireducible
#print axioms BenchmarkComparisons.representation_comparisons_except_cyclic_reverse
#print axioms BenchmarkComparisons.representation_comparisons_proved
