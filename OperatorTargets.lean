import OperatorNormalization
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
Exact target propositions for Theorems 1.3 and 1.4 of MeasureEquivalence.tex.
These are definitions of the outstanding goals, not proofs of those goals.
The operator topology is strong convergence on vectors. Representations are
all group homomorphisms to the genuine strong unitary group.
-/

open MeasureTheory

namespace OperatorCoding

noncomputable section

abbrev CanonicalHilbert := lp (fun _ : ℕ => ℂ) 2
abbrev Cantor := ℕ → Bool
abbrev CanonicalOperator := CanonicalHilbert →L[ℂ] CanonicalHilbert
abbrev UnitaryRepresentation (Γ : Type*) [Group Γ] := Γ →* StrongUnitary CanonicalHilbert

/-- The SOT on all bounded operators, specified without changing the norm
topology that Mathlib also uses on continuous linear maps. -/
abbrev operatorStrongTopology : TopologicalSpace CanonicalOperator :=
  TopologicalSpace.induced
    (fun T : CanonicalOperator => fun x : CanonicalHilbert => T x) inferInstance

abbrev operatorBorel : MeasurableSpace CanonicalOperator :=
  @borel CanonicalOperator operatorStrongTopology

abbrev unitaryRepresentationTopology (Γ : Type*) [Group Γ] :
    TopologicalSpace (UnitaryRepresentation Γ) :=
  TopologicalSpace.induced
    (fun ρ : UnitaryRepresentation Γ => fun g : Γ => ρ g) inferInstance

abbrev unitaryRepresentationBorel (Γ : Type*) [Group Γ] :
    MeasurableSpace (UnitaryRepresentation Γ) :=
  @borel (UnitaryRepresentation Γ) (unitaryRepresentationTopology Γ)

def MeasureEquivalent (μ ν : ProbabilityMeasure Cantor) : Prop :=
  (μ : Measure Cantor) ≪ (ν : Measure Cantor) ∧ (ν : Measure Cantor) ≪ (μ : Measure Cantor)

def UnitaryRepresentationEquivalent {Γ : Type*} [Group Γ]
    (ρ σ : UnitaryRepresentation Γ) : Prop :=
  ∃ u : StrongUnitary CanonicalHilbert, ∀ g, u * ρ g * u⁻¹ = σ g

/-- Borel reducibility with the two measurable structures explicit. This
prevents accidental use of the operator-norm Borel structure. -/
def BorelReducesWith {X Y : Type*} (mX : MeasurableSpace X) (mY : MeasurableSpace Y)
    (E : X → X → Prop) (F : Y → Y → Prop) : Prop :=
  ∃ f : X → Y, @Measurable X Y mX mY f ∧ ∀ x y, E x y ↔ F (f x) (f y)

def BorelBireducibleWith {X Y : Type*} (mX : MeasurableSpace X) (mY : MeasurableSpace Y)
    (E : X → X → Prop) (F : Y → Y → Prop) : Prop :=
  BorelReducesWith mX mY E F ∧ BorelReducesWith mY mX F E

def BorelStrictlyReducesWith {X Y : Type*} (mX : MeasurableSpace X) (mY : MeasurableSpace Y)
    (E : X → X → Prop) (F : Y → Y → Prop) : Prop :=
  BorelReducesWith mX mY E F ∧ ¬ BorelReducesWith mY mX F E

theorem borelReducesWith_trans {X Y Z : Type*}
    {mX : MeasurableSpace X} {mY : MeasurableSpace Y} {mZ : MeasurableSpace Z}
    {E : X → X → Prop} {F : Y → Y → Prop} {G : Z → Z → Prop}
    (hEF : BorelReducesWith mX mY E F) (hFG : BorelReducesWith mY mZ F G) :
    BorelReducesWith mX mZ E G := by
  obtain ⟨f, hf, hE⟩ := hEF
  obtain ⟨g, hg, hF⟩ := hFG
  exact ⟨g ∘ f, @Measurable.comp X Y Z mX mY mZ g f hg hf,
    fun x y => (hE x y).trans (hF (f x) (f y))⟩

/-- Exact Theorem 1.3 on the canonical separable infinite-dimensional Hilbert
space. This proposition is deliberately not asserted as a theorem. -/
def Theorem13 : Prop :=
  BorelStrictlyReducesWith inferInstance operatorBorel
    MeasureEquivalent OperatorUnitaryEquivalent

/-- Exact chain of comparisons in Theorem 1.4. This proposition is deliberately
not asserted as a theorem. `Multiplicative ℤ` is the group written additively
as ℤ in the manuscript. -/
def Theorem14 : Prop :=
  BorelBireducibleWith (unitaryRepresentationBorel (Multiplicative ℤ)) inferInstance
    UnitaryRepresentationEquivalent MeasureEquivalent ∧
  BorelStrictlyReducesWith inferInstance (unitaryRepresentationBorel (FreeGroup ℕ))
    MeasureEquivalent UnitaryRepresentationEquivalent ∧
  BorelBireducibleWith (unitaryRepresentationBorel (FreeGroup ℕ)) operatorBorel
    UnitaryRepresentationEquivalent OperatorUnitaryEquivalent

end
end OperatorCoding

#print axioms OperatorCoding.Theorem13
#print axioms OperatorCoding.Theorem14
