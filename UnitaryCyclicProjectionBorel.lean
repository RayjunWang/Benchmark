import UnitaryCyclicSubspace
import CountableSpanProjectionBorel

/-! Borel orthogonal projections onto the actual cyclic subspaces of
unitaries, with both the generator vector and test vector varying. -/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

set_option maxHeartbeats 1000000

namespace OperatorCoding

open MeasureUnitary

noncomputable section

def integerEnumeration : ℕ → ℤ := Classical.choose (exists_surjective_nat ℤ)

theorem integerEnumeration_surjective : Function.Surjective integerEnumeration :=
  Classical.choose_spec (exists_surjective_nat ℤ)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance cyclicSpan_complete (U : StrongUnitary H) (v : H) : CompleteSpace (cyclicSpan U v) :=
  (cyclicSpan_isClosed U v).isComplete.completeSpace_coe

def enumeratedCyclicOrbit (U : StrongUnitary H) (v : H) (n : ℕ) : H :=
  (U ^ integerEnumeration n) v

theorem closedFamilySpan_enumeratedCyclicOrbit (U : StrongUnitary H) (v : H) :
    closedFamilySpan (enumeratedCyclicOrbit U v) = cyclicSpan U v := by
  have hrange : Set.range (enumeratedCyclicOrbit U v) = Set.range (fun n : ℤ => (U ^ n) v) := by
    ext x
    constructor
    · rintro ⟨n,rfl⟩
      exact ⟨integerEnumeration n,rfl⟩
    · rintro ⟨n,rfl⟩
      obtain ⟨m,hm⟩ := integerEnumeration_surjective n
      exact ⟨m,by simp only [enumeratedCyclicOrbit,hm]⟩
  unfold closedFamilySpan cyclicSpan
  rw [hrange]

variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

local instance : MeasurableSpace (StrongUnitary H) := borel _
local instance : BorelSpace (StrongUnitary H) := ⟨rfl⟩

theorem cyclicSpan_projection_measurable :
    Measurable (fun p : StrongUnitary H × H × H =>
      (cyclicSpan p.1 p.2.1).starProjection p.2.2) := by
  have hf (n : ℕ) : Measurable (fun p : StrongUnitary H × H × H =>
      enumeratedCyclicOrbit p.1 p.2.1 n) :=
    (strongUnitary_continuous_action (continuous_fst.zpow (integerEnumeration n))
      continuous_snd.fst).measurable
  have hp := closedFamilySpan_projection_measurable
    (fun p : StrongUnitary H × H × H => enumeratedCyclicOrbit p.1 p.2.1)
    hf (fun p => p.2.2) measurable_snd.snd
  have heq : (fun p : StrongUnitary H × H × H =>
      (closedFamilySpan (enumeratedCyclicOrbit p.1 p.2.1)).starProjection p.2.2) =
      (fun p : StrongUnitary H × H × H => (cyclicSpan p.1 p.2.1).starProjection p.2.2) := by
    funext p
    exact congrArg (fun T : H →L[ℂ] H => T p.2.2)
      (starProjection_eq_of_submodule_eq _ _ (closedFamilySpan_enumeratedCyclicOrbit p.1 p.2.1))
  exact heq ▸ hp

end
end OperatorCoding

#print axioms OperatorCoding.cyclicSpan_projection_measurable
