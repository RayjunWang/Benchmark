import UnitaryCyclicProjectionBorel

/-! The actual Borel greedy cyclic generators obtained from a fixed
dense sequence by projecting away all earlier Laurent orbits. -/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped InnerProductSpace

set_option maxHeartbeats 1500000

namespace OperatorCoding

open MeasureUnitary

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [SecondCountableTopology H]

def greedyCyclicGenerator (U : StrongUnitary H) (n : ℕ) : H :=
  denseSeq H n - (closedFamilySpan (fun p : ℕ =>
    if hi : (Nat.unpair p).1 < n then
      (U ^ integerEnumeration (Nat.unpair p).2) (greedyCyclicGenerator U (Nat.unpair p).1)
    else 0)).starProjection (denseSeq H n)
termination_by n
decreasing_by exact hi

def greedyPreviousFamily (U : StrongUnitary H) (n : ℕ) (p : ℕ) : H :=
  if (Nat.unpair p).1 < n then
    (U ^ integerEnumeration (Nat.unpair p).2) (greedyCyclicGenerator U (Nat.unpair p).1)
  else 0

theorem greedyCyclicGenerator_formula (U : StrongUnitary H) (n : ℕ) :
    greedyCyclicGenerator U n = denseSeq H n -
      (closedFamilySpan (greedyPreviousFamily U n)).starProjection (denseSeq H n) := by
  conv_lhs => rw [greedyCyclicGenerator]
  rfl

theorem greedyCyclicGenerator_orthogonal_previous (U : StrongUnitary H) (n : ℕ) :
    greedyCyclicGenerator U n ∈ (closedFamilySpan (greedyPreviousFamily U n))ᗮ := by
  rw [greedyCyclicGenerator_formula]
  exact Submodule.sub_starProjection_mem_orthogonal _

theorem greedy_orbit_mem_previous (U : StrongUnitary H) (i n : ℕ) (hi : i < n) (m : ℤ) :
    (U ^ m) (greedyCyclicGenerator U i) ∈ closedFamilySpan (greedyPreviousFamily U n) := by
  obtain ⟨j,hj⟩ := integerEnumeration_surjective m
  apply Submodule.le_topologicalClosure _
  apply Submodule.subset_span
  refine ⟨Nat.pair i j, ?_⟩
  simp only [greedyPreviousFamily, Nat.unpair_pair, hi, if_pos, hj]

theorem greedy_cyclicSpan_le_previous (U : StrongUnitary H) (i n : ℕ) (hi : i < n) :
    cyclicSpan U (greedyCyclicGenerator U i) ≤ closedFamilySpan (greedyPreviousFamily U n) :=
  cyclicSpan_minimal U _ _ (Submodule.isClosed_topologicalClosure _)
    (fun m => greedy_orbit_mem_previous U i n hi m)

variable [MeasurableSpace H] [BorelSpace H]

local instance : MeasurableSpace (StrongUnitary H) := borel _
local instance : BorelSpace (StrongUnitary H) := ⟨rfl⟩

theorem greedyCyclicGenerator_measurable (n : ℕ) :
    Measurable (fun U : StrongUnitary H => greedyCyclicGenerator U n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hf (p : ℕ) : Measurable (fun U : StrongUnitary H => greedyPreviousFamily U n p) := by
      unfold greedyPreviousFamily
      split_ifs with hi
      · have heval : Continuous (fun q : StrongUnitary H × H => q.1 q.2) :=
          strongUnitary_continuous_action continuous_fst continuous_snd
        exact heval.measurable.comp
          ((continuous_id.zpow (integerEnumeration (Nat.unpair p).2)).measurable.prodMk
            (ih (Nat.unpair p).1 hi))
      · exact measurable_const
    have hp := closedFamilySpan_projection_measurable
      (fun U : StrongUnitary H => greedyPreviousFamily U n) hf
        (fun _ => denseSeq H n) measurable_const
    have heq : (fun U : StrongUnitary H => greedyCyclicGenerator U n) =
        (fun U : StrongUnitary H => denseSeq H n -
          (closedFamilySpan (greedyPreviousFamily U n)).starProjection (denseSeq H n)) :=
      funext (fun U => greedyCyclicGenerator_formula U n)
    rw [heq]
    exact measurable_const.sub hp

end
end OperatorCoding

#print axioms OperatorCoding.greedyCyclicGenerator_measurable
