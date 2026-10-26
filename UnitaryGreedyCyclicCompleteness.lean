import UnitaryGreedyCyclicDecomposition

/-! The Borel greedy cyclic subspaces are pairwise orthogonal and span
the entire Hilbert space. Zero generators cause no exceptional case. -/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped InnerProductSpace

set_option maxHeartbeats 1500000

namespace OperatorCoding

open MeasureUnitary

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [SecondCountableTopology H]

def greedyCyclicAllSpan (U : StrongUnitary H) : Submodule ℂ H :=
  (⨆ n : ℕ, cyclicSpan U (greedyCyclicGenerator U n)).topologicalClosure

theorem greedy_previous_le_all (U : StrongUnitary H) (n : ℕ) :
    closedFamilySpan (greedyPreviousFamily U n) ≤ greedyCyclicAllSpan U := by
  apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_topologicalClosure _)
  apply Submodule.span_le.mpr
  rintro _ ⟨p,rfl⟩
  unfold greedyPreviousFamily
  split_ifs with hi
  · apply Submodule.le_topologicalClosure _
    apply le_iSup (fun i => cyclicSpan U (greedyCyclicGenerator U i)) (Nat.unpair p).1
    exact cyclicSpan_contains_orbit U (greedyCyclicGenerator U (Nat.unpair p).1)
      (integerEnumeration (Nat.unpair p).2)
  · exact Submodule.zero_mem _

theorem greedy_denseSeq_mem_all (U : StrongUnitary H) (n : ℕ) :
    denseSeq H n ∈ greedyCyclicAllSpan U := by
  have hg : greedyCyclicGenerator U n ∈ greedyCyclicAllSpan U :=
    Submodule.le_topologicalClosure _
      (le_iSup (fun i => cyclicSpan U (greedyCyclicGenerator U i)) n
        (cyclicSpan_contains_generator U (greedyCyclicGenerator U n)))
  have hp : (closedFamilySpan (greedyPreviousFamily U n)).starProjection (denseSeq H n) ∈
      greedyCyclicAllSpan U :=
    greedy_previous_le_all U n (Submodule.coe_mem
      ((closedFamilySpan (greedyPreviousFamily U n)).orthogonalProjection (denseSeq H n)))
  rw [greedyCyclicGenerator_formula] at hg
  simpa only [sub_add_cancel] using (greedyCyclicAllSpan U).add_mem hg hp

theorem greedyCyclicAllSpan_eq_top (U : StrongUnitary H) : greedyCyclicAllSpan U = ⊤ := by
  apply top_unique
  intro x hx
  have hrange : Set.range (denseSeq H) ⊆ (greedyCyclicAllSpan U : Set H) := by
    rintro _ ⟨n,rfl⟩
    exact greedy_denseSeq_mem_all U n
  have hclosed : IsClosed (greedyCyclicAllSpan U : Set H) := Submodule.isClosed_topologicalClosure _
  exact (closure_minimal hrange hclosed) (denseRange_denseSeq H x)

theorem greedy_cyclicSpans_isOrtho_of_lt (U : StrongUnitary H) (i j : ℕ) (hij : i < j) :
    (cyclicSpan U (greedyCyclicGenerator U i)).IsOrtho
      (cyclicSpan U (greedyCyclicGenerator U j)) := by
  have hj : greedyCyclicGenerator U j ∈ (cyclicSpan U (greedyCyclicGenerator U i))ᗮ :=
    Submodule.orthogonal_le (greedy_cyclicSpan_le_previous U i j hij)
      (greedyCyclicGenerator_orthogonal_previous U j)
  have hle : cyclicSpan U (greedyCyclicGenerator U j) ≤
      (cyclicSpan U (greedyCyclicGenerator U i))ᗮ :=
    cyclicSpan_minimal U _ _ (Submodule.isClosed_orthogonal _)
      (fun m => cyclicSpan_orthogonal_zpow_invariant U (greedyCyclicGenerator U i) m
        (greedyCyclicGenerator U j) hj)
  exact (Submodule.isOrtho_iff_le.mpr hle).symm

theorem greedy_cyclicSpans_pairwise_isOrtho (U : StrongUnitary H) :
    Pairwise (fun i j => (cyclicSpan U (greedyCyclicGenerator U i)).IsOrtho
      (cyclicSpan U (greedyCyclicGenerator U j))) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact greedy_cyclicSpans_isOrtho_of_lt U i j hlt
  · exact (greedy_cyclicSpans_isOrtho_of_lt U j i hgt).symm

end
end OperatorCoding

#print axioms OperatorCoding.greedyCyclicAllSpan_eq_top
#print axioms OperatorCoding.greedy_cyclicSpans_pairwise_isOrtho
