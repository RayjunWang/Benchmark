import L2CoordinateProjection
import FreeGroupCones
import ProjectionMassGap

/-! An actual uniform ℓ² spectral gap for arbitrary sums of the free
regular representation of F₂, obtained from its four first-letter cones. -/

open Set
open scoped ENNReal

noncomputable section

namespace BenchmarkRegularGap

open BenchmarkShift BenchmarkCoordinateProjection

variable {Q : Type*}

def coneSet (a : Letter) : Set (Q × Group) := {p | p.2 ∈ cone a}

def leftPermutation (a : Letter) : (Q × Group) ≃ (Q × Group) :=
  Equiv.prodCongr (Equiv.refl Q) (Equiv.mulLeft (letterGroup a))

lemma coneSet_preimage (a : Letter) :
    (leftPermutation (Q := Q) a) ⁻¹' coneSet a = (coneSet (reverseLetter a))ᶜ := by
  ext p
  exact cone_letter_mul_iff a p.2

lemma coneSet_disjoint {a b : Letter} (hab : a ≠ b) :
    Disjoint (coneSet (Q := Q) a) (coneSet b) := by
  rw [Set.disjoint_left]
  intro p ha hb
  exact Set.disjoint_left.mp (cone_disjoint hab) ha hb

theorem regular_free_group_gap (v : Space (Q × Group)) :
    ‖v‖ ^ 2 ≤ 8 *
      (‖permute (leftPermutation (0, true)) v - v‖ ^ 2 +
        ‖permute (leftPermutation (1, true)) v - v‖ ^ 2) := by
  let ap := coneSet (Q := Q) (0, true)
  let am := coneSet (Q := Q) (0, false)
  let bp := coneSet (Q := Q) (1, true)
  let bm := coneSet (Q := Q) (1, false)
  let eA := leftPermutation (Q := Q) (0, true)
  let eB := leftPermutation (Q := Q) (1, true)
  apply BenchmarkProjectionGap.two_partition_gap
    (projection ap) (projection am) (projection bp) (projection bm)
    (fun w => norm_project_le ap w) (fun w => norm_project_le bp w)
    v (permute eA v) (permute eB v) (norm_permute eA v) (norm_permute eB v)
  · exact norm_project_permute_pair ap am eA (coneSet_preimage (0, true)) v
  · exact norm_project_permute_pair bp bm eB (coneSet_preimage (1, true)) v
  · exact four_projection_mass_le ap am bp bm
      (coneSet_disjoint (by decide : ((0, true) : Letter) ≠ (0, false)))
      (coneSet_disjoint (by decide : ((0, true) : Letter) ≠ (1, true)))
      (coneSet_disjoint (by decide : ((0, true) : Letter) ≠ (1, false)))
      (coneSet_disjoint (by decide : ((0, false) : Letter) ≠ (1, true)))
      (coneSet_disjoint (by decide : ((0, false) : Letter) ≠ (1, false)))
      (coneSet_disjoint (by decide : ((1, true) : Letter) ≠ (1, false))) v

end BenchmarkRegularGap

#print axioms BenchmarkRegularGap.regular_free_group_gap
