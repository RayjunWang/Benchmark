import ShiftFiniteBalls
import BoundedNullProduct

/-! Actual positive benchmark comparisons: the full F₂ shift orbit
relation, and its countable product, Borel reduce to c₀. -/

open Filter Set
open scoped Topology

noncomputable section

namespace BenchmarkShift

def Orbit (x y : Point) : Prop := ∃ g : Group, ∀ h : Group, y h = x (g⁻¹ * h)

lemma orbit_iff_reachable (x y : Point) : Orbit x y ↔ graph.Reachable x y := by
  rw [reachable_iff_shift]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, funext hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, congrFun hg⟩

theorem exists_borel_shift_null_reduction :
    ∃ F : Point → (ℕ → ℝ), Measurable F ∧ (∀ x j, 0 ≤ F x j ∧ F x j ≤ 1) ∧
      ∀ x y, Orbit x y ↔ Tendsto (fun j => F x j - F y j) atTop (𝓝 0) := by
  obtain ⟨F, hF, hb, hr⟩ := BenchmarkBoundedGraphNull.exists_borel_reduction
    graph ballSize ball measurable_ball ball_complete cantorCode measurable_cantorCode cantorCode_injective
  exact ⟨F, hF, hb, fun x y => (orbit_iff_reachable x y).trans (hr x y)⟩

theorem exists_borel_product_shift_null_reduction :
    ∃ F : (ℕ → Point) → (ℕ → ℝ), Measurable F ∧ (∀ x j, 0 ≤ F x j ∧ F x j ≤ 1) ∧
      ∀ x y, (∀ i, Orbit (x i) (y i)) ↔ Tendsto (fun j => F x j - F y j) atTop (𝓝 0) := by
  obtain ⟨F, hF, hb, hr⟩ := exists_borel_shift_null_reduction
  exact BenchmarkBoundedNullProduct.exists_product_reduction Orbit F hF hb hr

end BenchmarkShift

#print axioms BenchmarkShift.exists_borel_shift_null_reduction
#print axioms BenchmarkShift.exists_borel_product_shift_null_reduction
