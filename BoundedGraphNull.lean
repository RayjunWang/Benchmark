import CountableBorelColoring
import FiniteBorelColoring
import RefiningFinitePartitions

/-! The complete graph-distance construction for graphs whose bounded balls
are explicitly enumerated by finitely many measurable maps. No finite Borel
coloring theorem is assumed: the prefix and greedy constructions supply it.
-/

open Filter Set
open scoped Topology

noncomputable section

namespace BenchmarkBoundedGraphNull

variable {X : Type*} (G : SimpleGraph X)

def distancePower (r : ℕ) : SimpleGraph X where
  Adj x y := x ≠ y ∧ G.Reachable x y ∧ G.dist x y ≤ r
  symm := by
    intro x y h
    refine ⟨h.1.symm, h.2.1.symm, ?_⟩
    simpa only [SimpleGraph.dist_comm] using h.2.2
  loopless := ⟨by intro x h; exact h.1 rfl⟩

variable [MeasurableSpace X]

theorem exists_borel_reduction
    (m : ℕ → ℕ) (ball : ∀ r, Fin (m r) → X → X)
    (hball_meas : ∀ r i, Measurable (ball r i))
    (hball : ∀ r x z, (G.Reachable x z ∧ G.dist x z ≤ r) ↔ ∃ i, ball r i x = z)
    (embedding : X → ℕ → Bool) (he : Measurable embedding)
    (hinj : Function.Injective embedding) :
    ∃ F : X → (ℕ → ℝ), Measurable F ∧ (∀ x j, 0 ≤ F x j ∧ F x j ≤ 1) ∧
      ∀ x y, G.Reachable x y ↔ Tendsto (fun j => F x j - F y j) atTop (𝓝 0) := by
  classical
  have hex : ∀ n : ℕ, ∃ q : X → Fin (m (4 * (n + 1)) + 1),
      Measurable q ∧ ∀ x y, (distancePower G (4 * (n + 1))).Adj x y → q x ≠ q y := by
    intro n
    let r := 4 * (n + 1)
    let H := distancePower G r
    have henum : ∀ x y, H.Adj x y → ∃ i, ball r i x = y := by
      intro x y hxy
      exact (hball r x y).mp hxy.2
    obtain ⟨rank, hrank, hproper⟩ :=
      BenchmarkCountableColoring.exists_measurable_countable_proper_coloring
        (m r) (ball r) embedding hinj H henum (hball_meas r) he
    exact BenchmarkFiniteColoring.exists_measurable_finite_proper_coloring
      (m r) (ball r) rank H henum (hball_meas r) hrank hproper
  choose q hq hproper using hex
  apply BenchmarkRefiningPartitions.exists_borel_reduction
    (fun n => m (4 * (n + 1)) + 1) q embedding G m ball hball_meas hball hq he hinj
  intro n x y hc hr hd
  by_contra hne
  exact hproper n x y ⟨hne, hr, hd⟩ hc

end BenchmarkBoundedGraphNull

#print axioms BenchmarkBoundedGraphNull.exists_borel_reduction
