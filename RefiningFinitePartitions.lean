import GraphDistanceBlocks

/-! Finite proper colorings of graph powers are refined into nested finite
partitions that also separate all points. Bounded-ball enumerators supply
the measurable bounded-neighborhood hypothesis in the block construction. -/

open Filter Set
open scoped Topology

noncomputable section

namespace BenchmarkRefiningPartitions

variable {X : Type*} (qk : ℕ → ℕ) (q : ∀ n, X → Fin (qk n))
  (embedding : X → ℕ → Bool)

abbrev RawColor (n : ℕ) :=
  (Fin (n + 1) → Bool) × (∀ i : Fin (n + 1), Fin (qk i))

def colorSize (n : ℕ) : ℕ := Fintype.card (RawColor qk n)

def rawColor (n : ℕ) (x : X) : RawColor qk n :=
  (fun i => embedding x i, fun i => q i x)

def color (n : ℕ) (x : X) : Fin (colorSize qk n) :=
  Fintype.equivFin (RawColor qk n) (rawColor qk q embedding n x)

lemma rawColor_eq_of_color_eq {n : ℕ} {x y : X}
    (h : color qk q embedding n x = color qk q embedding n y) :
    rawColor qk q embedding n x = rawColor qk q embedding n y :=
  (Fintype.equivFin (RawColor qk n)).injective h

theorem color_refines (n : ℕ) (x y : X)
    (h : color qk q embedding (n + 1) x = color qk q embedding (n + 1) y) :
    color qk q embedding n x = color qk q embedding n y := by
  apply congrArg (Fintype.equivFin (RawColor qk n))
  have hr := rawColor_eq_of_color_eq qk q embedding h
  apply Prod.ext
  · funext i
    exact congrArg (fun c : RawColor qk (n + 1) => c.1 ⟨i, by omega⟩) hr
  · funext i
    exact congrArg (fun c : RawColor qk (n + 1) => c.2 ⟨i, by omega⟩) hr

theorem color_separates (hinj : Function.Injective embedding) (x y : X)
    (h : ∀ n, color qk q embedding n x = color qk q embedding n y) : x = y := by
  apply hinj
  funext n
  have hr := rawColor_eq_of_color_eq qk q embedding (h n)
  exact congrArg (fun c : RawColor qk n => c.1 ⟨n, by omega⟩) hr

theorem color_equal_implies_q_equal (n : ℕ) (x y : X)
    (h : color qk q embedding n x = color qk q embedding n y) : q n x = q n y := by
  have hr := rawColor_eq_of_color_eq qk q embedding h
  exact congrArg (fun c : RawColor qk n => c.2 ⟨n, by omega⟩) hr

variable [MeasurableSpace X]

theorem measurable_color (hq : ∀ n, Measurable (q n)) (he : Measurable embedding) (n : ℕ) :
    Measurable (color qk q embedding n) := by
  have hprefix : Measurable (fun x => fun i : Fin (n + 1) => embedding x i) :=
    measurable_pi_lambda _ (fun i => (measurable_pi_apply (i : ℕ)).comp he)
  have hcolors : Measurable (fun x => fun i : Fin (n + 1) => q i x) :=
    measurable_pi_lambda _ (fun i => hq i)
  have hraw : Measurable (rawColor qk q embedding n) := hprefix.prodMk hcolors
  exact (measurable_of_countable (Fintype.equivFin (RawColor qk n))).comp hraw

theorem measurable_nearCell (G : SimpleGraph X) (m : ℕ → ℕ)
    (ball : ∀ r, Fin (m r) → X → X)
    (hball_meas : ∀ r i, Measurable (ball r i))
    (hball : ∀ r x z, (G.Reachable x z ∧ G.dist x z ≤ r) ↔ ∃ i, ball r i x = z)
    (hq : ∀ n, Measurable (q n)) (he : Measurable embedding)
    (n : ℕ) (i : Fin (colorSize qk n)) (r : ℕ) :
    MeasurableSet {x | BenchmarkGraphBlocks.nearCell G (colorSize qk)
      (color qk q embedding) n i x r} := by
  have heq : {x | BenchmarkGraphBlocks.nearCell G (colorSize qk)
      (color qk q embedding) n i x r} =
      ⋃ j : Fin (m r), {x | color qk q embedding n (ball r j x) = i} := by
    ext x
    simp only [BenchmarkGraphBlocks.nearCell, mem_setOf_eq, mem_iUnion]
    constructor
    · rintro ⟨z, hr, hd, hc⟩
      obtain ⟨j, hj⟩ := (hball r x z).mp ⟨hr, hd⟩
      exact ⟨j, hj ▸ hc⟩
    · rintro ⟨j, hj⟩
      have hb := (hball r x (ball r j x)).mpr ⟨j, rfl⟩
      exact ⟨ball r j x, hb.1, hb.2, hj⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro j
  exact ((measurable_color qk q embedding hq he n).comp (hball_meas r j))
    (measurableSet_singleton i)

theorem exists_borel_reduction (G : SimpleGraph X) (m : ℕ → ℕ)
    (ball : ∀ r, Fin (m r) → X → X)
    (hball_meas : ∀ r i, Measurable (ball r i))
    (hball : ∀ r x z, (G.Reachable x z ∧ G.dist x z ≤ r) ↔ ∃ i, ball r i x = z)
    (hq : ∀ n, Measurable (q n)) (he : Measurable embedding)
    (hinj : Function.Injective embedding)
    (hfar : ∀ n x y, q n x = q n y → G.Reachable x y →
      G.dist x y ≤ 4 * (n + 1) → x = y) :
    ∃ F : X → (ℕ → ℝ), Measurable F ∧ (∀ x j, 0 ≤ F x j ∧ F x j ≤ 1) ∧
      ∀ x y, G.Reachable x y ↔ Tendsto (fun j => F x j - F y j) atTop (𝓝 0) := by
  apply BenchmarkGraphBlocks.exists_borel_null_reduction G (colorSize qk) (color qk q embedding)
  · exact color_refines qk q embedding
  · exact color_separates qk q embedding hinj
  · intro n x y hc hr hd
    exact hfar n x y (color_equal_implies_q_equal qk q embedding n x y hc) hr hd
  · exact measurable_nearCell qk q embedding G m ball hball_meas hball hq he

end BenchmarkRefiningPartitions

#print axioms BenchmarkRefiningPartitions.exists_borel_reduction
