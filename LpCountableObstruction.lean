import LpGenericConstancy
import LpClassMeagre

/-! Unconditional nonreducibility of every finite real-sequence Lp relation
to the actual full binary free-group orbit relation. -/

open Filter Set Topology TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace BenchmarkCountableReverse

theorem finite_ENNlp_not_reduces_eInfinity (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    ¬ BenchmarkComparisons.BorelReduces (BenchmarkComparisons.LpDifference p.toReal)
      BenchmarkComparisons.EInfinity := by
  rintro ⟨f, hf, hred⟩
  obtain ⟨g, U, W, hUo, hUn, hWo, hWn, hRes⟩ := countable_orbit_rectangle p hp f hf
    (fun x y hxy => (hred x y).mp hxy)
  obtain ⟨h₀, hh₀⟩ := hWn
  obtain ⟨ε, hε, hBall⟩ := Metric.isOpen_iff.mp hWo h₀ hh₀
  obtain ⟨D, hDG, hDd, hfD⟩ := BenchmarkJump.measurable_continuousOn_residual f hf
  have hD : D ∈ residual RealSequences := residual_of_dense_Gδ hDG hDd
  let A : Set RealSequences := (fun x => x + coordinates p h₀) '' U
  have hAo : IsOpen A := isOpenMap_add_right (coordinates p h₀) _ hUo
  have hAn : A.Nonempty := hUn.image _
  obtain ⟨C, hCo, hCn, hCA, hC⟩ := exists_open_prefixConvex_subset A hAo hAn
  have hSmall : ∀ y ∈ C, ∀ k : Translations p, ‖k‖ < ε →
      y ∈ D → y + coordinates p k ∈ D → f y = f (y + coordinates p k) := by
    intro y hyC k hk hyD hzD
    obtain ⟨x, hxU, hxy⟩ := hCA hyC
    have hbase : translationAction p (x, h₀) = y := hxy
    have hnext : translationAction p (x, h₀ + k) = y + coordinates p k := by
      change x + coordinates p (h₀ + k) = y + coordinates p k
      rw [← hxy]
      change x + (coordinates p h₀ + coordinates p k) = (x + coordinates p h₀) + coordinates p k
      abel
    have he := small_translation_exact p U W hUo hWo D hD f hfD g hRes
      h₀ hh₀ ε hBall x hxU k hk (hbase.symm ▸ hyD) (hnext.symm ▸ hzD)
    simpa only [hbase, hnext] using he
  obtain ⟨a, ha⟩ := prefix_interpolation_generic_constant p C hCo hCn hC D hD f hfD ε hε hSmall
  letI : Nonempty C := hCn.to_subtype
  letI : BaireSpace C := hCo.baireSpace
  obtain ⟨x₀, hx₀⟩ := (dense_of_mem_residual ha).nonempty
  have hnot : ∀ᶠ y : C in residual C,
      ¬ BenchmarkComparisons.LpDifference p.toReal (x₀ : RealSequences) y :=
    tendsto_residual_of_isOpenMap continuous_subtype_val hCo.isOpenMap_subtype_val
      (lp_class_meagre p hp x₀)
  have hfalse : ∀ᶠ y : C in residual C, False := by
    filter_upwards [ha, hnot] with y hy hny
    apply hny
    apply (hred x₀ y).mpr
    rw [hx₀, hy]
    exact ⟨1, by intro h; simp⟩
  obtain ⟨y, hy⟩ := (dense_of_mem_residual hfalse).nonempty
  exact hy

theorem finiteLp_not_reduces_eInfinity (p : ℝ) (hp : 1 ≤ p) :
    ¬ BenchmarkComparisons.BorelReduces (BenchmarkComparisons.LpDifference p)
      BenchmarkComparisons.EInfinity := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  have h := finite_ENNlp_not_reduces_eInfinity (ENNReal.ofReal p) ENNReal.ofReal_ne_top
  simpa only [ENNReal.toReal_ofReal (le_trans zero_le_one hp)] using h

end BenchmarkCountableReverse

#print axioms BenchmarkCountableReverse.finiteLp_not_reduces_eInfinity
