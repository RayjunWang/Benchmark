import ClopenHaarNode

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace BenchmarkJump

variable {α : Type*} [MeasurableSpace α]

/-- Each child indicator belongs to the span of the parent indicator and
its actual normalized Haar difference. This is the recursive completeness
step for the varying Cantor Haar basis. -/
theorem splitHaar_children_mem_span (μ : Measure α) [IsFiniteMeasure μ]
    (A B : Set α) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (ha : 0 < μ.real A) (hb : 0 < μ.real B) :
    let parent : Lp ℝ 2 μ :=
      indicatorConstLp 2 (hA.union hB) (measure_ne_top μ _) (1 : ℝ)
    let V := Submodule.span ℝ ({parent, splitHaar μ A B hA hB} : Set (Lp ℝ 2 μ))
    indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ) ∈ V ∧
      indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ) ∈ V := by
  let f : Lp ℝ 2 μ := indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ)
  let g : Lp ℝ 2 μ := indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ)
  let parent : Lp ℝ 2 μ := indicatorConstLp 2 (hA.union hB) (measure_ne_top μ _) (1 : ℝ)
  let w := splitHaar μ A B hA hB
  let V := Submodule.span ℝ ({parent, w} : Set (Lp ℝ 2 μ))
  change f ∈ V ∧ g ∈ V
  have hp : parent ∈ V := Submodule.subset_span (by simp)
  have hw : w ∈ V := Submodule.subset_span (by simp)
  have hparent : parent = f + g := indicatorConstLp_disjoint_union hA hB _ _ hAB 1
  let d : ℝ := Real.sqrt (μ.real A * μ.real B * (μ.real A + μ.real B))
  have hd : d ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hsum : μ.real A + μ.real B ≠ 0 := by positivity
  have hwExp : d • w = μ.real B • f - μ.real A • g := by
    change d • (d⁻¹ • (μ.real B • f - μ.real A • g)) = _
    rw [smul_smul, mul_inv_cancel₀ hd, one_smul]
  have hleft : (μ.real A + μ.real B) • f ∈ V := by
    have hlin := V.add_mem (V.smul_mem (μ.real A) hp) (V.smul_mem d hw)
    have heq : μ.real A • parent + d • w = (μ.real A + μ.real B) • f := by
      rw [hparent, hwExp]
      module
    rwa [heq] at hlin
  have hf : f ∈ V := by
    have h := V.smul_mem (μ.real A + μ.real B)⁻¹ hleft
    simpa only [smul_smul, inv_mul_cancel₀ hsum, one_smul] using h
  have hg : g ∈ V := by
    have heq : parent - f = g := by rw [hparent]; abel
    simpa only [heq] using V.sub_mem hp hf
  exact ⟨hf, hg⟩

#print axioms splitHaar_children_mem_span

end BenchmarkJump
