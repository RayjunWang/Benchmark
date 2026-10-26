import CantorHaarFamily
import MeasureCantorDenseFamily

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

noncomputable section

namespace BenchmarkJump

private theorem haar_lp_finset_sum_coe {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Finset ι) (u : ι → Lp ℝ 2 μ) :
    (∑ i ∈ s, u i : Lp ℝ 2 μ) =ᵐ[μ] fun x => ∑ i ∈ s, u i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Lp.coeFn_zero (μ := μ) (E := ℝ) (p := 2))
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (u a) (∑ i ∈ s, u i), ih] with x hx hsum
      simpa only [Pi.add_apply, Finset.sum_insert ha] using
        hx.trans (congrArg (fun v => u a x + v) hsum)

def cantorLevelSimple (μ : PositiveCylinderProbabilities) (n : ℕ)
    (u : (Fin n → Bool) → ℝ) :
    Lp ℝ 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) :=
  ∑ s : Fin n → Bool, u s • cantorPrefixVector μ s

theorem cantorLevelSimple_mem_span (μ : PositiveCylinderProbabilities) (n : ℕ)
    (u : (Fin n → Bool) → ℝ) : cantorLevelSimple μ n u ∈ cantorHaarSpan μ :=
  (cantorHaarSpan μ).sum_mem (fun s _ =>
    (cantorHaarSpan μ).smul_mem (u s) (cantorPrefixVector_mem_span μ n s))

theorem cantorLevelSimple_coe (μ : PositiveCylinderProbabilities) (n : ℕ)
    (u : (Fin n → Bool) → ℝ) :
    cantorLevelSimple μ n u =ᵐ[((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)]
      fun x => u (fun i : Fin n => x i) := by
  classical
  have hOne (s : Fin n → Bool) :
      (u s • cantorPrefixVector μ s) =ᵐ[((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)]
        fun x => u s * (prefixCylinder s).indicator (fun _ => (1 : ℝ)) x := by
    filter_upwards [Lp.coeFn_smul (u s) (cantorPrefixVector μ s),
      indicatorConstLp_coeFn (p := 2) (hs := (isClopen_prefixCylinder s).isClosed.measurableSet)
        (hμs := measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) _)
        (c := (1 : ℝ))] with x hx hy
    simpa only [Pi.smul_apply, smul_eq_mul] using hx.trans (congrArg (fun z => u s * z) hy)
  have hAll := eventually_countable_forall.mpr hOne
  filter_upwards [haar_lp_finset_sum_coe
    ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) Finset.univ
      (fun s : Fin n → Bool => u s • cantorPrefixVector μ s), hAll] with x hx hAllx
  change (∑ s : Fin n → Bool, u s • cantorPrefixVector μ s) x = _
  rw [hx]
  simp_rw [hAllx]
  let s₀ : Fin n → Bool := fun i => x i
  rw [Finset.sum_eq_single s₀]
  · simp [prefixCylinder, s₀]
  · intro s _hs hss
    have hNot : x ∉ prefixCylinder s := by
      intro hxs
      apply hss
      funext i
      exact (hxs i).symm
    simp [hNot]
  · simp

/-- Every arbitrary finite-coordinate Cantor cylinder indicator is exactly
a finite-level prefix simple function, hence lies in the Haar span. -/
theorem cantorCylinder_indicator_mem_span (μ : PositiveCylinderProbabilities)
    (k : MeasureUnitary.CantorCylinderIndex) :
    indicatorConstLp 2 (MeasureUnitary.cantorCylinder_measurable k)
      (measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) _) (1 : ℝ) ∈
        cantorHaarSpan μ := by
  classical
  let N : ℕ := k.1.sup id + 1
  let project : (Fin N → Bool) → (∀ i : k.1, Bool) := fun s i =>
    s ⟨i, Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)⟩
  let u : (Fin N → Bool) → ℝ := fun s => if project s ∈ k.2 then 1 else 0
  have heq : indicatorConstLp 2 (MeasureUnitary.cantorCylinder_measurable k)
      (measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) _) (1 : ℝ) =
      cantorLevelSimple μ N u := by
    apply Lp.ext
    filter_upwards [indicatorConstLp_coeFn (p := 2)
      (hs := MeasureUnitary.cantorCylinder_measurable k)
      (hμs := measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) _)
      (c := (1 : ℝ)), cantorLevelSimple_coe μ N u] with x hx hy
    rw [hx, hy]
    have hp : project (fun i : Fin N => x i) = k.1.restrict x := rfl
    simp only [u, hp, MeasureUnitary.cantorCylinder, mem_cylinder, Set.indicator_apply]
  rw [heq]
  exact cantorLevelSimple_mem_span μ N u

theorem cantorCylinder_constant_mem_span (μ : PositiveCylinderProbabilities)
    (k : MeasureUnitary.CantorCylinderIndex) (c : ℝ) :
    indicatorConstLp 2 (MeasureUnitary.cantorCylinder_measurable k)
      (measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) _) c ∈
        cantorHaarSpan μ := by
  have heq : indicatorConstLp 2 (MeasureUnitary.cantorCylinder_measurable k)
      (measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) _) c =
      c • indicatorConstLp 2 (MeasureUnitary.cantorCylinder_measurable k)
        (measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) _) (1 : ℝ) := by
    apply Lp.ext
    filter_upwards [indicatorConstLp_coeFn (p := 2)
      (hs := MeasureUnitary.cantorCylinder_measurable k)
      (hμs := measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) _)
      (c := c), indicatorConstLp_coeFn (p := 2)
      (hs := MeasureUnitary.cantorCylinder_measurable k)
      (hμs := measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) _)
      (c := (1 : ℝ)), Lp.coeFn_smul c
        (indicatorConstLp 2 (MeasureUnitary.cantorCylinder_measurable k)
          (measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) _) (1 : ℝ))]
      with x hc h1 hs
    simp only [Pi.smul_apply, smul_eq_mul] at hs
    rw [hc, hs, h1]
    by_cases hx : x ∈ MeasureUnitary.cantorCylinder k <;> simp [hx]
  rw [heq]
  exact (cantorHaarSpan μ).smul_mem c (cantorCylinder_indicator_mem_span μ k)

/-- The actual Haar family is complete in the actual real L2 space. -/
theorem cantorHaarSpan_dense (μ : PositiveCylinderProbabilities) :
    (cantorHaarSpan μ).topologicalClosure = ⊤ := by
  let ν : Measure HaarCantor := ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
  let V := (cantorHaarSpan μ).topologicalClosure
  have hCylinder (k : MeasureUnitary.CantorCylinderIndex) (c : ℝ) :
      indicatorConstLp 2 (MeasureUnitary.cantorCylinder_measurable k) (measure_ne_top ν _) c ∈ V :=
    (Submodule.le_topologicalClosure (cantorHaarSpan μ)) (cantorCylinder_constant_mem_span μ k c)
  have hAllIndicators (c : ℝ) {s : Set HaarCantor} (hs : MeasurableSet s) (hνs : ν s ≠ ∞) :
      indicatorConstLp 2 hs hνs c ∈ V := by
    letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
    have ha := (MeasureUnitary.cantorCylinder_measureDense ν).indicatorConstLp_subset_closure 2 c
      (show indicatorConstLp 2 hs hνs c ∈
        {indicatorConstLp 2 ht hμt c | (t : Set HaarCantor) (ht : MeasurableSet t) (hμt : ν t ≠ ∞)}
        from ⟨s, hs, hνs, rfl⟩)
    apply closure_minimal (t := (V : Set _)) ?_ (Submodule.isClosed_topologicalClosure _) ha
    rintro x ⟨t, ht, hνt, rfl⟩
    obtain ⟨k, rfl⟩ := ht
    exact hCylinder k c
  have hall : ∀ f : Lp ℝ 2 ν, f ∈ V := by
    apply Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (fun f : Lp ℝ 2 ν => f ∈ V)
    · intro c s hs hνs
      exact hAllIndicators c hs hνs.ne
    · intro f g hf hg _hdis hfm hgm
      exact V.add_mem hfm hgm
    · exact Submodule.isClosed_topologicalClosure _
  apply top_unique
  intro f _hf
  exact hall f

def cantorRealHaarBasis (μ : PositiveCylinderProbabilities) :
    HilbertBasis (Option HaarNodeIndex) ℝ
      (Lp ℝ 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) :=
  HilbertBasis.mk (cantorHaarFamily_orthonormal μ) (by
    rw [span_cantorHaarFamily, cantorHaarSpan_dense])

#print axioms cantorHaarSpan_dense
#print axioms cantorRealHaarBasis

end BenchmarkJump
