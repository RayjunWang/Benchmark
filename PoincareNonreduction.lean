import RealMedians
import SequencePoincareCollapse
import Mathlib.Analysis.Normed.Lp.lpSpace

/-! The measure-theoretic contradiction after scalar Poincaré collapse.
The abstract criterion below still requires a Poincaré bound for the chosen
source transformations; it does not assert that the Bernoulli bound has
already been formalized. -/

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace BenchmarkPoincareNonreduction

open BenchmarkPoincareRadial BenchmarkSequencePoincare BenchmarkRealMedians

lemma summable_difference_of_common_center
    (p : ℝ≥0∞) (hp : 0 < p.toReal) (a b m : ℕ → ℝ)
    (ha : Summable (fun i => |a i - m i| ^ p.toReal))
    (hb : Summable (fun i => |b i - m i| ^ p.toReal)) :
    Summable (fun i => |a i - b i| ^ p.toReal) := by
  have hma : Memℓp (fun i => a i - m i) p :=
    (memℓp_gen_iff hp).mpr (by simpa only [Real.norm_eq_abs] using ha)
  have hmb : Memℓp (fun i => b i - m i) p :=
    (memℓp_gen_iff hp).mpr (by simpa only [Real.norm_eq_abs] using hb)
  have hsub := (memℓp_gen_iff hp).mp (hma.sub hmb)
  simpa only [Pi.sub_apply, Real.norm_eq_abs, sub_sub_sub_cancel_right] using hsub

theorem exists_almost_sure_lp_class
    {X S : Type*} [MeasurableSpace X] [Fintype S]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (C : ℝ≥0∞) (hC : C ≠ ∞) (t : S → X → X) (ht : ∀ s, Measurable (t s))
    (hP : ScalarPoincareBound p μ t C)
    (f : X → ℕ → ℝ) (hf : Measurable f)
    (hdisplacement : ∀ s, ∀ᵐ x ∂μ,
      Summable (fun i => |f (t s x) i - f x i| ^ p.toReal)) :
    ∃ m : ℕ → ℝ, ∀ᵐ x ∂μ, Summable (fun i => |f x i - m i| ^ p.toReal) := by
  obtain ⟨m, hm⟩ := exists_coordinate_medians μ f hf
  exact ⟨m, ae_summable_centered_of_poincare p μ hp C hC t ht hP f hf m hm hdisplacement⟩

theorem no_lp_reduction_of_null_classes_and_poincare
    {X S : Type*} [MeasurableSpace X] [Fintype S]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (μ : Measure X) [IsProbabilityMeasure μ] (E : X → X → Prop)
    (hnull : ∀ x, μ {y | E x y} = 0)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (t : S → X → X) (ht : ∀ s, Measurable (t s))
    (hE : ∀ s, ∀ᵐ x ∂μ, E (t s x) x)
    (hP : ScalarPoincareBound p μ t C) :
    ¬ ∃ f : X → ℕ → ℝ, Measurable f ∧
      ∀ x y, E x y ↔ Summable (fun i => |f x i - f y i| ^ p.toReal) := by
  rintro ⟨f, hf, hred⟩
  have hdisplacement : ∀ s, ∀ᵐ x ∂μ,
      Summable (fun i => |f (t s x) i - f x i| ^ p.toReal) := by
    intro s
    filter_upwards [hE s] with x hx
    exact (hred (t s x) x).mp hx
  obtain ⟨m, hm⟩ := exists_almost_sure_lp_class p hp μ C hC t ht hP f hf hdisplacement
  obtain ⟨x₀, hx₀⟩ := hm.exists
  have hclass : ∀ᵐ x ∂μ, E x₀ x := by
    filter_upwards [hm] with x hx
    exact (hred x₀ x).mpr
      (summable_difference_of_common_center p (p.toReal_pos_iff_ne_top.mpr hp) _ _ _ hx₀ hx)
  let A : Set X := {x | E x₀ x}
  have hAzero : μ A = 0 := hnull x₀
  have hAc : μ Aᶜ = 0 := by simpa only [A, compl_setOf] using ae_iff.mp hclass
  have huniv : μ univ = 0 := by
    apply le_antisymm _ bot_le
    calc
      μ univ = μ (A ∪ Aᶜ) := by rw [union_compl_self]
      _ ≤ μ A + μ Aᶜ := measure_union_le _ _
      _ = 0 := by rw [hAzero, hAc, zero_add]
  exact (one_ne_zero : (1 : ℝ≥0∞) ≠ 0) (by simpa only [measure_univ] using huniv)

end BenchmarkPoincareNonreduction

#print axioms BenchmarkPoincareNonreduction.no_lp_reduction_of_null_classes_and_poincare
