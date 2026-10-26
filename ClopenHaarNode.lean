import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.Indicator
import Mathlib.Tactic

/-! Concrete varying-measure Haar nodes for a positive clopen split.
The node is (b 1_A - a 1_B)/sqrt(a*b*(a+b)), algebraically equal to
the coefficients displayed in Benchmark.tex. -/

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

variable {α : Type*} [MeasurableSpace α]

def splitHaar (μ : Measure α) [IsFiniteMeasure μ]
    (A B : Set α) (hA : MeasurableSet A) (hB : MeasurableSet B) : Lp ℝ 2 μ :=
  (Real.sqrt (μ.real A * μ.real B * (μ.real A + μ.real B)))⁻¹ •
    ((μ.real B) • indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ) -
      (μ.real A) • indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ))

theorem splitHaar_norm (μ : Measure α) [IsFiniteMeasure μ]
    (A B : Set α) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (ha : 0 < μ.real A) (hb : 0 < μ.real B) :
    ‖splitHaar μ A B hA hB‖ = 1 := by
  let f : Lp ℝ 2 μ := indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ)
  let g : Lp ℝ 2 μ := indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ)
  have hff : inner ℝ f f = μ.real A := by
    simpa only [f, inter_self] using
      L2.real_inner_indicatorConstLp_one_indicatorConstLp_one hA hA
  have hgg : inner ℝ g g = μ.real B := by
    simpa only [g, inter_self] using
      L2.real_inner_indicatorConstLp_one_indicatorConstLp_one hB hB
  have hfg : inner ℝ f g = 0 := by
    simpa only [f, g, disjoint_iff_inter_eq_empty.mp hAB, measureReal_empty] using
      L2.real_inner_indicatorConstLp_one_indicatorConstLp_one hA hB
  have hgf : inner ℝ g f = 0 := by rw [real_inner_comm, hfg]
  have hsq : ‖μ.real B • f - μ.real A • g‖ ^ 2 =
      μ.real A * μ.real B * (μ.real A + μ.real B) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real, hff, hgg, hfg, hgf]
    ring
  have hpos : 0 < μ.real A * μ.real B * (μ.real A + μ.real B) := by positivity
  have hroot : 0 < Real.sqrt (μ.real A * μ.real B * (μ.real A + μ.real B)) :=
    Real.sqrt_pos.mpr hpos
  have hnorm : ‖μ.real B • f - μ.real A • g‖ =
      Real.sqrt (μ.real A * μ.real B * (μ.real A + μ.real B)) := by
    nlinarith [Real.sq_sqrt hpos.le, norm_nonneg (μ.real B • f - μ.real A • g)]
  change ‖(Real.sqrt (μ.real A * μ.real B * (μ.real A + μ.real B)))⁻¹ •
    (μ.real B • f - μ.real A • g)‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hroot), hnorm,
    inv_mul_cancel₀ hroot.ne']

theorem splitHaar_inner_one (μ : Measure α) [IsFiniteMeasure μ]
    (A B : Set α) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    inner ℝ (splitHaar μ A B hA hB)
      (indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1 : ℝ)) = 0 := by
  unfold splitHaar
  simp only [inner_smul_left, inner_sub_left, RCLike.conj_to_real,
    L2.real_inner_indicatorConstLp_one_indicatorConstLp_one, inter_univ]
  ring

section Topology

variable [TopologicalSpace α] [CompactSpace α] [BorelSpace α]

theorem continuous_clopen_mass (A : Set α) (hA : IsClopen A) :
    Continuous (fun μ : ProbabilityMeasure α => (μ : Measure α).real A) := by
  let f : C(α, ℝ) := ⟨A.indicator (fun _ => 1), hA.continuous_indicator continuous_const⟩
  have hcont := ProbabilityMeasure.continuous_integral_continuousMap f
  have heq : (fun μ : ProbabilityMeasure α => ∫ x, f x ∂(μ : Measure α)) =
      (fun μ : ProbabilityMeasure α => (μ : Measure α).real A) := by
    funext μ
    exact integral_indicator_one hA.isClosed.measurableSet
  rwa [heq] at hcont

def PositiveSplitProbabilities (A B : Set α) : Set (ProbabilityMeasure α) :=
  {μ | 0 < (μ : Measure α).real A ∧ 0 < (μ : Measure α).real B}

theorem isOpen_positiveSplitProbabilities (A B : Set α)
    (hA : IsClopen A) (hB : IsClopen B) : IsOpen (PositiveSplitProbabilities A B) :=
  (isOpen_lt continuous_const (continuous_clopen_mass A hA)).inter
    (isOpen_lt continuous_const (continuous_clopen_mass B hB))

def haarNodeFunction (A B : Set α) (μ : ProbabilityMeasure α) (x : α) : ℝ :=
  ((μ : Measure α).real B * A.indicator (fun _ => (1 : ℝ)) x -
    (μ : Measure α).real A * B.indicator (fun _ => (1 : ℝ)) x) /
      Real.sqrt ((μ : Measure α).real A * (μ : Measure α).real B *
        ((μ : Measure α).real A + (μ : Measure α).real B))

/-- Finite Haar node values depend jointly continuously on the weak measure
parameter and the underlying point, on the genuine positive-mass locus. -/
theorem continuous_haarNodeFunction (A B : Set α) (hA : IsClopen A) (hB : IsClopen B) :
    Continuous (fun p : PositiveSplitProbabilities A B × α =>
      haarNodeFunction A B p.1 p.2) := by
  have ha : Continuous (fun μ : PositiveSplitProbabilities A B =>
      ((μ : ProbabilityMeasure α) : Measure α).real A) :=
    (continuous_clopen_mass A hA).comp continuous_subtype_val
  have hb : Continuous (fun μ : PositiveSplitProbabilities A B =>
      ((μ : ProbabilityMeasure α) : Measure α).real B) :=
    (continuous_clopen_mass B hB).comp continuous_subtype_val
  unfold haarNodeFunction
  apply Continuous.div
  · exact ((hb.comp continuous_fst).mul
      ((hA.continuous_indicator continuous_const).comp continuous_snd)).sub
      ((ha.comp continuous_fst).mul
        ((hB.continuous_indicator continuous_const).comp continuous_snd))
  · exact (((ha.mul hb).mul (ha.add hb)).sqrt).comp continuous_fst
  · intro p
    apply (Real.sqrt_pos.mpr ?_).ne'
    have hpa := p.1.property.1
    have hpb := p.1.property.2
    positivity

#print axioms splitHaar_norm
#print axioms continuous_haarNodeFunction

end Topology
end BenchmarkJump
