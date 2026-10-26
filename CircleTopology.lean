import CircleGrids
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open Filter Topology Set TopologicalSpace
open scoped Topology BigOperators ENNReal NNReal

noncomputable section

namespace MeasureEquivalenceCircleTopology

open MeasureEquivalenceCircle

abbrev K := ℕ → UnitAddCircle

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

def trunc (s : Finset ℕ) (x : K) : Hp p :=
  ∑ i ∈ s, lp.single p i (x i)

lemma continuous_trunc (s : Finset ℕ) : Continuous (trunc p s) := by
  apply continuous_finsetSum
  intro i hi
  exact (lp.singleContinuousAddMonoidHom (fun _ : ℕ => UnitAddCircle) p i).continuous.comp
    (continuous_apply i)

lemma dense_trunc (hp : p ≠ ⊤) : Dense (⋃ s : Finset ℕ, range (trunc p s)) := by
  intro x
  have hx := lp.hasSum_single hp x
  apply mem_closure_of_tendsto hx
  exact Filter.Eventually.of_forall (fun s => mem_iUnion.mpr ⟨s, ⟨(x : K), rfl⟩⟩)

theorem hp_separable (hp : p ≠ ⊤) : SeparableSpace (Hp p) := by
  apply (dense_trunc p hp).isSeparable_iff.mp
  exact IsSeparable.iUnion (fun s => isSeparable_range (continuous_trunc p s))

lemma continuous_hp_coordinates : Continuous (fun h : Hp p => (h : K)) := by
  apply continuous_pi
  intro i
  exact (lp.lipschitzWith_one_eval p i).continuous

theorem hp_polish (hp : p ≠ ⊤) : PolishSpace (Hp p) := by
  let := hp_separable p hp
  infer_instance

lemma h0_closed : IsClosed (H0subgroup : Set (Hp ⊤)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro u x hu hx
  change Tendsto (fun k => x k) atTop (𝓝 0)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := (Metric.tendsto_nhds.mp hx (ε / 2) (by positivity)).exists
  have huj : Tendsto (fun k => u j k) atTop (𝓝 0) := hu j
  filter_upwards [Metric.tendsto_nhds.mp huj (ε / 2) (by positivity)] with k hk
  have hcoord : dist (x k) (u j k) ≤ dist x (u j) := by
    simpa only [dist_eq_norm, lp.coeFn_sub, Pi.sub_apply] using
      lp.norm_apply_le_norm ENNReal.top_ne_zero (x - u j) k
  calc
    dist (x k) 0 ≤ dist (x k) (u j k) + dist (u j k) 0 := dist_triangle _ _ _
    _ ≤ dist x (u j) + dist (u j k) 0 := add_le_add hcoord le_rfl
    _ < ε := by rw [dist_comm x]; linarith

theorem h0_complete : CompleteSpace H0 := h0_closed.isComplete.completeSpace_coe

omit [Fact (1 ≤ p)] in
lemma trunc_apply (s : Finset ℕ) (x : K) (k : ℕ) :
    trunc p s x k = if k ∈ s then x k else 0 := by
  simp only [trunc, lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply,
    Finset.sum_pi_single]

lemma trunc_null (s : Finset ℕ) (x : K) : trunc ⊤ s x ∈ H0subgroup := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (s.sup id)] with k hk
  have hkn : k ∉ s := by
    intro hmem
    have : k ≤ s.sup id := Finset.le_sup (f := id) hmem
    omega
  simp [trunc_apply, hkn]

def trunc0 (s : Finset ℕ) (x : K) : H0 := ⟨trunc ⊤ s x, trunc_null s x⟩

lemma continuous_trunc0 (s : Finset ℕ) : Continuous (trunc0 s) :=
  (continuous_trunc ⊤ s).subtype_mk _

lemma tendsto_trunc0 (x : H0) :
    Tendsto (fun N : ℕ => trunc0 (Finset.range N) ((x : Hp ⊤) : K)) atTop (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hx : Tendsto (fun k => (x : Hp ⊤) k) atTop (𝓝 0) := x.property
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (Metric.tendsto_nhds.mp hx (ε / 2) (by positivity))
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (b := ε / 2) _ (by linarith)
  change ‖trunc ⊤ (Finset.range n) ((x : Hp ⊤) : K) - (x : Hp ⊤)‖ ≤ ε / 2
  apply lp.norm_le_of_forall_le (by positivity)
  intro k
  simp only [lp.coeFn_sub, Pi.sub_apply, trunc_apply, Finset.mem_range]
  split_ifs with hk
  · simp; positivity
  · have hNk : N ≤ k := by omega
    simpa only [zero_sub, norm_neg, dist_zero_right] using (hN k hNk).le

lemma dense_trunc0 : Dense (⋃ s : Finset ℕ, range (trunc0 s)) := by
  intro x
  apply mem_closure_of_tendsto (tendsto_trunc0 x)
  exact Filter.Eventually.of_forall (fun N =>
    mem_iUnion.mpr ⟨Finset.range N, ⟨((x : Hp ⊤) : K), rfl⟩⟩)

theorem h0_separable : SeparableSpace H0 := by
  apply dense_trunc0.isSeparable_iff.mp
  exact IsSeparable.iUnion (fun s => isSeparable_range (continuous_trunc0 s))

theorem h0_polish : PolishSpace H0 := by
  let := h0_complete
  let := h0_separable
  infer_instance

lemma continuous_h0_coordinates : Continuous (fun h : H0 => ((h : Hp ⊤) : K)) :=
  (continuous_hp_coordinates ⊤).comp continuous_subtype_val

end MeasureEquivalenceCircleTopology

#print axioms MeasureEquivalenceCircleTopology.hp_separable
#print axioms MeasureEquivalenceCircleTopology.continuous_hp_coordinates
#print axioms MeasureEquivalenceCircleTopology.hp_polish
#print axioms MeasureEquivalenceCircleTopology.h0_closed
#print axioms MeasureEquivalenceCircleTopology.h0_complete
#print axioms MeasureEquivalenceCircleTopology.tendsto_trunc0
#print axioms MeasureEquivalenceCircleTopology.h0_separable
#print axioms MeasureEquivalenceCircleTopology.h0_polish
#print axioms MeasureEquivalenceCircleTopology.continuous_h0_coordinates
