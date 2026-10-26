import WalshContinuousDensity
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! A complete Walsh Hilbert basis for the actual Bernoulli L² space.
Uniform Stone-Weierstrass density is transported through the continuous
map from continuous functions to L². -/

open MeasureTheory Filter Set
open scoped Topology ENNReal InnerProductSpace

noncomputable section

namespace BenchmarkShift

local instance : DecidableEq Group := Classical.decEq Group

abbrev BernoulliL2 := Lp ℝ 2 bernoulli

def walshL2 (S : Finset Group) : BernoulliL2 :=
  ContinuousMap.toLp 2 bernoulli ℝ (continuousWalsh S)

lemma walshL2_ae (S : Finset Group) : (walshL2 S : Point → ℝ) =ᵐ[bernoulli] walsh S :=
  ContinuousMap.coeFn_toLp (p := 2) (μ := bernoulli) (𝕜 := ℝ) (continuousWalsh S)

theorem inner_walshL2 (S T : Finset Group) :
    ⟪walshL2 S, walshL2 T⟫_ℝ = if S = T then 1 else 0 := by
  rw [L2.inner_def]
  apply Eq.trans _ (integral_walsh_mul S T)
  apply integral_congr_ae
  filter_upwards [walshL2_ae S, walshL2_ae T] with x hx hy
  rw [hx, hy, Real.inner_apply]

theorem orthonormal_walshL2 : Orthonormal ℝ walshL2 :=
  orthonormal_iff_ite.mpr inner_walshL2

theorem dense_walshL2_span : Dense (Submodule.span ℝ (Set.range walshL2) : Set BernoulliL2) := by
  let T : C(Point, ℝ) →L[ℝ] BernoulliL2 := ContinuousMap.toLp 2 bernoulli ℝ
  have hT : DenseRange T := ContinuousMap.toLp_denseRange
    (E := ℝ) (μ := bernoulli) (p := 2) (𝕜 := ℝ) (by norm_num)
  have hd := hT.dense_image T.continuous dense_continuous_walsh_span
  have himage : T '' (Submodule.span ℝ (Set.range continuousWalsh) : Set C(Point, ℝ)) =
      ((Submodule.span ℝ (Set.range continuousWalsh)).map T.toLinearMap : Set BernoulliL2) := rfl
  rw [himage, Submodule.map_span, ← Set.range_comp] at hd
  exact hd

def walshBasis : HilbertBasis (Finset Group) ℝ BernoulliL2 :=
  HilbertBasis.mk orthonormal_walshL2 (by
    rw [(Submodule.dense_iff_topologicalClosure_eq_top).mp dense_walshL2_span])

@[simp] lemma walshBasis_apply (S : Finset Group) : walshBasis S = walshL2 S := by
  simp [walshBasis]

end BenchmarkShift

#print axioms BenchmarkShift.walshBasis
