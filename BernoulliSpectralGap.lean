import WalshKoopmanRepresentation
import RegularFreeGroupGap

/-! The actual fair F₂ Bernoulli shift has a quantitative L² spectral gap.
The proof reindexes the nonconstant Walsh coefficients into free regular
orbits, applies the first-letter cone estimate, and transports norms back. -/

open MeasureTheory Filter Set
open scoped Topology ENNReal InnerProductSpace

noncomputable section

namespace BenchmarkShift

open BenchmarkCoordinateProjection BenchmarkRegularGap

def regularIndex (p : SupportOrbit × Group) : Finset Group := (supportOrbitEquiv.symm p).val

lemma regularIndex_injective : Function.Injective regularIndex :=
  Subtype.val_injective.comp supportOrbitEquiv.symm.injective

def regularCoefficients (u : BernoulliL2) : Space (SupportOrbit × Group) :=
  ⟨fun p => walshBasis.repr u (regularIndex p),
    (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
      (((lp.memℓp (walshBasis.repr u)).summable (by norm_num)).comp_injective regularIndex_injective)⟩

lemma coordinate_norm_sq {I : Type*} (v : Space I) : ‖v‖ ^ 2 = ∑' i, (v i) ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) v

theorem norm_regularCoefficients_le (u : BernoulliL2) : ‖regularCoefficients u‖ ≤ ‖u‖ := by
  have hs := tsum_comp_le_tsum_of_inj
    (show Summable (fun S => (walshBasis.repr u S) ^ 2) by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
        (lp.memℓp (walshBasis.repr u)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))
    (fun S => sq_nonneg _) regularIndex_injective
  have hnorm : ‖regularCoefficients u‖ ^ 2 ≤ ‖walshBasis.repr u‖ ^ 2 := by
    rw [coordinate_norm_sq, coordinate_norm_sq]
    exact hs
  rw [walshBasis.repr.norm_map] at hnorm
  nlinarith [norm_nonneg (regularCoefficients u), norm_nonneg u]

theorem norm_regularCoefficients_eq (u : BernoulliL2) (hmean : (∫ x, u x ∂bernoulli) = 0) :
    ‖regularCoefficients u‖ = ‖u‖ := by
  have hempty : walshBasis.repr u ∅ = 0 := (empty_walsh_coefficient u).trans hmean
  let b := fun S : Finset Group => (walshBasis.repr u S) ^ 2
  have hsupport : Function.support b ⊆ {S : Finset Group | S.Nonempty} := by
    intro S hS
    by_contra hne
    have heq : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst S
    exact hS (by simp [b, hempty])
  have hsub : (∑' S : NonemptySupport, b S.val) = ∑' S : Finset Group, b S :=
    tsum_subtype_eq_of_support_subset hsupport
  have hreindex : (∑' p : SupportOrbit × Group, b (regularIndex p)) =
      ∑' S : NonemptySupport, b S.val :=
    supportOrbitEquiv.symm.tsum_eq (fun S : NonemptySupport => b S.val)
  have hnorm : ‖regularCoefficients u‖ ^ 2 = ‖walshBasis.repr u‖ ^ 2 := by
    rw [coordinate_norm_sq, coordinate_norm_sq]
    exact hreindex.trans hsub
  rw [walshBasis.repr.norm_map] at hnorm
  nlinarith [norm_nonneg (regularCoefficients u), norm_nonneg u]

theorem regularCoefficients_sub (u v : BernoulliL2) :
    regularCoefficients (u - v) = regularCoefficients u - regularCoefficients v := by
  ext p
  change walshBasis.repr (u - v) (regularIndex p) =
    walshBasis.repr u (regularIndex p) - walshBasis.repr v (regularIndex p)
  rw [map_sub]
  rfl

theorem regularCoefficients_koopman (a : Letter) (u : BernoulliL2) :
    regularCoefficients (koopman (letterGroup a) u) =
      permute (leftPermutation a) (regularCoefficients u) := by
  ext p
  rcases p with ⟨q, h⟩
  change walshBasis.repr (koopman (letterGroup a) u) (regularIndex (q, h)) =
    walshBasis.repr u (regularIndex (q, (letterGroup a)⁻¹ * h))
  rw [walsh_coefficient_koopman]
  have hv := congrArg Subtype.val (supportOrbitEquiv_symm_mul q (letterGroup a)⁻¹ h)
  exact congrArg (fun S : Finset Group => walshBasis.repr u S) hv.symm

theorem bernoulli_L2_spectral_gap (u : BernoulliL2) (hmean : (∫ x, u x ∂bernoulli) = 0) :
    ‖u‖ ^ 2 ≤ 8 *
      (‖koopman (letterGroup (0, true)) u - u‖ ^ 2 +
        ‖koopman (letterGroup (1, true)) u - u‖ ^ 2) := by
  have hgap := regular_free_group_gap (regularCoefficients u)
  have hA : permute (leftPermutation (0, true)) (regularCoefficients u) - regularCoefficients u =
      regularCoefficients (koopman (letterGroup (0, true)) u - u) := by
    rw [regularCoefficients_sub, regularCoefficients_koopman]
  have hB : permute (leftPermutation (1, true)) (regularCoefficients u) - regularCoefficients u =
      regularCoefficients (koopman (letterGroup (1, true)) u - u) := by
    rw [regularCoefficients_sub, regularCoefficients_koopman]
  rw [norm_regularCoefficients_eq u hmean, hA, hB] at hgap
  have hca := norm_regularCoefficients_le (koopman (letterGroup (0, true)) u - u)
  have hcb := norm_regularCoefficients_le (koopman (letterGroup (1, true)) u - u)
  nlinarith [norm_nonneg (regularCoefficients (koopman (letterGroup (0, true)) u - u)),
    norm_nonneg (regularCoefficients (koopman (letterGroup (1, true)) u - u)),
    norm_nonneg (koopman (letterGroup (0, true)) u - u),
    norm_nonneg (koopman (letterGroup (1, true)) u - u)]

end BenchmarkShift

#print axioms BenchmarkShift.bernoulli_L2_spectral_gap
