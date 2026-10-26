import WalshSupportOrbits

/-! Group laws and coefficient transport for the actual Koopman action. -/

open MeasureTheory Filter Set
open scoped Topology ENNReal InnerProductSpace

noncomputable section

namespace BenchmarkShift

lemma koopman_ae (g : Group) (u : BernoulliL2) :
    (koopman g u : Point → ℝ) =ᵐ[bernoulli] fun x => u (shift g⁻¹ x) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_shift g⁻¹)

theorem koopman_one (u : BernoulliL2) : koopman 1 u = u := by
  apply Lp.ext
  filter_upwards [koopman_ae 1 u] with x hx
  simpa only [inv_one, shift_one] using hx

theorem koopman_mul (g h : Group) (u : BernoulliL2) : koopman g (koopman h u) = koopman (g * h) u := by
  apply Lp.ext
  have hg := koopman_ae g (koopman h u)
  have hh := (measurePreserving_shift g⁻¹).quasiMeasurePreserving.ae
    (koopman_ae h u)
  have hgh := koopman_ae (g * h) u
  filter_upwards [hg, hh, hgh] with x hx hy hz
  calc
    koopman g (koopman h u) x = koopman h u (shift g⁻¹ x) := hx
    _ = u (shift h⁻¹ (shift g⁻¹ x)) := hy
    _ = u (shift (g * h)⁻¹ x) := by rw [shift_mul, mul_inv_rev]
    _ = koopman (g * h) u x := hz.symm

theorem inner_walshL2_koopman (g : Group) (S : Finset Group) (u : BernoulliL2) :
    ⟪walshL2 S, koopman g u⟫_ℝ = ⟪walshL2 (supportTranslate g⁻¹ S), u⟫_ℝ := by
  have h := (koopman g).inner_map_map (koopman g⁻¹ (walshL2 S)) u
  rw [koopman_mul, mul_inv_cancel, koopman_one, koopman_walshL2] at h
  exact h

theorem walsh_coefficient_koopman (g : Group) (S : Finset Group) (u : BernoulliL2) :
    walshBasis.repr (koopman g u) S = walshBasis.repr u (supportTranslate g⁻¹ S) := by
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, walshBasis_apply, walshBasis_apply]
  exact inner_walshL2_koopman g S u

end BenchmarkShift

#print axioms BenchmarkShift.walsh_coefficient_koopman
