import WalshL2Basis
import FiniteSupportTranslation

/-! The actual Koopman shifts permute the Walsh basis by left translation
of its finite supports. The empty coefficient is the integral. -/

open MeasureTheory Filter Set
open scoped Topology ENNReal InnerProductSpace

noncomputable section

namespace BenchmarkShift

def supportTranslate (g : Group) (S : Finset Group) : Finset Group :=
  S.image (fun h => g * h)

lemma walsh_shift_inverse (g : Group) (S : Finset Group) (x : Point) :
    walsh S (shift g⁻¹ x) = walsh (supportTranslate g S) x := by
  classical
  unfold walsh supportTranslate
  rw [Finset.prod_image]
  · simp only [shift, inv_inv]
  · intro a _ b _ hab
    exact mul_left_cancel hab

def koopman (g : Group) : BernoulliL2 →ₗᵢ[ℝ] BernoulliL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ (shift g⁻¹) (measurePreserving_shift g⁻¹)

theorem koopman_walshL2 (g : Group) (S : Finset Group) :
    koopman g (walshL2 S) = walshL2 (supportTranslate g S) := by
  apply Lp.ext
  have hcomp := Lp.coeFn_compMeasurePreserving (walshL2 S) (measurePreserving_shift g⁻¹)
  have hsource := (measurePreserving_shift g⁻¹).quasiMeasurePreserving.ae (walshL2_ae S)
  filter_upwards [hcomp, hsource, walshL2_ae (supportTranslate g S)] with x hc hs ht
  change (Lp.compMeasurePreserving (shift g⁻¹) (measurePreserving_shift g⁻¹) (walshL2 S)) x = _
  rw [hc, Function.comp_apply, hs, ht]
  exact walsh_shift_inverse g S x

theorem koopman_walshBasis (g : Group) (S : Finset Group) :
    koopman g (walshBasis S) = walshBasis (supportTranslate g S) := by
  simpa only [walshBasis_apply] using koopman_walshL2 g S

theorem supportTranslate_faithful (S : Finset Group) (hS : S.Nonempty)
    (g : Group) (h : supportTranslate g S = S) : g = 1 :=
  BenchmarkFiniteSupport.freeGroup_translate_eq_self_implies_one S hS g h

theorem empty_walsh_coefficient (u : BernoulliL2) :
    walshBasis.repr u ∅ = ∫ x, u x ∂bernoulli := by
  rw [HilbertBasis.repr_apply_apply, walshBasis_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [walshL2_ae ∅] with x hx
  rw [hx, Real.inner_apply]
  simp [walsh]

end BenchmarkShift

#print axioms BenchmarkShift.koopman_walshBasis
#print axioms BenchmarkShift.supportTranslate_faithful
