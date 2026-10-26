import MeasureGramSchmidtBorel
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! A finite orthogonal family, allowing zero entries, gives its actual
orthogonal projection by the usual measurable coefficient formula. -/

open MeasureTheory Set Finset Filter Topology
open scoped InnerProductSpace

set_option maxHeartbeats 1500000

namespace MeasureUnitary

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def finiteFamilySpan (f : ℕ → H) (n : ℕ) : Submodule ℂ H :=
  Submodule.span ℂ (f '' Set.Iio n)

instance finiteFamilySpan_finiteDimensional (f : ℕ → H) (n : ℕ) :
    FiniteDimensional ℂ (finiteFamilySpan f n) :=
  FiniteDimensional.span_of_finite ℂ ((Set.finite_Iio n).image f)

def finiteOrthogonalProjection (f : ℕ → H) (n : ℕ) (x : H) : H :=
  ∑ i ∈ Finset.range n, (inner ℂ (f i) x / inner ℂ (f i) (f i)) • f i

theorem finiteOrthogonalProjection_mem (f : ℕ → H) (n : ℕ) (x : H) :
    finiteOrthogonalProjection f n x ∈ finiteFamilySpan f n := by
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨i, Finset.mem_range.mp hi, rfl⟩

theorem finiteOrthogonalProjection_inner (f : ℕ → H)
    (horth : Pairwise (fun i j => inner ℂ (f i) (f j) = 0))
    (n : ℕ) (x : H) (i : ℕ) (hi : i < n) :
    inner ℂ (f i) (x - finiteOrthogonalProjection f n x) = 0 := by
  rw [inner_sub_right]
  have hsum : inner ℂ (f i) (finiteOrthogonalProjection f n x) = inner ℂ (f i) x := by
    rw [finiteOrthogonalProjection, inner_sum]
    rw [Finset.sum_eq_single i]
    · rw [inner_smul_right]
      by_cases hzero : f i = 0
      · simp [hzero]
      · exact div_mul_cancel₀ _ (inner_self_ne_zero.mpr hzero)
    · intro j hj hji
      rw [inner_smul_right, horth hji.symm, mul_zero]
    · intro hni
      exact (hni (Finset.mem_range.mpr hi)).elim
  rw [hsum, sub_self]

theorem finiteOrthogonalProjection_eq_starProjection (f : ℕ → H)
    (horth : Pairwise (fun i j => inner ℂ (f i) (f j) = 0)) (n : ℕ) (x : H) :
    finiteOrthogonalProjection f n x = (finiteFamilySpan f n).starProjection x := by
  symm
  apply (finiteFamilySpan f n).eq_starProjection_of_mem_of_inner_eq_zero
    (finiteOrthogonalProjection_mem f n x)
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, hi, rfl⟩ := hw
    rw [inner_eq_zero_symm]
    exact finiteOrthogonalProjection_inner f horth n x i hi
  | zero => simp
  | add u v hu hv ihu ihv => simp only [inner_add_right, ihu, ihv, add_zero]
  | smul a u hu ihu => simp only [inner_smul_right, ihu, mul_zero]

variable {S : Type*} [MeasurableSpace S] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H]

theorem finiteOrthogonalProjection_measurable (f : S → ℕ → H)
    (hf : ∀ i, Measurable (fun s => f s i)) (x : S → H) (hx : Measurable x) (n : ℕ) :
    Measurable (fun s => finiteOrthogonalProjection (f s) n (x s)) := by
  unfold finiteOrthogonalProjection
  apply Finset.measurable_sum
  intro i hi
  exact ((hf i).inner hx |>.div ((hf i).inner (hf i))).smul (hf i)

end
end MeasureUnitary

#print axioms MeasureUnitary.finiteOrthogonalProjection_eq_starProjection
