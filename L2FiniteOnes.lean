import L2LocalizedAdjoints

/-! Canonical indicator vectors for finite sets, including their exact
mass, restriction and zero-extension identities. -/

open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace

namespace MeasureEquivalenceL2Restriction

open MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def finiteOne (A : Set X) (hA : MeasurableSet A) (hfin : μ A ≠ ∞) : Lp ℂ 2 μ :=
  indicatorConstLp 2 hA hfin (1 : ℂ)

def restrictedOne (A : Set X) (hfin : μ A ≠ ∞) : Lp ℂ 2 (μ.restrict A) :=
  indicatorConstLp 2 MeasurableSet.univ (by simpa using hfin) (1 : ℂ)

theorem finiteOne_coe (A : Set X) (hA : MeasurableSet A) (hfin : μ A ≠ ∞) :
    finiteOne μ A hA hfin =ᵐ[μ] A.indicator (fun _ => (1 : ℂ)) :=
  indicatorConstLp_coeFn

theorem restrictedOne_coe (A : Set X) (hfin : μ A ≠ ∞) :
    restrictedOne μ A hfin =ᵐ[μ.restrict A] fun _ => (1 : ℂ) := by
  simpa only [Set.indicator_univ] using
    (indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
      (hμs := by simpa using hfin) (c := (1 : ℂ)))

theorem restrictedOne_norm_sq (A : Set X) (hfin : μ A ≠ ∞) :
    ‖restrictedOne μ A hfin‖ ^ 2 = μ.real A := by
  rw [l2_norm_sq_integral]
  calc
    (∫ x, ‖restrictedOne μ A hfin x‖ ^ 2 ∂μ.restrict A) = ∫ _ : X, (1 : ℝ) ∂μ.restrict A := by
      apply integral_congr_ae
      filter_upwards [restrictedOne_coe μ A hfin] with x hx
      simp [hx]
    _ = μ.real A := by simp [measureReal_def]

theorem zeroExtend_restrictedOne (A : Set X) (hA : MeasurableSet A) (hfin : μ A ≠ ∞) :
    zeroExtend μ A hA (restrictedOne μ A hfin) = finiteOne μ A hA hfin := by
  apply Lp.ext
  have hc := (ae_eq_restrict_iff_indicator_ae_eq hA).mp (restrictedOne_coe μ A hfin)
  filter_upwards [zeroExtend_coe μ A hA (restrictedOne μ A hfin),
    finiteOne_coe μ A hA hfin, hc] with x he hf hone
  exact he.trans (hone.trans hf.symm)

theorem indicatorL2_nested (A C : Set X) (hA : MeasurableSet A) (hC : MeasurableSet C)
    (hsub : A ⊆ C) (f : Lp ℂ 2 μ) :
    indicatorL2 μ hA (indicatorL2 μ hC f) = indicatorL2 μ hA f := by
  apply Lp.ext
  filter_upwards [indicatorL2_coe μ hA (indicatorL2 μ hC f),
    indicatorL2_coe μ hC f, indicatorL2_coe μ hA f] with x ha hc hf
  rw [ha, hf]
  by_cases hx : x ∈ A
  · simp [hx, hsub hx, hc]
  · simp [hx]

theorem indicatorL2_nested_reverse (A C : Set X) (hA : MeasurableSet A) (hC : MeasurableSet C)
    (hsub : A ⊆ C) (f : Lp ℂ 2 μ) :
    indicatorL2 μ hC (indicatorL2 μ hA f) = indicatorL2 μ hA f := by
  apply Lp.ext
  filter_upwards [indicatorL2_coe μ hC (indicatorL2 μ hA f),
    indicatorL2_coe μ hA f] with x hc ha
  rw [hc]
  by_cases hx : x ∈ A
  · simp [hx, hsub hx]
  · by_cases hxC : x ∈ C <;> simp [hx, hxC, ha]

end
end MeasureEquivalenceL2Restriction

#print axioms MeasureEquivalenceL2Restriction.restrictedOne_norm_sq
