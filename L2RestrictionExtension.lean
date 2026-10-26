import L2CountAdjoints

/-! Actual bounded restriction and isometric zero extension for complex
L2 spaces, including their projection and adjoint identities. -/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

namespace MeasureEquivalenceL2Restriction

open MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def restrictMap (A : Set X) (f : Lp ℂ 2 μ) : Lp ℂ 2 (μ.restrict A) :=
  ((Lp.memLp f).restrict A).toLp f

theorem restrict_coe (A : Set X) (f : Lp ℂ 2 μ) :
    restrictMap μ A f =ᵐ[μ.restrict A] f := ((Lp.memLp f).restrict A).coeFn_toLp

theorem restrict_norm_le (A : Set X) (f : Lp ℂ 2 μ) :
    ‖restrictMap μ A f‖ ≤ ‖f‖ := by
  rw [restrictMap, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_restrict_le f 2 μ A)

def restrictCLM (A : Set X) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (μ.restrict A) :=
  LinearMap.mkContinuous
    { toFun := restrictMap μ A
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [restrict_coe μ A (f+g), restrict_coe μ A f, restrict_coe μ A g,
          Lp.coeFn_add (restrictMap μ A f) (restrictMap μ A g),
          ae_restrict_of_ae (Lp.coeFn_add f g)] with x hfg hf hg hadd hsource
        simp only [Pi.add_apply] at hadd hsource
        rw [hfg, hadd, hf, hg, hsource]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [restrict_coe μ A (c • f), restrict_coe μ A f,
          Lp.coeFn_smul c (restrictMap μ A f), ae_restrict_of_ae (Lp.coeFn_smul c f)]
          with x hcf hf hsmul hsource
        simp only [Pi.smul_apply] at hsmul hsource
        simp only [RingHom.id_apply]
        rw [hcf, hsmul, hf, hsource] }
    1 (fun f => by simpa only [one_mul] using restrict_norm_le μ A f)

def zeroExtend (A : Set X) (hA : MeasurableSet A) (f : Lp ℂ 2 (μ.restrict A)) : Lp ℂ 2 μ :=
  ((memLp_indicator_iff_restrict hA).mpr (Lp.memLp f)).toLp (A.indicator f)

theorem zeroExtend_coe (A : Set X) (hA : MeasurableSet A) (f : Lp ℂ 2 (μ.restrict A)) :
    zeroExtend μ A hA f =ᵐ[μ] A.indicator f :=
  ((memLp_indicator_iff_restrict hA).mpr (Lp.memLp f)).coeFn_toLp

theorem zeroExtend_norm (A : Set X) (hA : MeasurableSet A) (f : Lp ℂ 2 (μ.restrict A)) :
    ‖zeroExtend μ A hA f‖ = ‖f‖ := by
  rw [zeroExtend, Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hA, Lp.norm_def]

def zeroExtendLI (A : Set X) (hA : MeasurableSet A) :
    Lp ℂ 2 (μ.restrict A) →ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun := zeroExtend μ A hA
  map_add' := by
    intro f g
    apply Lp.ext
    have hs := (ae_eq_restrict_iff_indicator_ae_eq hA).mp (Lp.coeFn_add f g)
    filter_upwards [zeroExtend_coe μ A hA (f+g), zeroExtend_coe μ A hA f,
      zeroExtend_coe μ A hA g, Lp.coeFn_add (zeroExtend μ A hA f) (zeroExtend μ A hA g), hs]
      with x hfg hf hg hadd hsource
    simp only [Pi.add_apply] at hadd
    rw [hfg, hadd, hf, hg, hsource]
    by_cases hx : x ∈ A <;> simp [hx]
  map_smul' := by
    intro c f
    apply Lp.ext
    have hs := (ae_eq_restrict_iff_indicator_ae_eq hA).mp (Lp.coeFn_smul c f)
    filter_upwards [zeroExtend_coe μ A hA (c • f), zeroExtend_coe μ A hA f,
      Lp.coeFn_smul c (zeroExtend μ A hA f), hs] with x hcf hf hsmul hsource
    simp only [Pi.smul_apply] at hsmul
    simp only [RingHom.id_apply]
    rw [hcf, hsmul, hf, hsource]
    by_cases hx : x ∈ A <;> simp [hx]
  norm_map' := zeroExtend_norm μ A hA

theorem restrict_zeroExtend (A : Set X) (hA : MeasurableSet A)
    (f : Lp ℂ 2 (μ.restrict A)) : restrictMap μ A (zeroExtend μ A hA f) = f := by
  apply Lp.ext
  filter_upwards [restrict_coe μ A (zeroExtend μ A hA f),
    ae_restrict_of_ae (zeroExtend_coe μ A hA f), ae_restrict_mem hA] with x hr he hx
  rw [hr, he]
  simp only [Set.indicator_of_mem hx]

theorem zeroExtend_restrict (A : Set X) (hA : MeasurableSet A) (f : Lp ℂ 2 μ) :
    zeroExtend μ A hA (restrictMap μ A f) = indicatorL2 μ hA f := by
  apply Lp.ext
  have hs := (ae_eq_restrict_iff_indicator_ae_eq hA).mp (restrict_coe μ A f)
  filter_upwards [zeroExtend_coe μ A hA (restrictMap μ A f), indicatorL2_coe μ hA f, hs]
    with x he hi hsx
  exact he.trans (hsx.trans hi.symm)

theorem inner_zeroExtend_restrict (A : Set X) (hA : MeasurableSet A)
    (f : Lp ℂ 2 (μ.restrict A)) (g : Lp ℂ 2 μ) :
    inner ℂ (zeroExtend μ A hA f) g = inner ℂ f (restrictMap μ A g) := by
  rw [L2.inner_def, L2.inner_def]
  calc
    (∫ x, inner ℂ (zeroExtend μ A hA f x) (g x) ∂μ) =
        ∫ x, A.indicator (fun y => inner ℂ (f y) (g y)) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [zeroExtend_coe μ A hA f] with x hx
      rw [hx]
      by_cases hxA : x ∈ A <;> simp [hxA]
    _ = ∫ x in A, inner ℂ (f x) (g x) ∂μ := integral_indicator hA
    _ = ∫ x in A, inner ℂ (f x) (restrictMap μ A g x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [restrict_coe μ A g] with x hx
      rw [hx]

theorem restrict_adjoint (A : Set X) (hA : MeasurableSet A) :
    (restrictCLM μ A).adjoint = (zeroExtendLI μ A hA).toContinuousLinearMap := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  exact fun f g => inner_zeroExtend_restrict μ A hA f g

theorem zeroExtend_adjoint (A : Set X) (hA : MeasurableSet A) :
    (zeroExtendLI μ A hA).toContinuousLinearMap.adjoint = restrictCLM μ A := by
  rw [← restrict_adjoint, ContinuousLinearMap.adjoint_adjoint]

end
end MeasureEquivalenceL2Restriction

#print axioms MeasureEquivalenceL2Restriction.restrictCLM
#print axioms MeasureEquivalenceL2Restriction.zeroExtendLI
#print axioms MeasureEquivalenceL2Restriction.restrict_zeroExtend
#print axioms MeasureEquivalenceL2Restriction.zeroExtend_restrict
#print axioms MeasureEquivalenceL2Restriction.zeroExtend_adjoint
