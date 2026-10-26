import MeasureContinuousMultipliers

/-! Multiplication by pulled-back continuous functions on arbitrary
measurable measure spaces. No finiteness or topology on the source measure
space is required. -/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureUnitary

noncomputable section

variable {Ω K : Type*} [MeasurableSpace Ω] [TopologicalSpace K] [MeasurableSpace K]
  [BorelSpace K] [CompactSpace K] [SecondCountableTopology K]
  (μ : Measure Ω) (q : Ω → K) (hq : Measurable q)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

include hq

theorem pullbackContinuous_memLp_top (g : C(K, ℂ)) : MemLp (fun x => g (q x)) ∞ μ :=
  memLp_top_of_bound (g.continuous.measurable.comp hq).aestronglyMeasurable ‖g‖
    (.of_forall (fun x => g.norm_coe_le_norm (q x)))

def pullbackContinuousSymbol (g : C(K, ℂ)) : Lp ℂ ∞ μ :=
  (pullbackContinuous_memLp_top μ q hq g).toLp (fun x => g (q x))

theorem pullbackContinuousSymbol_coe (g : C(K, ℂ)) :
    pullbackContinuousSymbol μ q hq g =ᵐ[μ] fun x => g (q x) :=
  (pullbackContinuous_memLp_top μ q hq g).coeFn_toLp

theorem pullbackContinuousSymbol_norm_le (g : C(K, ℂ)) :
    ‖pullbackContinuousSymbol μ q hq g‖ ≤ ‖g‖ := by
  rw [pullbackContinuousSymbol, Lp.norm_toLp]
  apply ENNReal.toReal_le_of_le_ofReal (norm_nonneg g)
  exact eLpNormEssSup_le_of_ae_bound (.of_forall (fun x => g.norm_coe_le_norm (q x)))

def pullbackContinuousSymbolCLM : C(K, ℂ) →L[ℂ] Lp ℂ ∞ μ := by
  let L : C(K, ℂ) →ₗ[ℂ] Lp ℂ ∞ μ := {
    toFun := pullbackContinuousSymbol μ q hq
    map_add' := by
      intro g h
      apply Lp.ext
      filter_upwards [pullbackContinuousSymbol_coe μ q hq (g + h),
        pullbackContinuousSymbol_coe μ q hq g, pullbackContinuousSymbol_coe μ q hq h,
        Lp.coeFn_add (pullbackContinuousSymbol μ q hq g) (pullbackContinuousSymbol μ q hq h)]
        with x hgh hg hh ha
      simp only [Pi.add_apply] at ha
      rw [hgh, ha, hg, hh]
      rfl
    map_smul' := by
      intro c g
      apply Lp.ext
      filter_upwards [pullbackContinuousSymbol_coe μ q hq (c • g), pullbackContinuousSymbol_coe μ q hq g,
        Lp.coeFn_smul c (pullbackContinuousSymbol μ q hq g)] with x hcg hg hs
      simp only [RingHom.id_apply]
      simp only [Pi.smul_apply] at hs
      rw [hcg, hs, hg]
      rfl }
  exact L.mkContinuous 1 (fun g => by simpa using pullbackContinuousSymbol_norm_le μ q hq g)

def pullbackMultiplierL2 : C(K, ℂ) →L[ℂ] (Lp E 2 μ →L[ℂ] Lp E 2 μ) :=
  ((ContinuousLinearMap.lsmul ℂ ℂ (E := E)).holderL μ ∞ 2 2).comp
    (pullbackContinuousSymbolCLM μ q hq)

theorem pullbackMultiplierL2_coe (g : C(K, ℂ)) (f : Lp E 2 μ) :
    pullbackMultiplierL2 μ q hq g f =ᵐ[μ] fun x => g (q x) • f x := by
  have hh := (ContinuousLinearMap.lsmul ℂ ℂ (E := E)).coeFn_holder (r := 2)
    (pullbackContinuousSymbol μ q hq g) f
  filter_upwards [hh, pullbackContinuousSymbol_coe μ q hq g] with x hh hg
  exact hh.trans (by rw [hg]; rfl)

theorem pullbackMultiplierL2_one : pullbackMultiplierL2 (E := E) μ q hq (1 : C(K, ℂ)) = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [pullbackMultiplierL2_coe μ q hq (1 : C(K, ℂ)) f] with x hx
  simpa using hx

theorem pullbackMultiplierL2_mul (g h : C(K, ℂ)) :
    pullbackMultiplierL2 (E := E) μ q hq (g * h) =
      pullbackMultiplierL2 μ q hq g * pullbackMultiplierL2 μ q hq h := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [pullbackMultiplierL2_coe μ q hq (g * h) f,
    pullbackMultiplierL2_coe μ q hq g (pullbackMultiplierL2 μ q hq h f),
    pullbackMultiplierL2_coe μ q hq h f] with x hgh hg hh
  change (pullbackMultiplierL2 μ q hq (g * h) f) x =
    (pullbackMultiplierL2 μ q hq g (pullbackMultiplierL2 μ q hq h f)) x
  rw [hgh, hg, hh]
  exact mul_smul _ _ _

theorem pullbackMultiplierL2_algebraMap (c : ℂ) :
    pullbackMultiplierL2 (E := E) μ q hq (algebraMap ℂ C(K, ℂ) c) =
      algebraMap ℂ (Lp E 2 μ →L[ℂ] Lp E 2 μ) c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, pullbackMultiplierL2_one,
    Algebra.algebraMap_eq_smul_one]

theorem pullbackMultiplierL2_star (g : C(K, ℂ)) :
    pullbackMultiplierL2 (E := E) μ q hq (star g) = star (pullbackMultiplierL2 (E := E) μ q hq g) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f h
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [pullbackMultiplierL2_coe μ q hq (star g) f,
    pullbackMultiplierL2_coe μ q hq g h] with x hf hh
  rw [hf, hh]
  simp only [ContinuousMap.star_apply, inner_smul_left, inner_smul_right, starRingEnd_apply, star_star]

def pullbackMultiplierStarAlgHom : C(K, ℂ) →⋆ₐ[ℂ] (Lp E 2 μ →L[ℂ] Lp E 2 μ) where
  toFun := pullbackMultiplierL2 μ q hq
  map_zero' := map_zero _
  map_one' := pullbackMultiplierL2_one μ q hq
  map_add' := map_add _
  map_mul' := pullbackMultiplierL2_mul μ q hq
  commutes' := pullbackMultiplierL2_algebraMap μ q hq
  map_star' := pullbackMultiplierL2_star μ q hq

end

end MeasureUnitary

#print axioms MeasureUnitary.pullbackMultiplierStarAlgHom
