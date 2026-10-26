import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

open MeasureTheory Filter

namespace MeasureEquivalenceHellinger

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Squared Hellinger energy calculated with a specified reference measure. -/
noncomputable def energy (μ ν ρ : Measure α) : ℝ :=
  ∫ x, (Real.sqrt (μ.rnDeriv ρ x).toReal -
    Real.sqrt (ν.rnDeriv ρ x).toReal) ^ 2 ∂ρ

theorem energy_symm (μ ν ρ : Measure α) : energy μ ν ρ = energy ν μ ρ := by
  unfold energy
  congr 1
  funext x
  ring

theorem energy_map (e : α ≃ᵐ β) (μ ν ρ : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ] :
    energy (μ.map e) (ν.map e) (ρ.map e) = energy μ ν ρ := by
  unfold energy
  rw [integral_map_equiv]
  apply integral_congr_ae
  filter_upwards [e.measurableEmbedding.rnDeriv_map μ ρ,
    e.measurableEmbedding.rnDeriv_map ν ρ] with x hμ hν
  rw [hμ, hν]

theorem energy_change_reference (μ ν ρ σ : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ] [SigmaFinite σ]
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ) (hρ : ρ ≪ σ) :
    energy μ ν σ = energy μ ν ρ := by
  unfold energy
  rw [← integral_toReal_rnDeriv_mul hρ]
  apply integral_congr_ae
  filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := σ) hμ,
    Measure.rnDeriv_mul_rnDeriv (κ := σ) hν] with x hmx hnx
  simp only [Pi.mul_apply] at hmx hnx
  rw [← hmx, ← hnx, ENNReal.toReal_mul, ENNReal.toReal_mul,
    Real.sqrt_mul (ENNReal.toReal_nonneg),
    Real.sqrt_mul (ENNReal.toReal_nonneg)]
  nlinarith [Real.sq_sqrt (ENNReal.toReal_nonneg : 0 ≤ (ρ.rnDeriv σ x).toReal)]

theorem energy_fixed_reference_map (e : α ≃ᵐ α) (μ ν ρ : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ]
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ) (hρ : ρ.map e ≪ ρ) :
    energy (μ.map e) (ν.map e) ρ = energy μ ν ρ := by
  let : SigmaFinite (μ.map e) := e.measurableEmbedding.sigmaFinite_map
  let : SigmaFinite (ν.map e) := e.measurableEmbedding.sigmaFinite_map
  let : SigmaFinite (ρ.map e) := e.measurableEmbedding.sigmaFinite_map
  rw [energy_change_reference (μ.map e) (ν.map e) (ρ.map e) ρ
    (e.measurableEmbedding.absolutelyContinuous_map hμ)
    (e.measurableEmbedding.absolutelyContinuous_map hν) hρ]
  exact energy_map e μ ν ρ

theorem energy_reference_independent (μ ν ρ σ : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    (hμρ : μ ≪ ρ) (hνρ : ν ≪ ρ) (hμσ : μ ≪ σ) (hνσ : ν ≪ σ) :
    energy μ ν ρ = energy μ ν σ := by
  calc
    energy μ ν ρ = energy μ ν (ρ + σ) :=
      (energy_change_reference μ ν ρ (ρ + σ) hμρ hνρ
        (Measure.AbsolutelyContinuous.rfl.add_right σ)).symm
    _ = energy μ ν σ := energy_change_reference μ ν σ (ρ + σ) hμσ hνσ
      (Measure.AbsolutelyContinuous.rfl.add_right' ρ)

theorem sqrt_rnDeriv_memLp (μ ρ : Measure α) [IsFiniteMeasure μ] :
    MemLp (fun x ↦ Real.sqrt (μ.rnDeriv ρ x).toReal) 2 ρ := by
  apply (memLp_two_iff_integrable_sq
    ((Measure.measurable_rnDeriv μ ρ).ennreal_toReal.sqrt.aestronglyMeasurable)).2
  have hi := Measure.integrableOn_toReal_rnDeriv (ν := ρ) (measure_ne_top μ Set.univ)
  simpa only [IntegrableOn, Measure.restrict_univ, Real.sq_sqrt ENNReal.toReal_nonneg]
    using hi

/-- The actual L² class of the nonnegative square root of a finite measure's RN density. -/
noncomputable def root (μ ρ : Measure α) [IsFiniteMeasure μ] : Lp ℝ 2 ρ :=
  (sqrt_rnDeriv_memLp μ ρ).toLp (fun x ↦ Real.sqrt (μ.rnDeriv ρ x).toReal)

theorem root_coe (μ ρ : Measure α) [IsFiniteMeasure μ] :
    root μ ρ =ᵐ[ρ] fun x ↦ Real.sqrt (μ.rnDeriv ρ x).toReal :=
  (sqrt_rnDeriv_memLp μ ρ).coeFn_toLp

theorem root_dist_sq (μ ν ρ : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    dist (root μ ρ) (root ν ρ) ^ 2 = energy μ ν ρ := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, L2.inner_def]
  unfold energy
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (root μ ρ) (root ν ρ), root_coe μ ρ,
    root_coe ν ρ] with x hs hμ hν
  simp only [Pi.sub_apply] at hs
  rw [hs, hμ, hν]
  simp [sq]

theorem root_dist_map (e : α ≃ᵐ α) (μ ν ρ : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [SigmaFinite ρ]
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ) (hρ : ρ.map e ≪ ρ) :
    dist (root (μ.map e) ρ) (root (ν.map e) ρ) = dist (root μ ρ) (root ν ρ) := by
  have he := energy_fixed_reference_map e μ ν ρ hμ hν hρ
  rw [← root_dist_sq, ← root_dist_sq] at he
  nlinarith [dist_nonneg (x := root (μ.map e) ρ) (y := root (ν.map e) ρ),
    dist_nonneg (x := root μ ρ) (y := root ν ρ)]

theorem root_nonnegative (μ ρ : Measure α) [IsFiniteMeasure μ] :
    0 ≤ root μ ρ := by
  apply (Lp.coeFn_nonneg _).1
  filter_upwards [root_coe μ ρ] with x hx
  rw [hx]
  exact Real.sqrt_nonneg _

theorem root_norm_sq (μ ρ : Measure α) [IsFiniteMeasure μ] [SigmaFinite ρ]
    (hμ : μ ≪ ρ) : ‖root μ ρ‖ ^ 2 = μ.real Set.univ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def,
    ← Measure.integral_toReal_rnDeriv hμ]
  apply integral_congr_ae
  filter_upwards [root_coe μ ρ] with x hx
  rw [hx]
  simp [Real.sq_sqrt ENNReal.toReal_nonneg]

theorem root_probability_norm (μ ρ : Measure α) [IsProbabilityMeasure μ] [SigmaFinite ρ]
    (hμ : μ ≪ ρ) : ‖root μ ρ‖ = 1 := by
  have h := root_norm_sq μ ρ hμ
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one] at h
  nlinarith [norm_nonneg (root μ ρ)]

/-- Inversion preserves the actual L² density distance for two commuting
quasi-invariant measurable bijections. No Hellinger-invariance hypothesis is used. -/
theorem root_dist_inverse (e f : α ≃ᵐ α) (ρ : Measure α) [IsFiniteMeasure ρ]
    (hcomm : Function.Commute e f)
    (he : ρ.map e ≪ ρ) (hf : ρ.map f ≪ ρ)
    (hei : ρ.map e.symm ≪ ρ) (hfi : ρ.map f.symm ≪ ρ) :
    dist (root (ρ.map e.symm) ρ) (root (ρ.map f.symm) ρ) =
      dist (root (ρ.map e) ρ) (root (ρ.map f) ρ) := by
  have ht : ρ.map (e.trans f) ≪ ρ := by
    have ht' := (f.measurableEmbedding.absolutelyContinuous_map he).trans hf
    simpa only [Measure.map_map f.measurable e.measurable,
      MeasurableEquiv.coe_trans] using ht'
  have hmap1 : (ρ.map e.symm).map (e.trans f) = ρ.map f := by
    rw [Measure.map_map (e.trans f).measurable e.symm.measurable]
    congr 1
    funext x
    simp
  have hmap2 : (ρ.map f.symm).map (e.trans f) = ρ.map e := by
    rw [Measure.map_map (e.trans f).measurable f.symm.measurable]
    congr 1
    funext x
    change f (e (f.symm x)) = e x
    rw [← hcomm (f.symm x), f.apply_symm_apply]
  have hd := root_dist_map (e.trans f) (ρ.map e.symm) (ρ.map f.symm) ρ hei hfi ht
  simp only [hmap1, hmap2] at hd
  exact hd.symm.trans (dist_comm _ _)

end MeasureEquivalenceHellinger

#print axioms MeasureEquivalenceHellinger.energy_map
#print axioms MeasureEquivalenceHellinger.energy_change_reference
#print axioms MeasureEquivalenceHellinger.energy_fixed_reference_map
#print axioms MeasureEquivalenceHellinger.energy_reference_independent
#print axioms MeasureEquivalenceHellinger.sqrt_rnDeriv_memLp
#print axioms MeasureEquivalenceHellinger.root_dist_sq
#print axioms MeasureEquivalenceHellinger.root_dist_map
#print axioms MeasureEquivalenceHellinger.root_nonnegative
#print axioms MeasureEquivalenceHellinger.root_norm_sq
#print axioms MeasureEquivalenceHellinger.root_probability_norm
#print axioms MeasureEquivalenceHellinger.root_dist_inverse
