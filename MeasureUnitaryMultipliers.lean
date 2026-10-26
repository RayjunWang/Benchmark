import MeasureUnitaryRN

/-! Genuine multiplication unitaries in complex L², and their natural
intertwining by the square-root Radon–Nikodym unitary. -/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureUnitary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
  (c : α → ℂ) (hc : Measurable c) (hnorm : ∀ x, ‖c x‖ = 1)

include hc hnorm

theorem phase_memLp (f : Lp E 2 μ) : MemLp (fun x => c x • f x) 2 μ := by
  apply (Lp.memLp f).congr_norm (hc.aestronglyMeasurable.smul (Lp.aestronglyMeasurable f))
  exact .of_forall (fun x => by
    change ‖f x‖ = ‖c x • f x‖
    rw [norm_smul, hnorm x, one_mul])

noncomputable def phaseMap (f : Lp E 2 μ) : Lp E 2 μ :=
  (phase_memLp μ c hc hnorm f).toLp (fun x => c x • f x)

theorem phaseMap_coe (f : Lp E 2 μ) : phaseMap μ c hc hnorm f =ᵐ[μ] fun x => c x • f x :=
  (phase_memLp μ c hc hnorm f).coeFn_toLp

noncomputable def phaseLI : Lp E 2 μ →ₗᵢ[ℂ] Lp E 2 μ where
  toFun := phaseMap μ c hc hnorm
  map_add' := by
    intro f g
    apply Lp.ext
    filter_upwards [phaseMap_coe μ c hc hnorm (f + g), phaseMap_coe μ c hc hnorm f,
      phaseMap_coe μ c hc hnorm g,
      Lp.coeFn_add (phaseMap μ c hc hnorm f) (phaseMap μ c hc hnorm g), Lp.coeFn_add f g]
      with x hfg hf hg hadd hsource
    simp only [Pi.add_apply] at hadd hsource
    rw [hfg, hadd, hf, hg, hsource, smul_add]
  map_smul' := by
    intro a f
    apply Lp.ext
    filter_upwards [phaseMap_coe μ c hc hnorm (a • f), phaseMap_coe μ c hc hnorm f,
      Lp.coeFn_smul a (phaseMap μ c hc hnorm f), Lp.coeFn_smul a f]
      with x haf hf hsmul hsource
    simp only [Pi.smul_apply] at hsmul hsource
    simp only [RingHom.id_apply]
    rw [haf, hsmul, hf, hsource]
    exact smul_comm _ _ _
  norm_map' := by
    intro f
    change ‖phaseMap μ c hc hnorm f‖ = ‖f‖
    rw [phaseMap, Lp.norm_toLp, Lp.norm_def]
    congr 1
    exact eLpNorm_congr_norm_ae (.of_forall (fun x => by simp only [norm_smul, hnorm x, one_mul]))

omit hc in
theorem inversePhase_norm (x : α) : ‖(c x)⁻¹‖ = 1 := by rw [norm_inv, hnorm x, inv_one]

theorem phaseMap_inverse (f : Lp E 2 μ) :
    phaseMap μ c hc hnorm
      (phaseMap μ (fun x => (c x)⁻¹) hc.inv (inversePhase_norm c hnorm) f) = f := by
  apply Lp.ext
  filter_upwards [phaseMap_coe μ c hc hnorm
    (phaseMap μ (fun x => (c x)⁻¹) hc.inv (inversePhase_norm c hnorm) f),
    phaseMap_coe μ (fun x => (c x)⁻¹) hc.inv (inversePhase_norm c hnorm) f] with x houter hinner
  have hne : c x ≠ 0 := by
    intro hz
    have := hnorm x
    simp [hz] at this
  rw [houter, hinner, smul_smul, mul_inv_cancel₀ hne, one_smul]

noncomputable def phaseEquiv : Lp E 2 μ ≃ₗᵢ[ℂ] Lp E 2 μ :=
  LinearIsometryEquiv.ofSurjective (phaseLI μ c hc hnorm) (by
    intro f
    exact ⟨phaseMap μ (fun x => (c x)⁻¹) hc.inv (inversePhase_norm c hnorm) f,
      phaseMap_inverse μ c hc hnorm f⟩)

variable (ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]

theorem rnWeightedEquiv_intertwines_phase (hμν : μ ≪ ν) (hνμ : ν ≪ μ) (f : Lp E 2 μ) :
    rnWeightedEquiv μ ν hμν hνμ (phaseEquiv μ c hc hnorm f) =
      phaseEquiv ν c hc hnorm (rnWeightedEquiv μ ν hμν hνμ f) := by
  change rnWeightedMap μ ν hμν hνμ (phaseMap μ c hc hnorm f) =
    phaseMap ν c hc hnorm (rnWeightedMap μ ν hμν hνμ f)
  apply Lp.ext
  filter_upwards [rnWeightedMap_coe μ ν hμν hνμ (phaseMap μ c hc hnorm f),
    hνμ.ae_eq (phaseMap_coe μ c hc hnorm f),
    phaseMap_coe ν c hc hnorm (rnWeightedMap μ ν hμν hνμ f),
    rnWeightedMap_coe μ ν hμν hνμ f] with x hleft hphase hright hRN
  rw [hleft, hphase, hright, hRN]
  change rnWeight μ ν x • (c x • f x) = c x • (rnWeight μ ν x • f x)
  exact smul_comm _ _ _

end MeasureUnitary

#print axioms MeasureUnitary.phaseEquiv
#print axioms MeasureUnitary.rnWeightedEquiv_intertwines_phase

