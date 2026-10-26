import CantorHaarCylinders

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace BenchmarkJump

theorem splitHaar_coe {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (A B : Set α)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    splitHaar μ A B hA hB =ᵐ[μ] fun x =>
      (μ.real B * A.indicator (fun _ => (1 : ℝ)) x -
        μ.real A * B.indicator (fun _ => (1 : ℝ)) x) /
        Real.sqrt (μ.real A * μ.real B * (μ.real A + μ.real B)) := by
  let f : Lp ℝ 2 μ := indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ)
  let g : Lp ℝ 2 μ := indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ)
  let d := Real.sqrt (μ.real A * μ.real B * (μ.real A + μ.real B))
  filter_upwards [Lp.coeFn_smul d⁻¹ (μ.real B • f - μ.real A • g),
    Lp.coeFn_sub (μ.real B • f) (μ.real A • g), Lp.coeFn_smul (μ.real B) f,
    Lp.coeFn_smul (μ.real A) g,
    indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := measure_ne_top μ A) (c := (1 : ℝ)),
    indicatorConstLp_coeFn (p := 2) (hs := hB) (hμs := measure_ne_top μ B) (c := (1 : ℝ))]
    with x hscale hsub hsmulf hsmulg hf hg
  change (d⁻¹ • (μ.real B • f - μ.real A • g)) x = _
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hscale hsub hsmulf hsmulg
  rw [hscale, hsub, hsmulf, hsmulg]
  change f x = A.indicator (fun _ => (1 : ℝ)) x at hf
  change g x = B.indicator (fun _ => (1 : ℝ)) x at hg
  rw [hf, hg]
  change d⁻¹ * (μ.real B * A.indicator (fun _ => (1 : ℝ)) x -
    μ.real A * B.indicator (fun _ => (1 : ℝ)) x) = _
  rw [div_eq_mul_inv, mul_comm]

def cantorHaarFunction (μ : PositiveCylinderProbabilities) (i : HaarNodeIndex) (x : HaarCantor) : ℝ :=
  haarNodeFunction (prefixCylinder (Fin.snoc i.2 false))
    (prefixCylinder (Fin.snoc i.2 true)) μ x

theorem cantorHaarNode_coe (μ : PositiveCylinderProbabilities) (i : HaarNodeIndex) :
    cantorHaarNode μ i =ᵐ[((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)]
      cantorHaarFunction μ i :=
  splitHaar_coe _ _ _ _ _

/-- Each actual Haar basis function has jointly continuous finite-cylinder
coefficients as the full-support measure varies weakly. -/
theorem continuous_cantorHaarFunction (i : HaarNodeIndex) :
    Continuous (fun p : PositiveCylinderProbabilities × HaarCantor =>
      cantorHaarFunction p.1 i p.2) := by
  let A := prefixCylinder (Fin.snoc i.2 false)
  let B := prefixCylinder (Fin.snoc i.2 true)
  let map : PositiveCylinderProbabilities → PositiveSplitProbabilities A B :=
    fun μ => ⟨μ, μ.property (i.1 + 1) (Fin.snoc i.2 false),
      μ.property (i.1 + 1) (Fin.snoc i.2 true)⟩
  have hc : Continuous map := continuous_subtype_val.subtype_mk _
  exact (continuous_haarNodeFunction A B (isClopen_prefixCylinder _) (isClopen_prefixCylinder _)).comp
    ((hc.comp continuous_fst).prodMk continuous_snd)

#print axioms cantorHaarNode_coe
#print axioms continuous_cantorHaarFunction

end BenchmarkJump
