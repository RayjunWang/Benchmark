import UnitaryCFCStrongContinuity
import UnitaryVectorRieszMass
import UnitaryFullSpectralModel
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.GiryMonad

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal InnerProductSpace BoundedContinuousFunction

set_option maxHeartbeats 1500000

noncomputable section

namespace OperatorCoding

open MeasureUnitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] [SecondCountableTopology H]

local instance : MeasurableSpace H := borel _
local instance : BorelSpace H := ⟨rfl⟩
local instance : MeasurableSpace (StrongUnitary H) := borel _
local instance : BorelSpace (StrongUnitary H) := ⟨rfl⟩

theorem unitaryVectorSpectralMeasure_realTest_continuous (f : C(SpectralCircle, ℝ)) :
    Continuous (fun p : StrongUnitary H × H => ∫ x, f x ∂unitaryVectorSpectralMeasure p.1 p.2) := by
  let fc := realContinuousCompactSupport f
  have he := unitaryCircleRepresentation_joint_continuous (H := H) (complexifyCompactSupport fc)
  have hc : Continuous (fun p : StrongUnitary H × H =>
      (inner ℂ p.2 (unitaryCircleRepresentation p.1 (complexifyCompactSupport fc) p.2)).re) :=
    Complex.continuous_re.comp (continuous_snd.inner (𝕜 := ℂ) he)
  convert hc using 1
  funext p
  exact representationVectorMeasure_integral (unitaryCircleRepresentation p.1) p.2 fc

theorem unitaryVectorSpectralMeasure_nnTest_measurable (f : SpectralCircle →ᵇ ℝ≥0) :
    Measurable (fun p : StrongUnitary H × H =>
      ∫⁻ x, (f x : ℝ≥0∞) ∂unitaryVectorSpectralMeasure p.1 p.2) := by
  let g : C(SpectralCircle, ℝ) :=
    ⟨fun x => (f x : ℝ), NNReal.continuous_coe.comp f.continuous⟩
  have he : (fun p : StrongUnitary H × H =>
      ∫⁻ x, (f x : ℝ≥0∞) ∂unitaryVectorSpectralMeasure p.1 p.2) =
      (fun p => ENNReal.ofReal (∫ x, g x ∂unitaryVectorSpectralMeasure p.1 p.2)) := by
    funext p
    have hi : Integrable g (unitaryVectorSpectralMeasure p.1 p.2) :=
      g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    simpa only [g,ContinuousMap.coe_mk,ENNReal.ofReal_coe_nnreal] using
      (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall
        (fun x => NNReal.coe_nonneg (f x)))).symm
  rw [he]
  exact (unitaryVectorSpectralMeasure_realTest_continuous g).measurable.ennreal_ofReal

theorem unitaryVectorSpectralMeasure_closed_measurable (F : Set SpectralCircle) (hF : IsClosed F) :
    Measurable (fun p : StrongUnitary H × H => unitaryVectorSpectralMeasure p.1 p.2 F) := by
  have hlim : Tendsto (fun n (p : StrongUnitary H × H) =>
      ∫⁻ x, (hF.apprSeq n x : ℝ≥0∞) ∂unitaryVectorSpectralMeasure p.1 p.2) atTop
      (𝓝 (fun p => unitaryVectorSpectralMeasure p.1 p.2 F)) := by
    apply tendsto_pi_nhds.mpr
    intro p
    exact HasOuterApproxClosed.tendsto_lintegral_apprSeq hF (unitaryVectorSpectralMeasure p.1 p.2)
  exact measurable_of_tendsto_metrizable
    (fun n => unitaryVectorSpectralMeasure_nnTest_measurable (hF.apprSeq n)) hlim

theorem unitaryVectorSpectralMeasure_measurable :
    Measurable (fun p : StrongUnitary H × H => unitaryVectorSpectralMeasure p.1 p.2) := by
  have hgen : (inferInstance : MeasurableSpace SpectralCircle) =
      MeasurableSpace.generateFrom {s : Set SpectralCircle | IsClosed s} :=
    (BorelSpace.measurable_eq : (inferInstance : MeasurableSpace SpectralCircle) =
      borel SpectralCircle).trans borel_eq_generateFrom_isClosed
  apply Measurable.measure_of_isPiSystem (S := {s : Set SpectralCircle | IsClosed s})
  · exact hgen
  · exact isPiSystem_isClosed
  · intro F hF
    exact unitaryVectorSpectralMeasure_closed_measurable F hF
  · exact unitaryVectorSpectralMeasure_closed_measurable univ isClosed_univ

theorem greedySpectralMeasure_measurable (n : ℕ) :
    Measurable (fun U : StrongUnitary H => greedySpectralMeasure U n) := by
  change Measurable ((fun p : StrongUnitary H × H => unitaryVectorSpectralMeasure p.1 p.2) ∘
    (fun U : StrongUnitary H => (U,greedyCyclicGenerator U n)))
  exact (unitaryVectorSpectralMeasure_measurable (H := H)).comp
    (measurable_id.prodMk (greedyCyclicGenerator_measurable (H := H) n))

end OperatorCoding

#print axioms OperatorCoding.greedySpectralMeasure_measurable
