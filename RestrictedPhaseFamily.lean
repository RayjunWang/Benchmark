import RestrictedErgodic
import SolenoidGroups
import MeasureUnitaryMultipliers
import OperatorStrongUnitary
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Measure.Count

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid MeasureUnitary

abbrev CharacterIndex := ℕ × ℚ
instance : MeasurableSpace rationalZeroSumGroup := ⊤
instance : MeasurableSingletonClass rationalZeroSumGroup := ⟨fun _ => trivial⟩
abbrev Sample := RealSequences × rationalZeroSumGroup

def sampleMeasure : Measure Sample := tailProbability.prod Measure.count
abbrev CornerHilbert := Lp ℂ 2 sampleMeasure

def character (i : CharacterIndex) (k : CompactSequences) : ℂ :=
  (AddCircle.toCircle ((k i.1 : ℚ → UnitAddCircle) i.2) : ℂ)

theorem character_continuous (i : CharacterIndex) : Continuous (character i) := by
  exact continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp
    ((continuous_apply i.2).comp (continuous_subtype_val.comp (continuous_apply i.1))))

@[simp] theorem character_norm (i : CharacterIndex) (k : CompactSequences) :
    ‖character i k‖ = 1 := Circle.norm_coe _

@[simp] theorem character_zero (i : CharacterIndex) : character i 0 = 1 := by
  simp [character]

theorem character_add (i : CharacterIndex) (k l : CompactSequences) :
    character i (k + l) = character i k * character i l := by
  exact congrArg (fun z : Circle => (z : ℂ)) (AddCircle.toCircle_add _ _)

def sampleOrbit (p : Sample) : RealSequences := p.1 + rationalRealShift p.2

theorem sampleOrbit_measurable : Measurable sampleOrbit := by
  apply measurable_pi_lambda
  intro n
  exact ((measurable_pi_apply n).comp measurable_fst).add
    ((measurable_of_countable (fun q : rationalZeroSumGroup => rationalRealShift q n)).comp
      measurable_snd)

def samplePhase (k : CompactSequences) (i : CharacterIndex) (p : Sample) : ℂ :=
  character i (k + sequenceEmbedding (sampleOrbit p))

theorem samplePhase_measurable (k : CompactSequences) (i : CharacterIndex) :
    Measurable (samplePhase k i) := by
  exact (character_continuous i).measurable.comp
    (measurable_const.add (sequenceEmbedding_continuous.measurable.comp sampleOrbit_measurable))

theorem samplePhase_norm (k : CompactSequences) (i : CharacterIndex) (p : Sample) :
    ‖samplePhase k i p‖ = 1 := character_norm _ _

theorem samplePhase_factor (k : CompactSequences) (i : CharacterIndex) (p : Sample) :
    samplePhase k i p = character i k * samplePhase 0 i p := by
  simp only [samplePhase, zero_add, character_add]

def phaseUnitary (k : CompactSequences) (i : CharacterIndex) :
    CornerHilbert ≃ₗᵢ[ℂ] CornerHilbert :=
  phaseEquiv sampleMeasure (samplePhase k i) (samplePhase_measurable k i) (samplePhase_norm k i)

theorem phaseUnitary_coe (k : CompactSequences) (i : CharacterIndex) (u : CornerHilbert) :
    phaseUnitary k i u =ᵐ[sampleMeasure] fun p => samplePhase k i p * u p :=
  phaseMap_coe sampleMeasure (samplePhase k i) (samplePhase_measurable k i) (samplePhase_norm k i) u

theorem phaseUnitary_factor (k : CompactSequences) (i : CharacterIndex) (u : CornerHilbert) :
    phaseUnitary k i u = character i k • phaseUnitary 0 i u := by
  apply Lp.ext
  filter_upwards [phaseUnitary_coe k i u, phaseUnitary_coe 0 i u,
    Lp.coeFn_smul (character i k) (phaseUnitary 0 i u)] with p hp hp0 hsmul
  rw [hp, hsmul]
  change samplePhase k i p * u p = character i k * (phaseUnitary 0 i u) p
  rw [hp0, samplePhase_factor, mul_assoc]

theorem phaseUnitary_continuous (i : CharacterIndex) :
    Continuous (fun k : CompactSequences => phaseUnitary k i) := by
  apply (OperatorCoding.strongUnitary_continuous_iff _).mpr
  intro u
  have he : (fun k : CompactSequences => phaseUnitary k i u) =
      (fun k : CompactSequences => character i k • phaseUnitary 0 i u) :=
    funext (fun k => phaseUnitary_factor k i u)
  rw [he]
  exact (character_continuous i).smul continuous_const

theorem phaseTuple_continuous :
    Continuous (fun k : CompactSequences => fun i : CharacterIndex => phaseUnitary k i) :=
  continuous_pi phaseUnitary_continuous

end MeasureEquivalenceRestrictedPhase

#print axioms MeasureEquivalenceRestrictedPhase.phaseUnitary_continuous
#print axioms MeasureEquivalenceRestrictedPhase.phaseTuple_continuous
