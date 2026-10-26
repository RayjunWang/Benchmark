import HellingerVariational
import HellingerKernel
import RestrictedRoots
import Mathlib.Probability.Kernel.Composition.Lemmas

/-! Upper semicontinuity of averaged component affinities, obtained by
applying the actual affinity theorem to an equal-marginal joint measure. -/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

noncomputable section

namespace MeasureEquivalenceHellinger

section Orbit

variable {K Z : Type*} [Group K] [TopologicalSpace K] [FirstCountableTopology K]
    [MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z]
    (M : Measure Z) [IsProbabilityMeasure M]

def probabilityOrbit (g : K) : ProbabilityMeasure Z :=
  ⟨M.map (fun z => g • z), M.isProbabilityMeasure_map (measurable_const_smul g).aemeasurable⟩

theorem probabilityOrbit_continuous : Continuous (probabilityOrbit (K := K) M) := by
  apply (ProbabilityMeasure.toFiniteMeasure_isEmbedding Z).continuous_iff.mpr
  exact MeasureEquivalenceRestrictedRoots.finiteOrbit_continuous M

end Orbit

abbrev rightCoordinateAction (K Y Z : Type*) [Monoid K] [MulAction K Z] :
    MulAction K (Y × Z) where
  smul g p := (p.1, g • p.2)
  one_smul p := by
    change (p.1, (1:K) • p.2) = p
    simp
  mul_smul g h p := by
    change (p.1, (g*h) • p.2) = (p.1, g • (h • p.2))
    rw [mul_smul]

theorem rightCoordinateAction_continuous (K Y Z : Type*)
    [Monoid K] [TopologicalSpace K] [TopologicalSpace Y] [TopologicalSpace Z]
    [MulAction K Z] [ContinuousSMul K Z] :
    letI := rightCoordinateAction K Y Z
    ContinuousSMul K (Y × Z) := by
  letI := rightCoordinateAction K Y Z
  constructor
  change Continuous (fun p : K × (Y × Z) => (p.2.1, p.1 • p.2.2))
  exact (continuous_fst.comp continuous_snd).prodMk
    (continuous_fst.smul (continuous_snd.comp continuous_snd))

section Averaged

variable {K Y Z : Type*} [Group K] [TopologicalSpace K] [FirstCountableTopology K]
    [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z]
    (η : Measure Y) [IsProbabilityMeasure η] (κ : Kernel Y Z) [IsMarkovKernel κ]

theorem upperSemicontinuous_integrated_affinity :
    UpperSemicontinuous (fun g : K =>
      ∫ y, affinity (κ y) ((κ y).map (fun z => g • z)) ∂η) := by
  letI := rightCoordinateAction K Y Z
  letI : ContinuousSMul K (Y × Z) := rightCoordinateAction_continuous K Y Z
  let J : Measure (Y × Z) := η ⊗ₘ κ
  letI : IsProbabilityMeasure J := inferInstance
  let P : ProbabilityMeasure (Y × Z) := ⟨J, inferInstance⟩
  have hc : Continuous (fun g : K => (P, probabilityOrbit J g)) :=
    continuous_const.prodMk (probabilityOrbit_continuous J)
  have hu := upperSemicontinuous_affinity_probability.comp hc
  have he (g : K) :
      affinity J (probabilityOrbit J g : Measure (Y × Z)) =
        ∫ y, affinity (κ y) ((κ y).map (fun z => g • z)) ∂η := by
    have hm : (probabilityOrbit J g : Measure (Y × Z)) =
        η ⊗ₘ κ.map (fun z => g • z) := by
      simpa only [probabilityOrbit, J, rightCoordinateAction, Prod.map_apply, id_eq] using
        (Measure.compProd_map (μ := η) (κ := κ) (measurable_const_smul g)).symm
    simp only [hm]
    exact (affinity_compProd η κ (κ.map (fun z => g • z))).trans
      (integral_congr_ae (Eventually.of_forall (fun y => by
        simp only [Kernel.map_apply _ (measurable_const_smul g)])))
  have hfun : (fun g : K => affinity J (probabilityOrbit J g : Measure (Y × Z))) =
      fun g : K => ∫ y, affinity (κ y) ((κ y).map (fun z => g • z)) ∂η := funext he
  change UpperSemicontinuous (fun g : K =>
    affinity J (probabilityOrbit J g : Measure (Y × Z))) at hu
  rw [hfun] at hu
  exact hu

end Averaged

section StandardBorelAverage

variable {K Y Z : Type*} [Group K] [TopologicalSpace K] [FirstCountableTopology K]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z]
    (η : Measure Y) [IsProbabilityMeasure η] (κ : Kernel Y Z) [IsMarkovKernel κ]

/-- The component parameter only needs a standard Borel structure. We
embed it measurably into Cantor space and extend the kernel by a measurable
retraction, so the joint-measure argument applies on a compact metric space. -/
theorem upperSemicontinuous_integrated_affinity_standardBorel :
    UpperSemicontinuous (fun g : K =>
      ∫ y, affinity (κ y) ((κ y).map (fun z => g • z)) ∂η) := by
  let C := ℕ → Bool
  letI : MetricSpace C := TopologicalSpace.metrizableSpaceMetric C
  let e : Y → C := MeasurableSpace.mapNatBool Y
  have he : MeasurableEmbedding e :=
    (MeasurableSpace.measurable_mapNatBool Y).measurableEmbedding
      (MeasurableSpace.injective_mapNatBool Y)
  let r : C → Y := he.invFun
  have hr : Measurable r := he.measurable_invFun
  have hre : ∀ y, r (e y) = y := he.leftInverse_invFun
  let ηC : Measure C := η.map e
  letI : IsProbabilityMeasure ηC := η.isProbabilityMeasure_map he.measurable.aemeasurable
  let κC : Kernel C Z := κ.comap r hr
  have huc := upperSemicontinuous_integrated_affinity (K := K) ηC κC
  have hEq (g : K) :
      (∫ c, affinity (κC c) ((κC c).map (fun z => g • z)) ∂ηC) =
        ∫ y, affinity (κ y) ((κ y).map (fun z => g • z)) ∂η := by
    change (∫ c, affinity (κC c) ((κC c).map (fun z => g • z)) ∂η.map e) = _
    rw [he.integral_map]
    apply integral_congr_ae
    exact Eventually.of_forall (fun y => by simp only [κC, Kernel.comap_apply, hre])
  have hf : (fun g : K => ∫ c, affinity (κC c) ((κC c).map (fun z => g • z)) ∂ηC) =
      fun g : K => ∫ y, affinity (κ y) ((κ y).map (fun z => g • z)) ∂η := funext hEq
  rw [hf] at huc
  exact huc

end StandardBorelAverage

end MeasureEquivalenceHellinger

#print axioms MeasureEquivalenceHellinger.probabilityOrbit_continuous
#print axioms MeasureEquivalenceHellinger.upperSemicontinuous_integrated_affinity
#print axioms MeasureEquivalenceHellinger.upperSemicontinuous_integrated_affinity_standardBorel
