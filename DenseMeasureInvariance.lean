import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.CompactOpen
import Mathlib.Tactic

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G] [T2Space G]

theorem map_add_eq_of_dense_invariant (μ : Measure G) [μ.Regular]
    (D : Set G) (hD : Dense D)
    (hinv : ∀ q ∈ D, μ.map (fun x => x + q) = μ) (h : G) :
    μ.map (fun x => x + h) = μ := by
  let A : C(G × G, G) := ⟨fun p => p.2 + p.1, continuous_snd.add continuous_fst⟩
  have hle (a : G) (U : Set G) (hU : IsOpen U) : μ ((fun x => x + a) ⁻¹' U) ≤ μ U := by
    rw [(hU.preimage (show Continuous (fun x : G => x + a) from by fun_prop)).measure_eq_iSup_isCompact μ]
    apply iSup_le
    intro K
    apply iSup_le
    intro hKU
    apply iSup_le
    intro hK
    have he : ∀ᶠ q in 𝓝 a, MapsTo (A.curry q) K U :=
      (A.curry.continuous.tendsto a).eventually (ContinuousMap.eventually_mapsTo hK hU hKU)
    obtain ⟨q, hqD, hqK⟩ := hD.inter_nhds_nonempty he
    calc
      μ K ≤ μ ((fun x : G => x + q) ⁻¹' U) := measure_mono hqK
      _ = μ U := by rw [← Measure.map_apply (by fun_prop) hU.measurableSet, hinv q hqD]
  letI : (μ.map (fun x => x + h)).Regular :=
    Measure.Regular.map (μ := μ) (Homeomorph.addRight h)
  apply Measure.OuterRegular.ext_isOpen
  intro U hU
  rw [Measure.map_apply (by fun_prop) hU.measurableSet]
  apply le_antisymm (hle h U hU)
  have he := hle (-h) ((fun x : G => x + h) ⁻¹' U)
    (hU.preimage (show Continuous (fun x : G => x + h) from by fun_prop))
  have hpre : (fun x : G => x + -h) ⁻¹' ((fun x : G => x + h) ⁻¹' U) = U := by
    ext x
    simp [add_assoc]
  rw [hpre] at he
  exact he

end MeasureEquivalenceRestrictedProduct

#print axioms MeasureEquivalenceRestrictedProduct.map_add_eq_of_dense_invariant
