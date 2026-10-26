import ErgodicEquidecomposition
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Function.L2Space

/-! Countable equidecompositions give actual measure-preserving maps
with almost-everywhere inverses, and therefore genuine complex L2 unitaries. -/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace MeasureEquivalenceEquidecomposition

variable {X : Type*} [MeasurableSpace X]

theorem restrict_eq_sum_of_disjoint_cover (μ : Measure X) (A : Set X)
    (C : ℕ → Set X) (hCm : ∀ n, MeasurableSet (C n))
    (hCsub : ∀ n, C n ⊆ A)
    (hCdis : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hcover : μ (A \ ⋃ n, C n) = 0) :
    μ.restrict A = Measure.sum (fun n => μ.restrict (C n)) := by
  have hAE : A =ᵐ[μ] ⋃ n, C n := by
    rw [measure_eq_zero_iff_ae_notMem] at hcover
    filter_upwards [hcover] with x hx
    apply propext
    constructor
    · intro hxA
      by_contra hn
      exact hx ⟨hxA, hn⟩
    · intro hxC
      obtain ⟨n, hn⟩ := mem_iUnion.mp hxC
      exact hCsub n hn
  rw [Measure.restrict_congr_set hAE]
  exact Measure.restrict_iUnion hCdis hCm

/-- Construct piecewise forward and inverse transports from the actual
measurable pieces and measure-preserving local measurable equivalences. -/
theorem exists_piecewise_measure_transport
    (μ : Measure X) (A B : Set X) (C T : ℕ → Set X)
    (hCm : ∀ n, MeasurableSet (C n)) (hTm : ∀ n, MeasurableSet (T n))
    (hCsub : ∀ n, C n ⊆ A) (hTsub : ∀ n, T n ⊆ B)
    (hCdis : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hTdis : Pairwise (fun i j => Disjoint (T i) (T j)))
    (hcoverA : μ (A \ ⋃ n, C n) = 0) (hcoverB : μ (B \ ⋃ n, T n) = 0)
    (e : ℕ → X ≃ᵐ X) (he : ∀ n, MeasurePreserving (e n) μ μ)
    (himage : ∀ n, (e n) '' C n = T n) :
    ∃ F H : X → X,
      MeasurePreserving F (μ.restrict A) (μ.restrict B) ∧
      MeasurePreserving H (μ.restrict B) (μ.restrict A) ∧
      (∀ n, EqOn F (e n) (C n)) ∧ (∀ n, EqOn H (e n).symm (T n)) ∧
      (∀ᵐ x ∂μ.restrict A, H (F x) = x) ∧
      (∀ᵐ x ∂μ.restrict B, F (H x) = x) := by
  have hFagree : Pairwise (fun i j => EqOn (e i) (e j) (C i ∩ C j)) := by
    intro i j hij x hx
    exact (Set.disjoint_left.mp (hCdis hij) hx.1 hx.2).elim
  have hHagree : Pairwise (fun i j => EqOn (e i).symm (e j).symm (T i ∩ T j)) := by
    intro i j hij x hx
    exact (Set.disjoint_left.mp (hTdis hij) hx.1 hx.2).elim
  obtain ⟨F, hFm, hF⟩ := exists_measurable_piecewise C hCm
    (fun n => e n) (fun n => (e n).measurable) hFagree
  obtain ⟨H, hHm, hH⟩ := exists_measurable_piecewise T hTm
    (fun n => (e n).symm) (fun n => (e n).symm.measurable) hHagree
  have hsumA := restrict_eq_sum_of_disjoint_cover μ A C hCm hCsub hCdis hcoverA
  have hsumB := restrict_eq_sum_of_disjoint_cover μ B T hTm hTsub hTdis hcoverB
  have hmapF (n : ℕ) : (μ.restrict (C n)).map F = μ.restrict (T n) := by
    have hFeq : F =ᵐ[μ.restrict (C n)] e n := by
      filter_upwards [ae_restrict_mem (hCm n)] with x hx using hF n hx
    rw [Measure.map_congr hFeq, ← himage]
    exact ((he n).restrict_image_emb (e n).measurableEmbedding (C n)).map_eq
  have hmapH (n : ℕ) : (μ.restrict (T n)).map H = μ.restrict (C n) := by
    have hHeq : H =ᵐ[μ.restrict (T n)] (e n).symm := by
      filter_upwards [ae_restrict_mem (hTm n)] with x hx using hH n hx
    rw [Measure.map_congr hHeq]
    have hsymimage : (e n).symm '' T n = C n := by
      rw [← himage]
      exact (e n).symm_image_image (C n)
    rw [← hsymimage]
    exact ((he n).symm.restrict_image_emb (e n).symm.measurableEmbedding (T n)).map_eq
  have hFMP : MeasurePreserving F (μ.restrict A) (μ.restrict B) := by
    refine ⟨hFm, ?_⟩
    rw [hsumA, Measure.map_sum hFm.aemeasurable]
    simp_rw [hmapF]
    exact hsumB.symm
  have hHMP : MeasurePreserving H (μ.restrict B) (μ.restrict A) := by
    refine ⟨hHm, ?_⟩
    rw [hsumB, Measure.map_sum hHm.aemeasurable]
    simp_rw [hmapH]
    exact hsumA.symm
  refine ⟨F, H, hFMP, hHMP, hF, hH, ?_, ?_⟩
  · rw [hsumA, Measure.ae_sum_iff]
    intro n
    filter_upwards [ae_restrict_mem (hCm n)] with x hx
    have hext : e n x ∈ T n := by rw [← himage]; exact mem_image_of_mem _ hx
    rw [hF n hx, hH n hext]
    exact (e n).symm_apply_apply x
  · rw [hsumB, Measure.ae_sum_iff]
    intro n
    filter_upwards [ae_restrict_mem (hTm n)] with x hx
    have hext : (e n).symm x ∈ C n := by
      rw [← himage] at hx
      obtain ⟨z, hz, hez⟩ := hx
      simpa only [← hez, MeasurableEquiv.symm_apply_apply] using hz
    rw [hH n hx, hF n hext]
    exact (e n).apply_symm_apply x

section L2

variable {Y : Type*} [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (F : X → Y) (H : Y → X)
    (hF : MeasurePreserving F μ ν) (hH : MeasurePreserving H ν μ)
    (hHF : ∀ᵐ x ∂μ, H (F x) = x) (hFH : ∀ᵐ y ∂ν, F (H y) = y)

include hHF in
theorem pullback_inverse (u : Lp ℂ 2 μ) :
    Lp.compMeasurePreserving F hF (Lp.compMeasurePreserving H hH u) = u := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreserving H hH u) hF,
    hF.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving u hH), hHF]
    with x hx hu hxi
  simpa only [Function.comp_apply, hxi] using hx.trans hu

/-- Composition with actual inverse measure-preserving maps gives the
genuine complex L2 linear isometry equivalence used for induced modules. -/
noncomputable def pullbackUnitary : Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℂ F hF) (by
    intro u
    exact ⟨Lp.compMeasurePreserving H hH u, pullback_inverse μ ν F H hF hH hHF u⟩)

end L2

end MeasureEquivalenceEquidecomposition

#print axioms MeasureEquivalenceEquidecomposition.exists_piecewise_measure_transport
#print axioms MeasureEquivalenceEquidecomposition.pullbackUnitary
