import PiecewiseMeasureTransport
import MeasureUnitaryMultipliers
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Prod

/-! Genuine finite-corner induced-module transports on the product of
the base sample space and the counting-measure group coordinate. -/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace MeasureEquivalenceInducedCorners

noncomputable section

open MeasureEquivalenceEquidecomposition

variable {G Z : Type*} [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    [MeasurableSpace Z] [MulAction G Z] [MeasurableConstSMul G Z]

def indexRight (g : G) : G ≃ᵐ G where
  toEquiv := Equiv.mulRight g
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

def indexLeft (g : G) : G ≃ᵐ G where
  toEquiv := Equiv.mulLeft g
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

omit [Group G] [Countable G] in
theorem count_preserving (e : G ≃ᵐ G) :
    MeasurePreserving e (Measure.count : Measure G) Measure.count := by
  refine ⟨e.measurable, ?_⟩
  ext S hS
  rw [Measure.map_apply e.measurable hS]
  have he : e ⁻¹' S = e.symm '' S := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_preimage, MeasurableEquiv.apply_symm_apply] using hy
  rw [he]
  exact Measure.count_injective_image e.symm.injective S

def diagonalEquiv (g : G) : (Z × G) ≃ᵐ (Z × G) :=
  (MeasurableEquiv.smul g).prodCongr (indexRight g⁻¹)

def indexShift (g : G) : (Z × G) ≃ᵐ (Z × G) :=
  (MeasurableEquiv.refl Z).prodCongr (indexLeft g)

def orbitPoint (p : Z × G) : Z := p.2 • p.1

theorem orbitPoint_measurable : Measurable (orbitPoint (G := G) (Z := Z)) :=
  measurable_from_prod_countable_left (fun g => measurable_const_smul g)

theorem diagonal_orbitPoint (g : G) (p : Z × G) :
    orbitPoint (diagonalEquiv g p) = orbitPoint p := by
  change (p.2 * g⁻¹) • (g • p.1) = p.2 • p.1
  simp only [mul_smul, inv_smul_smul]

theorem diagonal_indexShift (g h : G) (p : Z × G) :
    diagonalEquiv g (indexShift h p) = indexShift h (diagonalEquiv g p) := by
  change (g • p.1, (h*p.2)*g⁻¹) = (g • p.1, h*(p.2*g⁻¹))
  rw [mul_assoc]

def cornerMeasure (μ : Measure Z) (A : Set Z) : Measure (Z × G) :=
  (μ.restrict A).prod Measure.count

omit [Group G] [MeasurableSingletonClass G] [MulAction G Z] [MeasurableConstSMul G Z] in
theorem cornerMeasure_eq_restrict (μ : Measure Z) [SigmaFinite μ] (A : Set Z) :
    cornerMeasure (G := G) μ A = (μ.prod (Measure.count : Measure G)).restrict (A ×ˢ univ) := by
  simpa only [cornerMeasure, Measure.restrict_univ] using
    (Measure.prod_restrict (μ := μ) (ν := (Measure.count : Measure G)) A univ)

variable (μ : Measure Z) [SigmaFinite μ]
    (hmp : ∀ g : G, MeasurePreserving (fun z : Z => g • z) μ μ)

include hmp in
theorem diagonal_preserving (g : G) :
    MeasurePreserving (diagonalEquiv (Z := Z) g)
      (μ.prod (Measure.count : Measure G)) (μ.prod Measure.count) :=
  (hmp g).prod (count_preserving (indexRight g⁻¹))

omit [MulAction G Z] [MeasurableConstSMul G Z] in
theorem indexShift_preserving (A : Set Z) (g : G) :
    MeasurePreserving (indexShift (Z := Z) g)
      (cornerMeasure (G := G) μ A) (cornerMeasure μ A) :=
  (MeasurePreserving.id (μ.restrict A)).prod (count_preserving (indexLeft g))

include hmp in
/-- The greedy equidecomposition supplies actual inverse transports
between the finite-corner product measures. They preserve the orbit
point and commute with every left index shift almost everywhere. -/
theorem exists_induced_corner_transport
    (herg : ∀ s : Set Z, MeasurableSet s →
      (∀ g : G, (fun z : Z => g • z) ⁻¹' s = s) → μ s = 0 ∨ μ sᶜ = 0)
    (A B : Set Z) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfin : μ A ≠ ∞) (hmass : μ A = μ B) :
    ∃ F H : (Z × G) → (Z × G),
      MeasurePreserving F (cornerMeasure μ A) (cornerMeasure μ B) ∧
      MeasurePreserving H (cornerMeasure μ B) (cornerMeasure μ A) ∧
      (∀ᵐ p ∂cornerMeasure μ A, H (F p) = p) ∧
      (∀ᵐ p ∂cornerMeasure μ B, F (H p) = p) ∧
      (∀ᵐ p ∂cornerMeasure μ A, orbitPoint (F p) = orbitPoint p) ∧
      (∀ h : G, ∀ᵐ p ∂cornerMeasure μ A,
        F (indexShift h p) = indexShift h (F p)) := by
  obtain ⟨e, C, T, hm, hsub, hCdis, hTdis, heq, hcoverA, hcoverB⟩ :=
    exists_equidecomposition μ hmp herg A B hA hB hfin hmass
  let ν := μ.prod (Measure.count : Measure G)
  let CS : ℕ → Set (Z × G) := fun n => C n ×ˢ univ
  let TS : ℕ → Set (Z × G) := fun n => T n ×ˢ univ
  have hCSm : ∀ n, MeasurableSet (CS n) := fun n => (hm n).1.prod MeasurableSet.univ
  have hTSm : ∀ n, MeasurableSet (TS n) := fun n => (hm n).2.prod MeasurableSet.univ
  have hCSdis : Pairwise (fun i j => Disjoint (CS i) (CS j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hi hj
    exact Set.disjoint_left.mp (hCdis hij) hi.1 hj.1
  have hTSdis : Pairwise (fun i j => Disjoint (TS i) (TS j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hi hj
    exact Set.disjoint_left.mp (hTdis hij) hi.1 hj.1
  have hCSA : ν ((A ×ˢ univ) \ ⋃ n, CS n) = 0 := by
    have hs : (A ×ˢ (univ : Set G)) \ ⋃ n, CS n = (A \ ⋃ n, C n) ×ˢ univ := by
      ext p
      simp only [CS, mem_diff, mem_prod, mem_univ, mem_iUnion, and_true]
    rw [hs, Measure.prod_prod, hcoverA, zero_mul]
  have hTSB : ν ((B ×ˢ univ) \ ⋃ n, TS n) = 0 := by
    have hs : (B ×ˢ (univ : Set G)) \ ⋃ n, TS n = (B \ ⋃ n, T n) ×ˢ univ := by
      ext p
      simp only [TS, mem_diff, mem_prod, mem_univ, mem_iUnion, and_true]
    rw [hs, Measure.prod_prod, hcoverB, zero_mul]
  have himage (n : ℕ) : diagonalEquiv (e n) '' CS n = TS n := by
    ext p
    constructor
    · rintro ⟨⟨x,d⟩, hx, rfl⟩
      refine ⟨?_, mem_univ _⟩
      rw [heq]
      change (e n)⁻¹ • (e n • x) ∈ C n
      simpa only [inv_smul_smul] using hx.1
    · rintro ⟨hp, _⟩
      rw [heq] at hp
      refine ⟨((e n)⁻¹ • p.1, p.2 * e n), ⟨hp, mem_univ _⟩, ?_⟩
      change (e n • ((e n)⁻¹ • p.1), (p.2 * e n) * (e n)⁻¹) = p
      simp only [smul_inv_smul, mul_inv_cancel_right, Prod.mk.eta]
  obtain ⟨F,H,hF,hH,hFC,hHT,hHF,hFH⟩ := exists_piecewise_measure_transport ν
    (A ×ˢ univ) (B ×ˢ univ) CS TS hCSm hTSm
    (fun n p hp => ⟨(hsub n).1 hp.1, mem_univ _⟩)
    (fun n p hp => ⟨(hsub n).2 hp.1, mem_univ _⟩)
    hCSdis hTSdis hCSA hTSB (fun n => diagonalEquiv (e n))
    (fun n => diagonal_preserving μ hmp (e n)) himage
  have hsumA := restrict_eq_sum_of_disjoint_cover ν (A ×ˢ univ) CS hCSm
    (fun n p hp => ⟨(hsub n).1 hp.1, mem_univ _⟩) hCSdis hCSA
  have hAeq := cornerMeasure_eq_restrict (G := G) (μ := μ) A
  have hBeq := cornerMeasure_eq_restrict (G := G) (μ := μ) B
  simp only [ν, ← hAeq, ← hBeq] at hF hH hHF hFH
  refine ⟨F,H,hF,hH,hHF,hFH,?_,?_⟩
  · rw [hAeq, hsumA, Measure.ae_sum_iff]
    intro n
    filter_upwards [ae_restrict_mem (hCSm n)] with p hp
    rw [hFC n hp]
    exact diagonal_orbitPoint (e n) p
  · intro h
    rw [hAeq, hsumA, Measure.ae_sum_iff]
    intro n
    filter_upwards [ae_restrict_mem (hCSm n)] with p hp
    have hshift : indexShift h p ∈ CS n := ⟨hp.1, mem_univ _⟩
    rw [hFC n hshift, hFC n hp]
    exact diagonal_indexShift (e n) h p

end
end MeasureEquivalenceInducedCorners

#print axioms MeasureEquivalenceInducedCorners.count_preserving
#print axioms MeasureEquivalenceInducedCorners.exists_induced_corner_transport
