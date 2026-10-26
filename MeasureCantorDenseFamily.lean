import MeasureL2Constants
import MeasureGramSchmidtBorel

/-! A countable cylinder-indicator fundamental family in the actual
infinite-multiplicity L² fibers. -/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace MeasureUnitary

noncomputable section

theorem cantorCylinder_isSetAlgebra : IsSetAlgebra (Set.range cantorCylinder) where
  empty_mem := ⟨⟨∅, ∅⟩, cylinder_empty ∅⟩
  compl_mem := by
    rintro s ⟨⟨I, S⟩, rfl⟩
    exact ⟨⟨I, Sᶜ⟩, (compl_cylinder (α := fun _ : ℕ => Bool) I S).symm⟩
  union_mem := by
    classical
    rintro s t ⟨⟨I, S⟩, rfl⟩ ⟨⟨J, T⟩, rfl⟩
    exact ⟨⟨I ∪ J, Finset.restrict₂ (π := fun _ : ℕ => Bool) (Finset.subset_union_left (s₁ := I) (s₂ := J)) ⁻¹' S ∪
      Finset.restrict₂ (π := fun _ : ℕ => Bool) (Finset.subset_union_right (s₁ := I) (s₂ := J)) ⁻¹' T⟩,
      (union_cylinder (α := fun _ : ℕ => Bool) I J S T).symm⟩

theorem cantorCylinder_measureDense (μ : Measure CantorSpace) [IsFiniteMeasure μ] :
    μ.MeasureDense (Set.range cantorCylinder) :=
  Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite μ cantorCylinder_isSetAlgebra
    cantorCylinder_generates.symm

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

noncomputable def indicatorConstantCLM {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    E →L[ℂ] Lp E 2 μ := by
  let L : E →ₗ[ℂ] Lp E 2 μ := {
    toFun := indicatorConstLp 2 hs hμs
    map_add' := fun _ _ => indicatorConstLp_add.symm
    map_smul' := by
      intro c v
      apply Lp.ext
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := c • v),
        indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := v),
        Lp.coeFn_smul c (indicatorConstLp 2 hs hμs v)] with x hcv hv hc
      simp only [Pi.smul_apply] at hc
      simp only [RingHom.id_apply]
      rw [hcv, hc, hv]
      by_cases hx : x ∈ s <;> simp [hx] }
  exact L.mkContinuous (μ.real s ^ (1 / (2 : ℝ))) (fun v => by
    change ‖indicatorConstLp 2 hs hμs v‖ ≤ _
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
    exact le_of_eq (mul_comm _ _))

abbrev CantorFundamentalIndex := CantorCylinderIndex × ℕ

local instance cantorFiberMeasurable (μ : Measure CantorSpace) :
    MeasurableSpace (Lp OperatorCoding.CanonicalHilbert 2 μ) := borel _

local instance cantorFiberBorelSpace (μ : Measure CantorSpace) :
    BorelSpace (Lp OperatorCoding.CanonicalHilbert 2 μ) := ⟨rfl⟩

noncomputable def cantorFundamentalVector (μ : Measure CantorSpace) [IsFiniteMeasure μ]
    (k : CantorFundamentalIndex) : Lp OperatorCoding.CanonicalHilbert 2 μ :=
  indicatorConstLp 2 (cantorCylinder_measurable k.1) (measure_ne_top μ _)
    (lp.single 2 k.2 (1 : ℂ) : OperatorCoding.CanonicalHilbert)

noncomputable def cantorFundamentalClosedSpan (μ : Measure CantorSpace) [IsFiniteMeasure μ] :
    Submodule ℂ (Lp OperatorCoding.CanonicalHilbert 2 μ) :=
  (Submodule.span ℂ (Set.range (cantorFundamentalVector μ))).topologicalClosure

theorem cantorFundamentalClosedSpan_indicator (μ : Measure CantorSpace) [IsFiniteMeasure μ]
    (k : CantorCylinderIndex) (v : OperatorCoding.CanonicalHilbert) :
    indicatorConstLp 2 (cantorCylinder_measurable k) (measure_ne_top μ _) v ∈
      cantorFundamentalClosedSpan μ := by
  let L : OperatorCoding.CanonicalHilbert →L[ℂ] Lp OperatorCoding.CanonicalHilbert 2 μ :=
    indicatorConstantCLM μ (cantorCylinder_measurable k) (measure_ne_top μ _)
  have hsum := L.hasSum (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) v)
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hsum
  apply Filter.Eventually.of_forall
  intro s
  apply Submodule.sum_mem
  intro n hn
  have he : (lp.single 2 n (v n) : OperatorCoding.CanonicalHilbert) =
      (v n) • (lp.single 2 n (1 : ℂ) : OperatorCoding.CanonicalHilbert) := by
    simpa using (lp.single_smul (E := fun _ : ℕ => ℂ) 2 n (v n) (1 : ℂ))
  rw [he, L.map_smul]
  apply Submodule.smul_mem
  apply Submodule.le_topologicalClosure
  exact Submodule.subset_span ⟨(k, n), rfl⟩

theorem cantorFundamentalClosedSpan_all_indicators (μ : Measure CantorSpace) [IsFiniteMeasure μ]
    (v : OperatorCoding.CanonicalHilbert) {s : Set CantorSpace} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) : indicatorConstLp 2 hs hμs v ∈ cantorFundamentalClosedSpan μ := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have ha := (cantorCylinder_measureDense μ).indicatorConstLp_subset_closure 2 v
    (show indicatorConstLp 2 hs hμs v ∈
      {indicatorConstLp 2 ht hμt v | (t : Set CantorSpace) (ht : MeasurableSet t) (hμt : μ t ≠ ∞)}
      from ⟨s, hs, hμs, rfl⟩)
  apply closure_minimal (t := (cantorFundamentalClosedSpan μ : Set _)) ?_
    (Submodule.isClosed_topologicalClosure _) ha
  rintro x ⟨t, ht, hμt, rfl⟩
  obtain ⟨k, rfl⟩ := ht
  exact cantorFundamentalClosedSpan_indicator μ k v

theorem cantorFundamentalVector_dense_span (μ : Measure CantorSpace) [IsFiniteMeasure μ] :
    (Submodule.span ℂ (Set.range (cantorFundamentalVector μ))).topologicalClosure = ⊤ := by
  have hall : ∀ f : Lp OperatorCoding.CanonicalHilbert 2 μ, f ∈ cantorFundamentalClosedSpan μ := by
    apply Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (fun f : Lp OperatorCoding.CanonicalHilbert 2 μ => f ∈ cantorFundamentalClosedSpan μ)
    · intro v s hs hμs
      exact cantorFundamentalClosedSpan_all_indicators μ v hs hμs.ne
    · intro f g hf hg hdis hfm hgm
      exact Submodule.add_mem _ hfm hgm
    · exact Submodule.isClosed_topologicalClosure _
  apply top_unique
  intro f hf
  exact hall f

instance cantorFundamentalIndex_nonempty : Nonempty CantorFundamentalIndex :=
  ⟨(⟨∅, Set.univ⟩, 0)⟩

noncomputable def cantorFundamentalEnumeration : ℕ → CantorFundamentalIndex :=
  (exists_surjective_nat CantorFundamentalIndex).choose

theorem cantorFundamentalEnumeration_surjective : Function.Surjective cantorFundamentalEnumeration :=
  (exists_surjective_nat CantorFundamentalIndex).choose_spec

noncomputable def cantorFundamentalSequence (μ : Measure CantorSpace) [IsFiniteMeasure μ] :
    ℕ → Lp OperatorCoding.CanonicalHilbert 2 μ :=
  cantorFundamentalVector μ ∘ cantorFundamentalEnumeration

theorem cantorFundamentalSequence_dense_span (μ : Measure CantorSpace) [IsFiniteMeasure μ] :
    (Submodule.span ℂ (Set.range (cantorFundamentalSequence μ))).topologicalClosure = ⊤ := by
  unfold cantorFundamentalSequence
  rw [Function.Surjective.range_comp cantorFundamentalEnumeration_surjective]
  exact cantorFundamentalVector_dense_span μ

theorem cantorFundamentalSequence_nonzero_infinite (μ : Measure CantorSpace) [IsProbabilityMeasure μ] :
    {i | InnerProductSpace.gramSchmidtNormed ℂ (cantorFundamentalSequence μ) i ≠ 0}.Infinite :=
  gramSchmidtNormed_nonzero_infinite (cantorFundamentalSequence μ)
    (cantorFundamentalSequence_dense_span μ) (amplifiedL2_not_finiteDimensional μ)

noncomputable def cantorFiberBasis (μ : Measure CantorSpace) [IsProbabilityMeasure μ] :
    HilbertBasis ℕ ℂ (Lp OperatorCoding.CanonicalHilbert 2 μ) :=
  HilbertBasis.mk
    (selectedGramSchmidt_orthonormal (fun _ : Unit => cantorFundamentalSequence μ)
      (fun _ => cantorFundamentalSequence_nonzero_infinite μ) ()) (by
        rw [selectedGramSchmidt_span, cantorFundamentalSequence_dense_span])

noncomputable def cantorFiberCoordinates (μ : Measure CantorSpace) [IsProbabilityMeasure μ] :
    Lp OperatorCoding.CanonicalHilbert 2 μ ≃ₗᵢ[ℂ] OperatorCoding.CanonicalHilbert :=
  (cantorFiberBasis μ).repr

end

end MeasureUnitary

#print axioms MeasureUnitary.cantorFundamentalClosedSpan_indicator
