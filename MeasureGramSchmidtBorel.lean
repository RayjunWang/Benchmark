import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Data.Nat.Nth
import HilbertSequenceTopology

/-! Borel Gram–Schmidt and Borel removal of its zero vectors.
These are fixed-fiber results; a parameter-dependent L² trivialization still
requires a measurable dense fundamental family. -/

open MeasureTheory InnerProductSpace Set Finset

namespace MeasureUnitary

variable {S : Type*} [MeasurableSpace S]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem measurable_gramSchmidt (f : S → ℕ → E)
    (hf : ∀ n, Measurable (fun s => f s n)) (n : ℕ) :
    Measurable (fun s => gramSchmidt ℂ (f s) n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have heq : (fun s => gramSchmidt ℂ (f s) n) = fun s => f s n -
        ∑ i ∈ Finset.Iio n,
          (inner ℂ (gramSchmidt ℂ (f s) i) (f s n) /
            ((‖gramSchmidt ℂ (f s) i‖ ^ 2 : ℝ) : ℂ)) • gramSchmidt ℂ (f s) i := by
      funext s
      rw [gramSchmidt_def]
      simp only [Submodule.starProjection_singleton]
      rfl
    rw [heq]
    apply (hf n).sub
    apply Finset.measurable_sum
    intro i hi
    have hg := ih i (Finset.mem_Iio.mp hi)
    have hden : Measurable (fun s => ((‖gramSchmidt ℂ (f s) i‖ ^ 2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (hg.norm.pow_const 2)
    exact ((hg.inner (hf n)).div hden).smul hg

theorem measurable_gramSchmidtNormed (f : S → ℕ → E)
    (hf : ∀ n, Measurable (fun s => f s n)) (n : ℕ) :
    Measurable (fun s => gramSchmidtNormed ℂ (f s) n) := by
  unfold gramSchmidtNormed
  have hg := measurable_gramSchmidt f hf n
  exact ((Complex.continuous_ofReal.measurable.comp hg.norm).inv).smul hg

theorem measurable_nat_count (p : S → ℕ → Prop) [∀ s, DecidablePred (p s)]
    (hp : ∀ n, MeasurableSet {s | p s n}) (n : ℕ) :
    Measurable (fun s => Nat.count (p s) n) := by
  induction n with
  | zero => simpa only [Nat.count_zero] using (measurable_const : Measurable (fun _ : S => (0 : ℕ)))
  | succ n ih =>
    simp_rw [Nat.count_succ]
    exact ih.add (Measurable.ite (hp n) measurable_const measurable_const)

theorem measurable_nat_nth (p : S → ℕ → Prop) [∀ s, DecidablePred (p s)]
    (hp : ∀ n, MeasurableSet {s | p s n}) (hinf : ∀ s, {n | p s n}.Infinite) (n : ℕ) :
    Measurable (fun s => Nat.nth (p s) n) := by
  apply measurable_to_countable'
  intro m
  have heq : {s | Nat.nth (p s) n = m} = {s | p s m} ∩ {s | Nat.count (p s) m = n} := by
    ext s
    constructor
    · intro h
      exact ⟨h ▸ Nat.nth_mem_of_infinite (hinf s) n,
        h ▸ Nat.count_nth_of_infinite (hinf s) n⟩
    · rintro ⟨hm, hc⟩
      rw [← hc]
      exact Nat.nth_count hm
  change MeasurableSet {s | Nat.nth (p s) n = m}
  rw [heq]
  exact (hp m).inter (measurableSet_eq_fun (measurable_nat_count p hp m) measurable_const)

noncomputable def selectedGramSchmidt (f : S → ℕ → E) (s : S) (n : ℕ) : E :=
  gramSchmidtNormed ℂ (f s) (Nat.nth (fun i => gramSchmidtNormed ℂ (f s) i ≠ 0) n)

set_option maxHeartbeats 800000 in
theorem measurable_selectedGramSchmidt (f : S → ℕ → E)
    (hf : ∀ n, Measurable (fun s => f s n))
    (hinf : ∀ s, {i | gramSchmidtNormed ℂ (f s) i ≠ 0}.Infinite) (n : ℕ) :
    Measurable (fun s => selectedGramSchmidt f s n) := by
  classical
  have hp : ∀ i, MeasurableSet {s | gramSchmidtNormed ℂ (f s) i ≠ 0} :=
    fun i => (measurableSet_eq_fun (measurable_gramSchmidtNormed f hf i) measurable_const).compl
  have hn := measurable_nat_nth (fun s i => gramSchmidtNormed ℂ (f s) i ≠ 0) hp hinf n
  have hfamily : Measurable (fun sn : S × ℕ => gramSchmidtNormed ℂ (f sn.1) sn.2) :=
    measurable_from_prod_countable_left (fun i => measurable_gramSchmidtNormed f hf i)
  exact hfamily.comp (measurable_id.prodMk hn)

theorem selectedGramSchmidt_orthonormal (f : S → ℕ → E)
    (hinf : ∀ s, {i | gramSchmidtNormed ℂ (f s) i ≠ 0}.Infinite) (s : S) :
    Orthonormal ℂ (selectedGramSchmidt f s) := by
  classical
  let g : ℕ → {i | gramSchmidtNormed ℂ (f s) i ≠ 0} :=
    fun n => ⟨Nat.nth (fun i => gramSchmidtNormed ℂ (f s) i ≠ 0) n,
      Nat.nth_mem_of_infinite (hinf s) n⟩
  have hg : Function.Injective g := by
    intro i j h
    exact (Nat.nth_strictMono (hinf s)).injective (congrArg Subtype.val h)
  exact (gramSchmidtNormed_orthonormal' (𝕜 := ℂ) (f s)).comp g hg

theorem selectedGramSchmidt_span (f : S → ℕ → E) (s : S) :
    Submodule.span ℂ (Set.range (selectedGramSchmidt f s)) =
      Submodule.span ℂ (Set.range (f s)) := by
  classical
  calc
    Submodule.span ℂ (Set.range (selectedGramSchmidt f s)) =
        Submodule.span ℂ (Set.range (gramSchmidtNormed ℂ (f s))) := by
      apply le_antisymm
      · apply Submodule.span_mono
        rintro x ⟨n, rfl⟩
        exact ⟨_, rfl⟩
      · apply Submodule.span_le.mpr
        rintro x ⟨i, rfl⟩
        by_cases hi : gramSchmidtNormed ℂ (f s) i = 0
        · rw [hi]
          exact Submodule.zero_mem _
        · have hx : gramSchmidtNormed ℂ (f s) i = selectedGramSchmidt f s
              (Nat.count (fun j => gramSchmidtNormed ℂ (f s) j ≠ 0) i) := by
            unfold selectedGramSchmidt
            rw [Nat.nth_count hi]
          rw [hx]
          exact Submodule.subset_span ⟨_, rfl⟩
    _ = Submodule.span ℂ (Set.range (gramSchmidt ℂ (f s))) :=
      span_gramSchmidtNormed_range (f s)
    _ = Submodule.span ℂ (Set.range (f s)) := span_gramSchmidt ℂ (f s)

noncomputable def selectedGramSchmidtBasis [CompleteSpace E] (f : S → ℕ → E)
    (hinf : ∀ s, {i | gramSchmidtNormed ℂ (f s) i ≠ 0}.Infinite)
    (hdense : ∀ s, (Submodule.span ℂ (Set.range (f s))).topologicalClosure = ⊤)
    (s : S) : HilbertBasis ℕ ℂ E :=
  HilbertBasis.mk (selectedGramSchmidt_orthonormal f hinf s) (by
    rw [selectedGramSchmidt_span, hdense s])

theorem selectedGramSchmidtBasis_apply [CompleteSpace E] (f : S → ℕ → E)
    (hinf : ∀ s, {i | gramSchmidtNormed ℂ (f s) i ≠ 0}.Infinite)
    (hdense : ∀ s, (Submodule.span ℂ (Set.range (f s))).topologicalClosure = ⊤)
    (s : S) (n : ℕ) : selectedGramSchmidtBasis f hinf hdense s n = selectedGramSchmidt f s n := by
  exact congr_fun (HilbertBasis.coe_mk (selectedGramSchmidt_orthonormal f hinf s) _) n

theorem gramSchmidtNormed_nonzero_infinite (f : ℕ → E)
    (hdense : (Submodule.span ℂ (Set.range f)).topologicalClosure = ⊤)
    (hinfinite : ¬ FiniteDimensional ℂ E) :
    {i | gramSchmidtNormed ℂ f i ≠ 0}.Infinite := by
  classical
  intro hfinite
  have hfiniteRange : (Set.range (gramSchmidtNormed ℂ f)).Finite := by
    apply (hfinite.image (gramSchmidtNormed ℂ f)).insert (0 : E) |>.subset
    rintro x ⟨i, rfl⟩
    by_cases hi : gramSchmidtNormed ℂ f i = 0
    · exact Set.mem_insert_iff.mpr (Or.inl hi)
    · exact Set.mem_insert_of_mem _ ⟨i, hi, rfl⟩
  letI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (gramSchmidtNormed ℂ f))) :=
    FiniteDimensional.span_of_finite ℂ hfiniteRange
  have hspan : Submodule.span ℂ (Set.range (gramSchmidtNormed ℂ f)) = ⊤ := by
    rw [← (Submodule.span ℂ (Set.range (gramSchmidtNormed ℂ f))).closed_of_finiteDimensional.submodule_topologicalClosure_eq,
      span_gramSchmidtNormed_range, span_gramSchmidt, hdense]
  apply hinfinite
  apply Module.Finite.of_surjective (Submodule.span ℂ (Set.range (gramSchmidtNormed ℂ f))).subtype
  intro x
  have hx : x ∈ Submodule.span ℂ (Set.range (gramSchmidtNormed ℂ f)) := by rw [hspan]; trivial
  exact ⟨⟨x, hx⟩, rfl⟩

set_option maxHeartbeats 800000 in
theorem measurable_selectedGramSchmidt_coordinates [CompleteSpace E] (f : S → ℕ → E)
    (hf : ∀ n, Measurable (fun s => f s n))
    (hinf : ∀ s, {i | gramSchmidtNormed ℂ (f s) i ≠ 0}.Infinite)
    (hdense : ∀ s, (Submodule.span ℂ (Set.range (f s))).topologicalClosure = ⊤)
    (v : S → E) (hv : Measurable v) :
    @Measurable S OperatorCoding.CanonicalHilbert _ (borel _)
      (fun s => (selectedGramSchmidtBasis f hinf hdense s).repr (v s)) := by
  letI : MeasurableSpace OperatorCoding.CanonicalHilbert := borel _
  letI : BorelSpace OperatorCoding.CanonicalHilbert := ⟨rfl⟩
  apply OperatorCoding.canonicalHilbert_coordinates_measurableEmbedding.measurable_comp_iff.mp
  change Measurable (fun s => fun n => (selectedGramSchmidtBasis f hinf hdense s).repr (v s) n)
  apply measurable_pi_iff.mpr
  intro n
  simp only [HilbertBasis.repr_apply_apply, selectedGramSchmidtBasis_apply]
  exact (measurable_selectedGramSchmidt f hf hinf n).inner hv

end MeasureUnitary

#print axioms MeasureUnitary.measurable_selectedGramSchmidt
