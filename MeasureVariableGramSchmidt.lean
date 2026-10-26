import MeasureGramSchmidtBorel

/-! Gram–Schmidt in genuinely varying Hilbert fibers. Measurability is
deduced from scalar Gram entries, without putting a fictitious common
topology on the different L² spaces. Every constructed section is an actual
finite linear combination of the fundamental sections. -/

open MeasureTheory InnerProductSpace Set

namespace MeasureUnitary

variable {S : Type*} [MeasurableSpace S]
variable {E : S → Type*} [∀ s, NormedAddCommGroup (E s)] [∀ s, InnerProductSpace ℂ (E s)]

def FiniteBorelSection (f : ∀ s, ℕ → E s) (v : ∀ s, E s) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (j : I → ℕ) (c : S → I → ℂ),
    (∀ i, Measurable (fun s => c s i)) ∧ ∀ s, v s = ∑ i, c s i • f s (j i)

theorem finiteBorelSection_raw (f : ∀ s, ℕ → E s) (n : ℕ) :
    FiniteBorelSection f (fun s => f s n) := by
  refine ⟨Unit, inferInstance, (fun _ => n), (fun _ _ => 1),
    (fun _ => measurable_const), ?_⟩
  intro s
  simp

theorem finiteBorelSection_zero (f : ∀ s, ℕ → E s) :
    FiniteBorelSection f (fun s => (0 : E s)) := by
  refine ⟨Empty, inferInstance, Empty.elim, (fun _ => Empty.elim),
    (fun i => Empty.elim i), ?_⟩
  intro s
  simp

theorem FiniteBorelSection.add {f : ∀ s, ℕ → E s} {v w : ∀ s, E s}
    (hv : FiniteBorelSection f v) (hw : FiniteBorelSection f w) :
    FiniteBorelSection f (fun s => v s + w s) := by
  classical
  obtain ⟨I, hI, j, c, hc, hv⟩ := hv
  obtain ⟨J, hJ, k, d, hd, hw⟩ := hw
  letI := hI
  letI := hJ
  refine ⟨I ⊕ J, inferInstance, Sum.elim j k, (fun s => Sum.elim (c s) (d s)), ?_, ?_⟩
  · intro i
    cases i with
    | inl i => exact hc i
    | inr i => exact hd i
  · intro s
    dsimp only
    rw [Fintype.sum_sum_type, hv s, hw s]
    rfl

theorem FiniteBorelSection.smul {f : ∀ s, ℕ → E s} {v : ∀ s, E s}
    (hv : FiniteBorelSection f v) {a : S → ℂ} (ha : Measurable a) :
    FiniteBorelSection f (fun s => a s • v s) := by
  obtain ⟨I, hI, j, c, hc, hv⟩ := hv
  letI := hI
  refine ⟨I, hI, j, (fun s i => a s * c s i), (fun i => ha.mul (hc i)), ?_⟩
  intro s
  dsimp only
  rw [hv s, Finset.smul_sum]
  simp only [smul_smul]

theorem FiniteBorelSection.neg {f : ∀ s, ℕ → E s} {v : ∀ s, E s}
    (hv : FiniteBorelSection f v) : FiniteBorelSection f (fun s => -v s) := by
  simpa only [neg_one_smul] using hv.smul (a := fun _ => (-1 : ℂ)) measurable_const

theorem FiniteBorelSection.sub {f : ∀ s, ℕ → E s} {v w : ∀ s, E s}
    (hv : FiniteBorelSection f v) (hw : FiniteBorelSection f w) :
    FiniteBorelSection f (fun s => v s - w s) := by
  simpa only [sub_eq_add_neg] using hv.add hw.neg

theorem finiteBorelSection_sum {f : ∀ s, ℕ → E s} {I : Type*}
    (t : Finset I) (v : I → ∀ s, E s) (hv : ∀ i ∈ t, FiniteBorelSection f (v i)) :
    FiniteBorelSection f (fun s => ∑ i ∈ t, v i s) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using finiteBorelSection_zero f
  | @insert i t hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hv i (Finset.mem_insert_self _ _)).add (ih (fun j hj => hv j (Finset.mem_insert_of_mem hj)))

theorem FiniteBorelSection.inner_measurable {f : ∀ s, ℕ → E s}
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j)))
    {v w : ∀ s, E s} (hv : FiniteBorelSection f v) (hw : FiniteBorelSection f w) :
    Measurable (fun s => inner ℂ (v s) (w s)) := by
  obtain ⟨I, hI, j, c, hc, hv⟩ := hv
  obtain ⟨J, hJ, k, d, hd, hw⟩ := hw
  letI := hI
  letI := hJ
  have heq : (fun s => inner ℂ (v s) (w s)) =
      fun s => ∑ i : I, ∑ l : J, d s l * ((starRingEnd ℂ) (c s i) * inner ℂ (f s (j i)) (f s (k l))) := by
    funext s
    rw [hv s, hw s, sum_inner]
    simp only [inner_sum, inner_smul_left, inner_smul_right]
  rw [heq]
  apply Finset.measurable_sum
  intro i hi
  apply Finset.measurable_sum
  intro l hl
  exact (hd l).mul ((Complex.continuous_conj.measurable.comp (hc i)).mul (hgram (j i) (k l)))

theorem FiniteBorelSection.norm_measurable {f : ∀ s, ℕ → E s}
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j)))
    {v : ∀ s, E s} (hv : FiniteBorelSection f v) : Measurable (fun s => ‖v s‖) := by
  have hm := (Complex.continuous_re.measurable.comp (hv.inner_measurable hgram hv)).sqrt
  convert hm using 1
  funext s
  change ‖v s‖ = Real.sqrt (RCLike.re (inner ℂ (v s) (v s)))
  rw [← norm_sq_eq_re_inner (𝕜 := ℂ), Real.sqrt_sq (norm_nonneg _)]

theorem variableGramSchmidt_finiteBorelSection (f : ∀ s, ℕ → E s)
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j))) (n : ℕ) :
    FiniteBorelSection f (fun s => gramSchmidt ℂ (f s) n) := by
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
    apply (finiteBorelSection_raw f n).sub
    apply finiteBorelSection_sum
    intro i hi
    have hg := ih i (Finset.mem_Iio.mp hi)
    apply hg.smul
    exact (hg.inner_measurable hgram (finiteBorelSection_raw f n)).div
      (Complex.continuous_ofReal.measurable.comp ((hg.norm_measurable hgram).pow_const 2))

theorem variableGramSchmidtNormed_finiteBorelSection (f : ∀ s, ℕ → E s)
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j))) (n : ℕ) :
    FiniteBorelSection f (fun s => gramSchmidtNormed ℂ (f s) n) := by
  have hg := variableGramSchmidt_finiteBorelSection f hgram n
  exact hg.smul ((Complex.continuous_ofReal.measurable.comp (hg.norm_measurable hgram)).inv)

theorem FiniteBorelSection.map_linear {f : ∀ s, ℕ → E s}
    (T : ∀ s, E s →ₗ[ℂ] E s)
    (hT : ∀ n, FiniteBorelSection f (fun s => T s (f s n)))
    {v : ∀ s, E s} (hv : FiniteBorelSection f v) :
    FiniteBorelSection f (fun s => T s (v s)) := by
  obtain ⟨I, hI, j, c, hc, hv⟩ := hv
  letI := hI
  have heq : (fun s => T s (v s)) = fun s => ∑ i : I, c s i • T s (f s (j i)) := by
    funext s
    rw [hv s, map_sum]
    simp only [map_smul]
  rw [heq]
  exact finiteBorelSection_sum Finset.univ (fun i s => c s i • T s (f s (j i)))
    (fun i hi => (hT (j i)).smul (hc i))

theorem variableGramSchmidtNormed_norm_measurable (f : ∀ s, ℕ → E s)
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j))) (n : ℕ) :
    Measurable (fun s => ‖gramSchmidtNormed ℂ (f s) n‖) :=
  (variableGramSchmidtNormed_finiteBorelSection f hgram n).norm_measurable hgram

theorem variableGramSchmidtNormed_nonzero_measurableSet (f : ∀ s, ℕ → E s)
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j))) (n : ℕ) :
    MeasurableSet {s | gramSchmidtNormed ℂ (f s) n ≠ 0} := by
  have h := (variableGramSchmidtNormed_norm_measurable f hgram n) (measurableSet_singleton (0 : ℝ))
  simpa only [Set.preimage, Set.mem_singleton_iff, norm_eq_zero] using h.compl

set_option maxHeartbeats 800000 in
theorem variableGramSchmidtNormed_operator_inner_measurable (f : ∀ s, ℕ → E s)
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j)))
    (T : ∀ s, E s →ₗ[ℂ] E s)
    (hT : ∀ n, FiniteBorelSection f (fun s => T s (f s n))) (i j : ℕ) :
    Measurable (fun s => inner ℂ (gramSchmidtNormed ℂ (f s) i)
      (T s (gramSchmidtNormed ℂ (f s) j))) :=
  (variableGramSchmidtNormed_finiteBorelSection f hgram i).inner_measurable hgram
    ((variableGramSchmidtNormed_finiteBorelSection f hgram j).map_linear T hT)

noncomputable def variableSelectedGramSchmidt (f : ∀ s, ℕ → E s) (s : S) (n : ℕ) : E s :=
  gramSchmidtNormed ℂ (f s) (Nat.nth (fun i => gramSchmidtNormed ℂ (f s) i ≠ 0) n)

set_option maxHeartbeats 800000 in
theorem variableSelectedGramSchmidt_operator_inner_measurable (f : ∀ s, ℕ → E s)
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j)))
    (hinf : ∀ s, {i | gramSchmidtNormed ℂ (f s) i ≠ 0}.Infinite)
    (T : ∀ s, E s →ₗ[ℂ] E s)
    (hT : ∀ n, FiniteBorelSection f (fun s => T s (f s n))) (i j : ℕ) :
    Measurable (fun s => inner ℂ (variableSelectedGramSchmidt f s i)
      (T s (variableSelectedGramSchmidt f s j))) := by
  classical
  have hI (n : ℕ) : Measurable (fun s => Nat.nth (fun k => gramSchmidtNormed ℂ (f s) k ≠ 0) n) :=
    measurable_nat_nth _ (variableGramSchmidtNormed_nonzero_measurableSet f hgram) hinf n
  have hm : Measurable (fun p : S × (ℕ × ℕ) =>
      inner ℂ (gramSchmidtNormed ℂ (f p.1) p.2.1)
        (T p.1 (gramSchmidtNormed ℂ (f p.1) p.2.2))) :=
    measurable_from_prod_countable_left (fun ij =>
      variableGramSchmidtNormed_operator_inner_measurable f hgram T hT ij.1 ij.2)
  exact hm.comp (measurable_id.prodMk ((hI i).prodMk (hI j)))

end MeasureUnitary

#print axioms MeasureUnitary.variableGramSchmidtNormed_finiteBorelSection
