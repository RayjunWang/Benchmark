import FiniteFourier
import ScalarMultiplier
import TrigMultiplier

/-!
Finite product tori: arbitrary single-coordinate shifts compared with the
uniform three-point product walk. This is stronger than the half-turn case.
-/

open scoped BigOperators ComplexConjugate

namespace MeasureEquivalenceTorus

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} [NeZero m]

def axisHom (j : ι) : ZMod m →+ (ι → ZMod m) where
  toFun u i := if i = j then u else 0
  map_zero' := by ext i; simp
  map_add' a b := by ext i; by_cases h : i = j <;> simp [h]

noncomputable def coordinateChar (χ : AddChar (ι → ZMod m) ℂ) (j : ι) :
    AddChar (ZMod m) ℂ := χ.compAddMonoidHom (axisHom j)

lemma char_map_sum {A : Type*} [AddCommGroup A] (χ : AddChar A ℂ)
    {J : Type*} (s : Finset J) (f : J → A) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, χ.map_add_eq_mul, ih]

omit [NeZero m] in
lemma char_factor (χ : AddChar (ι → ZMod m) ℂ) (x : ι → ZMod m) :
    χ x = ∏ j, coordinateChar χ j (x j) := by
  have hx : x = ∑ j, axisHom j (x j) := by
    ext i
    simp [axisHom]
  conv_lhs => rw [hx, char_map_sum]
  rfl

def step (t : Fin 3) : ZMod m := ![-1, 0, 1] t

def shortShift (ε : ι → Fin 3) : ι → ZMod m := fun j => step (ε j)

noncomputable def q (χ : AddChar (ι → ZMod m) ℂ) (j : ι) : ℝ :=
  (1 + 2 * (coordinateChar χ j 1).re) / 3

omit [Fintype ι] in
lemma coordinate_step_sum (χ : AddChar (ι → ZMod m) ℂ) (j : ι) :
    (∑ t : Fin 3, coordinateChar χ j (step t)) = (3 : ℂ) * q χ j := by
  simp only [Fin.sum_univ_three, step, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, AddChar.map_zero_eq_one, AddChar.map_neg_eq_conj]
  apply Complex.ext <;> simp [q]
  ring

lemma random_character_sum (χ : AddChar (ι → ZMod m) ℂ) :
    (∑ ε : ι → Fin 3, χ (shortShift ε)) =
      (3 : ℂ) ^ Fintype.card ι * (∏ j, q χ j : ℝ) := by
  simp_rw [char_factor]
  change (∑ ε : ι → Fin 3, ∏ j, coordinateChar χ j (step (ε j))) = _
  rw [← Fintype.prod_sum (fun (j : ι) (t : Fin 3) => coordinateChar χ j (step t))]
  simp_rw [coordinate_step_sum]
  simp [Finset.prod_mul_distrib]

lemma random_energy_multiplier (χ : AddChar (ι → ZMod m) ℂ) :
    (∑ ε : ι → Fin 3, ‖χ (shortShift ε) - 1‖ ^ 2) =
      (3 : ℝ) ^ Fintype.card ι * (2 * (1 - ∏ j, q χ j)) := by
  have hre : (∑ ε : ι → Fin 3, (χ (shortShift ε)).re) =
      (3 : ℝ) ^ Fintype.card ι * ∏ j, q χ j := by
    have h := congrArg Complex.re (random_character_sum χ)
    have hreal : (3 : ℂ) ^ Fintype.card ι * (∏ j, q χ j : ℝ) =
        (((3 : ℝ) ^ Fintype.card ι * ∏ j, q χ j : ℝ) : ℂ) := by push_cast; rfl
    rw [hreal] at h
    simpa only [Complex.re_sum, Complex.ofReal_re] using h
  simp_rw [Complex.norm_sub_one_sq_eq_of_norm_eq_one (χ.norm_apply _)]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [hre]
  ring

noncomputable def frequency (χ : AddChar (ι → ZMod m) ℂ) (j : ι) : ZMod m :=
  AddChar.zmodAddEquiv.symm (coordinateChar χ j)

omit [Fintype ι] in
lemma coordinateChar_frequency (χ : AddChar (ι → ZMod m) ℂ) (j : ι) :
    coordinateChar χ j = AddChar.zmodAddEquiv (frequency χ j) := by
  simp [frequency]

lemma zmod_frequency_one (k : ZMod m) :
    ((AddChar.zmodAddEquiv k) 1).re =
      Real.cos (2 * Real.pi * (k.val : ℝ) / (m : ℝ)) := by
  change ((AddChar.zmod m k 1 : Circle) : ℂ).re = _
  have h := AddChar.zmod_intCast m (k.val : ℤ) (1 : ℤ)
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_one,
    mul_one] at h
  rw [h, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
  congr 1
  ring

omit [Fintype ι] in
lemma q_abs_le_one (χ : AddChar (ι → ZMod m) ℂ) (j : ι) : |q χ j| ≤ 1 := by
  have h := Complex.abs_re_le_norm (coordinateChar χ j 1)
  rw [(coordinateChar χ j).norm_apply] at h
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  unfold q
  exact abs_le.mpr ⟨by linarith, by linarith⟩

omit [Fintype ι] in
lemma q_abs_gap (χ : AddChar (ι → ZMod m) ℂ) (hm : 2 ≤ m) (j : ι)
    (hj : frequency χ j ≠ 0) : |q χ j| ≤ 1 - 1 / (m : ℝ) ^ 2 := by
  have hk1 : 1 ≤ ((frequency χ j).val : ℝ) := by
    exact_mod_cast (ZMod.val_pos.mpr hj)
  have hkm : ((frequency χ j).val : ℝ) ≤ (m : ℝ) - 1 := by
    have h := (frequency χ j).val_lt
    have h' : (frequency χ j).val + 1 ≤ m := h
    have hreal : ((frequency χ j).val : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h'
    linarith
  have h := MeasureEquivalenceTrig.trig_coordinate_bound (m : ℝ)
    (frequency χ j).val (by exact_mod_cast hm) hk1 hkm
  simpa only [q, coordinateChar_frequency, zmod_frequency_one] using h

noncomputable def active (χ : AddChar (ι → ZMod m) ℂ) : Finset ι :=
  Finset.univ.filter fun j => frequency χ j ≠ 0

lemma long_multiplier_le (χ : AddChar (ι → ZMod m) ℂ) (a : ι → ZMod m) :
    (∑ j, ‖χ (axisHom j (a j)) - 1‖ ^ 2) ≤ 4 * ((active χ).card : ℝ) := by
  have hpoint (j : ι) : ‖χ (axisHom j (a j)) - 1‖ ^ 2 ≤
      if frequency χ j ≠ 0 then (4 : ℝ) else 0 := by
    by_cases hj : frequency χ j ≠ 0
    · rw [if_pos hj]
      have hnorm := norm_sub_le (χ (axisHom j (a j))) (1 : ℂ)
      simp only [χ.norm_apply, norm_one] at hnorm
      have hn := norm_nonneg (χ (axisHom j (a j)) - 1)
      nlinarith
    · rw [if_neg hj]
      have hz : frequency χ j = 0 := not_ne_iff.mp hj
      change ‖coordinateChar χ j (a j) - 1‖ ^ 2 ≤ 0
      rw [coordinateChar_frequency, hz]
      have hzmap : AddChar.zmodAddEquiv (0 : ZMod m) =
          (0 : AddChar (ZMod m) ℂ) :=
        map_zero (AddChar.zmodAddEquiv : ZMod m ≃+ AddChar (ZMod m) ℂ)
      rw [hzmap]
      simp
  calc
    (∑ j, ‖χ (axisHom j (a j)) - 1‖ ^ 2) ≤
        ∑ j, if frequency χ j ≠ 0 then (4 : ℝ) else 0 :=
      Finset.sum_le_sum fun j _ => hpoint j
    _ = 4 * ((active χ).card : ℝ) := by
      rw [← Finset.sum_filter]
      simp [active, mul_comm]

theorem torus_multiplier (χ : AddChar (ι → ZMod m) ℂ) (a : ι → ZMod m)
    (hm : 2 ≤ m) (hn : Fintype.card ι ≤ m ^ 2) :
    (∑ j, ‖χ (axisHom j (a j)) - 1‖ ^ 2) ≤
      (4 * (m : ℝ) ^ 2 / (3 : ℝ) ^ Fintype.card ι) *
        ∑ ε : ι → Fin 3, ‖χ (shortShift ε) - 1‖ ^ 2 := by
  have hsub : active χ ⊆ Finset.univ := Finset.filter_subset _ _
  have hcard : (active χ).card ≤ m ^ 2 :=
    (Finset.card_le_card hsub).trans (by simpa using hn)
  have hscalar := MeasureEquivalenceScalar.square_scale_multiplier
    Finset.univ (active χ) (q χ) (m : ℝ) hsub
    (by exact_mod_cast (show 1 ≤ m by omega))
    (fun j _ => q_abs_le_one χ j)
    (fun j hj => q_abs_gap χ hm j (Finset.mem_filter.mp hj).2)
    (by exact_mod_cast hcard)
  calc
    (∑ j, ‖χ (axisHom j (a j)) - 1‖ ^ 2) ≤
        4 * ((active χ).card : ℝ) := long_multiplier_le χ a
    _ ≤ 4 * (m : ℝ) ^ 2 * (2 * (1 - ∏ j, q χ j)) := hscalar
    _ = (4 * (m : ℝ) ^ 2 / (3 : ℝ) ^ Fintype.card ι) *
        ∑ ε : ι → Fin 3, ‖χ (shortShift ε) - 1‖ ^ 2 := by
      rw [random_energy_multiplier]
      field_simp

/-- The finite-torus Hilbert inequality, with arbitrary shifts on each axis.
The missing common average over `x` cancels on both sides. -/
theorem finite_torus_hilbert {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (F : (ι → ZMod m) → E) (a : ι → ZMod m)
    (hm : 2 ≤ m) (hn : Fintype.card ι ≤ m ^ 2) :
    (∑ j, ∑ x, ‖F (x + axisHom j (a j)) - F x‖ ^ 2) ≤
      (4 * (m : ℝ) ^ 2 / (3 : ℝ) ^ Fintype.card ι) *
        ∑ ε : ι → Fin 3, ∑ x, ‖F (x + shortShift ε) - F x‖ ^ 2 :=
  MeasureEquivalenceFourier.spectral_comparison
    (fun j => axisHom j (a j)) shortShift _ (fun χ => torus_multiplier χ a hm hn) F

/-- The same inequality for arbitrary real inner product spaces. The finite
range spans a finite-dimensional subspace, whose orthonormal coordinates embed
isometrically into a complex Euclidean space. -/
theorem finite_torus_real_hilbert {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (F : (ι → ZMod m) → E) (a : ι → ZMod m)
    (hm : 2 ≤ m) (hn : Fintype.card ι ≤ m ^ 2) :
    (∑ j, ∑ x, ‖F (x + axisHom j (a j)) - F x‖ ^ 2) ≤
      (4 * (m : ℝ) ^ 2 / (3 : ℝ) ^ Fintype.card ι) *
        ∑ ε : ι → Fin 3, ∑ x, ‖F (x + shortShift ε) - F x‖ ^ 2 := by
  let S : Submodule ℝ E := Submodule.span ℝ (Set.range F)
  let : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (Set.finite_range F)
  let f : (ι → ZMod m) → S := fun x =>
    ⟨F x, Submodule.subset_span (Set.mem_range_self x)⟩
  let b := stdOrthonormalBasis ℝ S
  let g : (ι → ZMod m) → EuclideanSpace ℂ (Fin (Module.finrank ℝ S)) :=
    fun x => WithLp.toLp 2 (fun i => ((b.repr (f x) i : ℝ) : ℂ))
  have hnorm (x y : ι → ZMod m) : ‖g x - g y‖ ^ 2 = ‖F x - F y‖ ^ 2 := by
    calc
      ‖g x - g y‖ ^ 2 = ‖b.repr (f x) - b.repr (f y)‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
        apply Finset.sum_congr rfl
        intro i _
        simp [g, PiLp.sub_apply, ← Complex.ofReal_sub]
      _ = ‖f x - f y‖ ^ 2 := by rw [← map_sub, b.repr.norm_map]
      _ = ‖F x - F y‖ ^ 2 := rfl
  have h := finite_torus_hilbert g a hm hn
  simpa only [hnorm] using h

/-- Uniform-expectation form of the strengthened inequality. -/
theorem finite_torus_hilbert_expect {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (F : (ι → ZMod m) → E) (a : ι → ZMod m)
    (hm : 2 ≤ m) (hn : Fintype.card ι ≤ m ^ 2) :
    (∑ j, 𝔼 x, ‖F (x + axisHom j (a j)) - F x‖ ^ 2) ≤
      4 * (m : ℝ) ^ 2 *
        (𝔼 ε : ι → Fin 3, 𝔼 x, ‖F (x + shortShift ε) - F x‖ ^ 2) := by
  simp_rw [Fintype.expect_eq_sum_div_card]
  rw [← Finset.sum_div, ← Finset.sum_div]
  have h := div_le_div_of_nonneg_right (finite_torus_hilbert F a hm hn)
    (Nat.cast_nonneg (Fintype.card (ι → ZMod m)) : (0 : ℝ) ≤ _)
  convert h using 1
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- Uniform-expectation form for real targets. -/
theorem finite_torus_real_hilbert_expect {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (F : (ι → ZMod m) → E) (a : ι → ZMod m)
    (hm : 2 ≤ m) (hn : Fintype.card ι ≤ m ^ 2) :
    (∑ j, 𝔼 x, ‖F (x + axisHom j (a j)) - F x‖ ^ 2) ≤
      4 * (m : ℝ) ^ 2 *
        (𝔼 ε : ι → Fin 3, 𝔼 x, ‖F (x + shortShift ε) - F x‖ ^ 2) := by
  simp_rw [Fintype.expect_eq_sum_div_card]
  rw [← Finset.sum_div, ← Finset.sum_div]
  have h := div_le_div_of_nonneg_right (finite_torus_real_hilbert F a hm hn)
    (Nat.cast_nonneg (Fintype.card (ι → ZMod m)) : (0 : ℝ) ≤ _)
  convert h using 1
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- The original real-Hilbert half-turn inequality is an immediate instance.
No parity assumption is needed for the inequality; for even `m` this is the
half-turn of order two. -/
theorem half_turn_real_hilbert {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (F : (ι → ZMod m) → E)
    (hm : 2 ≤ m) (hn : Fintype.card ι ≤ m ^ 2) :
    (∑ j, 𝔼 x, ‖F (x + axisHom j ((m / 2 : ℕ) : ZMod m)) - F x‖ ^ 2) ≤
      4 * (m : ℝ) ^ 2 *
        (𝔼 ε : ι → Fin 3, 𝔼 x, ‖F (x + shortShift ε) - F x‖ ^ 2) :=
  finite_torus_real_hilbert_expect F (fun _ => ((m / 2 : ℕ) : ZMod m)) hm hn

end MeasureEquivalenceTorus

#print axioms MeasureEquivalenceTorus.random_energy_multiplier
#print axioms MeasureEquivalenceTorus.torus_multiplier
#print axioms MeasureEquivalenceTorus.finite_torus_hilbert
#print axioms MeasureEquivalenceTorus.finite_torus_real_hilbert
#print axioms MeasureEquivalenceTorus.finite_torus_hilbert_expect
#print axioms MeasureEquivalenceTorus.half_turn_real_hilbert
