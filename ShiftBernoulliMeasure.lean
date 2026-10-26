import ShiftNullReduction
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.Algebra.BigOperators.Fin

/-! The actual fair Bernoulli probability on the full free-group shift.
All singletons and all shift orbits are null, and shifts preserve it. -/

open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

noncomputable section

namespace BenchmarkShift

def fairLaw : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

instance fairLaw_probability : IsProbabilityMeasure fairLaw := by
  constructor
  norm_num [fairLaw, ENNReal.inv_two_add_inv_two]

lemma fairLaw_singleton (b : Bool) : fairLaw {b} = (1 / 2 : ℝ≥0∞) := by
  cases b <;> norm_num [fairLaw, Measure.dirac_apply]

def bernoulli : Measure Point := Measure.infinitePi (fun _ : Group => fairLaw)

instance bernoulli_probability : IsProbabilityMeasure bernoulli := by
  unfold bernoulli
  infer_instance

def natGroupEmbedding : ℕ ↪ Group where
  toFun n := FreeGroup.map (fun _ : Unit => (0 : Fin 2))
    (FreeGroup.freeGroupUnitEquivInt.symm (n : ℤ))
  inj' := (FreeGroup.map_injective (f := fun _ : Unit => (0 : Fin 2))
    (fun _ _ _ => Subsingleton.elim _ _)).comp
      (FreeGroup.freeGroupUnitEquivInt.symm.injective.comp Int.ofNat_injective)

lemma bernoulli_singleton_bound (x : Point) (n : ℕ) :
    bernoulli {x} ≤ (1 / 2 : ℝ≥0∞) ^ n := by
  classical
  let s : Finset Group := (Finset.range n).image natGroupEmbedding
  have hs : s.card = n := by
    rw [Finset.card_image_of_injective _ natGroupEmbedding.injective, Finset.card_range]
  have hsub : ({x} : Set Point) ⊆ Set.pi (s : Set Group) (fun g => {x g}) := by
    intro y hy
    subst y
    simp
  calc
    bernoulli {x} ≤ bernoulli (Set.pi (s : Set Group) (fun g => {x g})) := measure_mono hsub
    _ = ∏ g ∈ s, fairLaw {x g} := Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)
    _ = (1 / 2 : ℝ≥0∞) ^ n := by simp only [fairLaw_singleton, Finset.prod_const, hs]

theorem bernoulli_singleton_zero (x : Point) : bernoulli {x} = 0 := by
  have hr : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim : Tendsto (fun n : ℕ => (1 / 2 : ℝ≥0∞) ^ n) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.ofReal_zero, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using ENNReal.tendsto_ofReal hr
  exact le_antisymm (ge_of_tendsto hlim (Eventually.of_forall (bernoulli_singleton_bound x))) bot_le

instance bernoulli_noAtoms : NoAtoms bernoulli := ⟨bernoulli_singleton_zero⟩

theorem orbit_countable (x : Point) : {y | Orbit x y}.Countable := by
  have heq : {y | Orbit x y} = Set.range (fun g : Group => shift g x) := by
    ext y
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g, (funext hg).symm⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, fun _ => rfl⟩
  rw [heq]
  exact Set.countable_range _

theorem bernoulli_orbit_zero (x : Point) : bernoulli {y | Orbit x y} = 0 :=
  (orbit_countable x).measure_zero bernoulli

theorem measurePreserving_shift (g : Group) : MeasurePreserving (shift g) bernoulli bernoulli := by
  refine ⟨(continuous_shift g).measurable, ?_⟩
  have hmap := Measure.infinitePi_map_piCongrLeft (fun _ : Group => fairLaw) (Equiv.mulLeft g)
  have hfun : shift g = (MeasurableEquiv.piCongrLeft (fun _ : Group => Bool) (Equiv.mulLeft g)) := by
    funext x h
    obtain ⟨k, rfl⟩ := (Equiv.mulLeft g).surjective h
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    simp [shift]
  simpa only [← hfun, bernoulli] using hmap

end BenchmarkShift

#print axioms BenchmarkShift.bernoulli_orbit_zero
#print axioms BenchmarkShift.measurePreserving_shift
