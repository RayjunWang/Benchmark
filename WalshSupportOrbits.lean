import WalshShiftAction
import Mathlib.GroupTheory.GroupAction.Defs

/-! Nonconstant Walsh supports form a disjoint union of free regular
orbits. The displayed inverse coordinate map sends `(q,g)` to `g • q.out`. -/

noncomputable section

namespace BenchmarkShift

abbrev NonemptySupport := {S : Finset Group // S.Nonempty}

instance supportMulAction : MulAction Group NonemptySupport where
  smul g S := ⟨supportTranslate g S, S.property.image _⟩
  one_smul := by
    intro S
    apply Subtype.ext
    change supportTranslate 1 S.val = S.val
    ext a
    simp only [supportTranslate, Finset.mem_image, one_mul]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hb
    · intro ha
      exact ⟨a, ha, rfl⟩
  mul_smul := by
    intro g h S
    apply Subtype.ext
    change supportTranslate (g * h) S.val = supportTranslate g (supportTranslate h S.val)
    simp only [supportTranslate, Finset.image_image, Function.comp_def, mul_assoc]

lemma support_smul_faithful (g : Group) (S : NonemptySupport) (h : g • S = S) : g = 1 :=
  supportTranslate_faithful S S.property g (congrArg Subtype.val h)

lemma support_right_cancel (g h : Group) (S : NonemptySupport) (heq : g • S = h • S) : g = h := by
  have hfix : (h⁻¹ * g) • S = S := by rw [mul_smul, heq, inv_smul_smul]
  have hh := support_smul_faithful (h⁻¹ * g) S hfix
  exact (inv_mul_eq_one.mp hh).symm

abbrev SupportOrbit := Quotient (MulAction.orbitRel Group NonemptySupport)

local instance : Setoid NonemptySupport := MulAction.orbitRel Group NonemptySupport

def regularOrbitMap (p : SupportOrbit × Group) : NonemptySupport := p.2 • p.1.out

lemma support_class_smul (g : Group) (S : NonemptySupport) :
    (Quotient.mk' (g • S) : SupportOrbit) = Quotient.mk' S := by
  apply Quotient.sound
  apply MulAction.orbitRel_apply.mpr
  exact ⟨g, rfl⟩

theorem regularOrbitMap_bijective : Function.Bijective regularOrbitMap := by
  constructor
  · rintro ⟨q, g⟩ ⟨r, h⟩ heq
    have hclass := congrArg (fun S => (Quotient.mk' S : SupportOrbit)) heq
    have hqr : q = r := by
      have hclass' : (Quotient.mk' q.out : SupportOrbit) = Quotient.mk' r.out := by
        simpa only [regularOrbitMap, support_class_smul] using hclass
      have hq : (Quotient.mk' q.out : SupportOrbit) = q := Quotient.out_eq q
      have hr : (Quotient.mk' r.out : SupportOrbit) = r := Quotient.out_eq r
      exact hq.symm.trans (hclass'.trans hr)
    subst r
    have hgh : g = h := support_right_cancel g h q.out heq
    exact Prod.ext rfl hgh
  · intro S
    let q : SupportOrbit := Quotient.mk' S
    have hq : (Quotient.mk' q.out : SupportOrbit) = Quotient.mk' S := Quotient.out_eq q
    have hr := MulAction.orbitRel_apply.mp (Quotient.exact hq.symm)
    obtain ⟨g, hg⟩ := hr
    exact ⟨(q, g), hg⟩

def supportOrbitEquiv : NonemptySupport ≃ SupportOrbit × Group :=
  (Equiv.ofBijective regularOrbitMap regularOrbitMap_bijective).symm

@[simp] lemma supportOrbitEquiv_symm_apply (q : SupportOrbit) (g : Group) :
    supportOrbitEquiv.symm (q, g) = g • q.out := rfl

theorem supportOrbitEquiv_symm_mul (q : SupportOrbit) (g h : Group) :
    supportOrbitEquiv.symm (q, g * h) = g • supportOrbitEquiv.symm (q, h) := by
  simp only [supportOrbitEquiv_symm_apply, mul_smul]

end BenchmarkShift

#print axioms BenchmarkShift.supportOrbitEquiv
