import GdeltaPolish
import Mathlib.Topology.Constructions.SumProd

open Set Filter Topology
open scoped Topology

noncomputable section

namespace BenchmarkJump

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def OpenFiberSquare (s : X → Y) := {p : X × X | s p.1 = s p.2}

def fiberSquareLeft (s : X → Y) (z : OpenFiberSquare s) : X := z.1.1

def fiberSquareRight (s : X → Y) (z : OpenFiberSquare s) : X := z.1.2

theorem continuous_fiberSquareLeft (s : X → Y) : Continuous (fiberSquareLeft s) :=
  continuous_fst.comp continuous_subtype_val

theorem continuous_fiberSquareRight (s : X → Y) : Continuous (fiberSquareRight s) :=
  continuous_snd.comp continuous_subtype_val

theorem isOpenMap_fiberSquareLeft (s : X → Y) (hc : Continuous s) (ho : IsOpenMap s) :
    IsOpenMap (fiberSquareLeft s) := by
  intro W hW
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨z, hzW, rfl⟩
  obtain ⟨V, hVo, hVW⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hW
  have hzV : z.1 ∈ V := by
    change z ∈ Subtype.val ⁻¹' V
    rw [hVW]
    exact hzW
  obtain ⟨A, B, hAo, hBo, hxA, hyB, hAB⟩ := isOpen_prod_iff.mp hVo z.1.1 z.1.2 hzV
  have hO : IsOpen (A ∩ s ⁻¹' (s '' B)) := hAo.inter ((ho B hBo).preimage hc)
  have hxO : fiberSquareLeft s z ∈ A ∩ s ⁻¹' (s '' B) :=
    ⟨hxA, ⟨z.1.2, hyB, z.property.symm⟩⟩
  apply mem_of_superset (hO.mem_nhds hxO)
  rintro x ⟨hxA, y, hyB, hys⟩
  refine ⟨⟨(x, y), hys.symm⟩, ?_, rfl⟩
  rw [← hVW]
  exact hAB ⟨hxA, hyB⟩

def fiberSquareSwapHomeomorph (s : X → Y) : OpenFiberSquare s ≃ₜ OpenFiberSquare s :=
  { toEquiv :=
      { toFun := fun z => ⟨(z.1.2, z.1.1), z.property.symm⟩
        invFun := fun z => ⟨(z.1.2, z.1.1), z.property.symm⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    continuous_toFun := ((continuous_snd.comp continuous_subtype_val).prodMk
      (continuous_fst.comp continuous_subtype_val)).subtype_mk _
    continuous_invFun := ((continuous_snd.comp continuous_subtype_val).prodMk
      (continuous_fst.comp continuous_subtype_val)).subtype_mk _ }

theorem isOpenMap_fiberSquareRight (s : X → Y) (hc : Continuous s) (ho : IsOpenMap s) :
    IsOpenMap (fiberSquareRight s) := by
  exact (isOpenMap_fiberSquareLeft s hc ho).comp (fiberSquareSwapHomeomorph s).isOpenMap

theorem fiberSquareLeft_surjective (s : X → Y) : Function.Surjective (fiberSquareLeft s) :=
  fun x => ⟨⟨(x, x), rfl⟩, rfl⟩

theorem fiberSquareRight_surjective (s : X → Y) : Function.Surjective (fiberSquareRight s) :=
  fun x => ⟨⟨(x, x), rfl⟩, rfl⟩

theorem isClosed_openFiberSquare [T2Space Y] (s : X → Y) (hc : Continuous s) :
    IsClosed {p : X × X | s p.1 = s p.2} :=
  isClosed_eq (hc.comp continuous_fst) (hc.comp continuous_snd)

theorem openFiberSquare_polish [PolishSpace X] [T2Space Y] (s : X → Y) (hc : Continuous s) :
    PolishSpace (OpenFiberSquare s) := (isClosed_openFiberSquare s hc).polishSpace

end BenchmarkJump
