import MeasureCantorTuple

/-! The spectral-class measure attached to an actual L² vector, expressed
without invoking a spectral theorem. Its mass on a set is the square of the
norm of the corresponding multiplication projection. -/

open MeasureTheory Filter Set
open scoped ENNReal

namespace MeasureUnitary

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

noncomputable def indicatorL2 {s : Set α} (hs : MeasurableSet s) (f : Lp E 2 μ) : Lp E 2 μ :=
  ((Lp.memLp f).indicator hs).toLp (s.indicator f)

theorem indicatorL2_coe {s : Set α} (hs : MeasurableSet s) (f : Lp E 2 μ) :
    indicatorL2 μ hs f =ᵐ[μ] s.indicator f := ((Lp.memLp f).indicator hs).coeFn_toLp

theorem l2_norm_sq_integral (f : Lp E 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext x
  exact real_inner_self_eq_norm_sq (f x)

noncomputable def vectorDensityMeasure (f : Lp E 2 μ) : Measure α :=
  μ.withDensity (fun x => ENNReal.ofReal (‖f x‖ ^ 2))

theorem vectorDensityMeasure_absolutelyContinuous (f : Lp E 2 μ) : vectorDensityMeasure μ f ≪ μ :=
  withDensity_absolutelyContinuous μ _

theorem vectorDensityMeasure_apply {s : Set α} (hs : MeasurableSet s) (f : Lp E 2 μ) :
    vectorDensityMeasure μ f s = ENNReal.ofReal (‖indicatorL2 μ hs f‖ ^ 2) := by
  apply Eq.symm
  calc
    ENNReal.ofReal (‖indicatorL2 μ hs f‖ ^ 2) =
        ∫⁻ x, ENNReal.ofReal (‖indicatorL2 μ hs f x‖ ^ 2) ∂μ := by
      rw [l2_norm_sq_integral]
      exact ofReal_integral_eq_lintegral_ofReal
        ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _))
        (.of_forall (fun x => sq_nonneg _))
    _ = ∫⁻ x in s, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
      rw [← lintegral_indicator hs]
      apply lintegral_congr_ae
      filter_upwards [indicatorL2_coe μ hs f] with x hx
      rw [hx]
      by_cases hxs : x ∈ s <;> simp [hxs]
    _ = vectorDensityMeasure μ f s := (withDensity_apply _ hs).symm

noncomputable def constantVectorL2 [IsFiniteMeasure μ] (v : E) : Lp E 2 μ :=
  (memLp_const (μ := μ) (p := 2) v).toLp (fun _ => v)

theorem constantVectorL2_coe [IsFiniteMeasure μ] (v : E) :
    constantVectorL2 μ v =ᵐ[μ] fun _ => v :=
  (memLp_const (μ := μ) (p := 2) v).coeFn_toLp

theorem constantVectorL2_density [IsFiniteMeasure μ] (v : E) (hv : ‖v‖ = 1) :
    vectorDensityMeasure μ (constantVectorL2 μ v) = μ := by
  unfold vectorDensityMeasure
  have h : (fun x => ENNReal.ofReal (‖constantVectorL2 μ v x‖ ^ 2)) =ᵐ[μ] fun _ => 1 := by
    filter_upwards [constantVectorL2_coe μ v] with x hx
    rw [hx, hv]
    norm_num
  rw [withDensity_congr_ae h]
  change μ.withDensity 1 = μ
  exact withDensity_one

noncomputable def constantOneL2 [IsFiniteMeasure μ] : Lp ℂ 2 μ :=
  (memLp_const (μ := μ) (p := 2) (1 : ℂ)).toLp (fun _ => 1)

theorem constantOneL2_coe [IsFiniteMeasure μ] : constantOneL2 μ =ᵐ[μ] fun _ => (1 : ℂ) :=
  (memLp_const (μ := μ) (p := 2) (1 : ℂ)).coeFn_toLp

theorem constantOneL2_density [IsFiniteMeasure μ] : vectorDensityMeasure μ (constantOneL2 μ) = μ := by
  unfold vectorDensityMeasure
  have h : (fun x => ENNReal.ofReal (‖constantOneL2 μ x‖ ^ 2)) =ᵐ[μ] fun _ => 1 := by
    filter_upwards [constantOneL2_coe μ] with x hx
    rw [hx]
    norm_num
  rw [withDensity_congr_ae h]
  change μ.withDensity 1 = μ
  exact withDensity_one

end MeasureUnitary

#print axioms MeasureUnitary.vectorDensityMeasure_apply
