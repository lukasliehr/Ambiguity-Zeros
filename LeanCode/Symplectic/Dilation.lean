module

public import LeanCode.Analysis.Definitions
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Haar.Unique

public section

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace AmbiguityHoles.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem dilation_map_volume (B : E ≃L[ℝ] E) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧ Measure.map B (volume : Measure E) = c • volume := by
  let μ : Measure E := Measure.map B volume
  haveI : IsAddHaarMeasure μ := B.isAddHaarMeasure_map volume
  refine ⟨(addHaarScalarFactor μ (volume : Measure E) : ℝ≥0∞), ?_, ENNReal.coe_ne_top, ?_⟩
  · exact_mod_cast addHaarScalarFactor_pos_of_isAddHaarMeasure μ (volume : Measure E)
  · exact isAddLeftInvariant_eq_smul μ volume

theorem memLp_dilation (B : E ≃L[ℝ] E) {f : E → ℂ} (hf : MemLp f 2 volume) :
    MemLp (f ∘ B) 2 volume := by
  obtain ⟨c, _, hc, hm⟩ := dilation_map_volume B
  apply B.toHomeomorph.toMeasurableEquiv.memLp_map_measure_iff.mp
  change MemLp f 2 (Measure.map B volume)
  rw [hm]
  exact hf.smul_measure hc

theorem ambiguity_dilation_zero_iff (B : E ≃L[ℝ] E) (f : E → ℂ) (x ω : E) :
    ambiguity (f ∘ B) x ω = 0 ↔
      ambiguity f (B x) (B.symm.toContinuousLinearMap.adjoint ω) = 0 := by
  obtain ⟨c, hc, hc', hm⟩ := dilation_map_volume B
  let k : E → ℂ := fun s ↦ f (s + (1 / 2 : ℝ) • B x) *
    star (f (s - (1 / 2 : ℝ) • B x)) *
    (Real.fourierChar (-(inner ℝ (B.symm.toContinuousLinearMap.adjoint ω) s)) : ℂ)
  have hk : ambiguity (f ∘ B) x ω = ∫ t, k (B t) := by
    unfold ambiguity crossAmbiguity
    congr 1
    funext t
    simp [k, ContinuousLinearMap.adjoint_inner_left]
  rw [hk]
  have hchange : (∫ t, k (B t)) = ∫ s, k s ∂Measure.map B volume :=
    (integral_map_equiv (μ := volume) B.toHomeomorph.toMeasurableEquiv k).symm
  rw [hchange, hm, integral_smul_measure, smul_eq_zero]
  exact or_iff_right (ENNReal.toReal_ne_zero.mpr ⟨hc.ne', hc'⟩)

private theorem dilation_adjoint_inverse (B : E ≃L[ℝ] E) (y : E) :
    B.toContinuousLinearMap.adjoint (B.symm.toContinuousLinearMap.adjoint y) = y := by
  have h : B.symm.toContinuousLinearMap ∘L B.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ E := by
    ext t
    exact B.symm_apply_apply t
  have h' := congrArg ContinuousLinearMap.adjoint h
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] at h'
  exact congrArg (fun A : E →L[ℝ] E ↦ A y) h'

/-- The phase-space change associated with precomposition by a linear equivalence. -/
def dilationHomeomorph (B : E ≃L[ℝ] E) : E × E ≃ₜ E × E :=
  B.toHomeomorph.prodCongr
    { toEquiv :=
        { toFun := B.symm.toContinuousLinearMap.adjoint
          invFun := B.toContinuousLinearMap.adjoint
          left_inv := dilation_adjoint_inverse B
          right_inv := dilation_adjoint_inverse B.symm }
      continuous_toFun := B.symm.toContinuousLinearMap.adjoint.continuous
      continuous_invFun := B.toContinuousLinearMap.adjoint.continuous }

theorem ambiguity_dilationHomeomorph_zero_iff (B : E ≃L[ℝ] E) (f : E → ℂ) (z : E × E) :
    ambiguity (f ∘ B) z.1 z.2 = 0 ↔
      ambiguity f (dilationHomeomorph B z).1 (dilationHomeomorph B z).2 = 0 :=
  ambiguity_dilation_zero_iff B f z.1 z.2

end AmbiguityHoles.Analysis
