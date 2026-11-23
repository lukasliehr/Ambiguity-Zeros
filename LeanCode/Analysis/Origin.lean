module

public import LeanCode.Analysis.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

public section

noncomputable section
open MeasureTheory

namespace AmbiguityHoles.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {f g : E → ℂ}

theorem ambiguity_zero_zero (hf : MemLp f 2 volume) :
    ambiguity f 0 0 = ((eLpNorm f 2 volume).toReal ^ 2 : ℝ) := by
  calc
    ambiguity f 0 0 = inner ℂ (hf.toLp f) (hf.toLp f) := by
      rw [ambiguity, crossAmbiguity_zero_zero hf hf, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with t ht
      rw [RCLike.inner_apply, ht, starRingEnd_apply]
    _ = _ := by
      rw [inner_self_eq_norm_sq_to_K, Lp.norm_toLp]
      exact (Complex.ofReal_pow _ 2).symm

theorem ambiguity_zero_zero_eq_zero_iff (hf : MemLp f 2 volume) :
    ambiguity f 0 0 = 0 ↔ f =ᵐ[volume] 0 := by
  rw [ambiguity_zero_zero hf, Complex.ofReal_eq_zero, pow_eq_zero_iff (by decide)]
  rw [ENNReal.toReal_eq_zero_iff, or_iff_left hf.eLpNorm_ne_top]
  exact eLpNorm_eq_zero_iff hf.1 (by norm_num)

private theorem ambiguity_const_mul (f : E → ℂ) (c : ℂ) (x ω : E) :
    ambiguity (fun t ↦ c * f t) x ω = (c * star c) * ambiguity f x ω := by
  unfold ambiguity crossAmbiguity
  refine Eq.trans ?_ (integral_const_mul (μ := (volume : Measure E)) (c * star c) (fun t ↦
    f (t + (1 / 2 : ℝ) • x) * star (f (t - (1 / 2 : ℝ) • x)) *
      (Real.fourierChar (-(inner ℝ ω t)) : ℂ)))
  congr with t
  rw [star_mul]
  ring

private theorem ambiguity_ae_eq {f g : E → ℂ} (h : f =ᵐ[volume] g) (x ω : E) :
    ambiguity f x ω = ambiguity g x ω := by
  unfold ambiguity crossAmbiguity
  apply integral_congr_ae
  have hadd := (measurePreserving_add_right (volume : Measure E) ((1 / 2 : ℝ) • x)).quasiMeasurePreserving
  have hsub := (measurePreserving_add_right (volume : Measure E) (-((1 / 2 : ℝ) • x))).quasiMeasurePreserving
  filter_upwards [hadd.ae h, hsub.ae h] with t ht₁ ht₂
  simpa [sub_eq_add_neg] using congrArg₂ (fun a b : ℂ ↦
    a * star b * (Real.fourierChar (-(inner ℝ ω t)) : ℂ)) ht₁ ht₂

theorem ambiguity_eq_of_ae_dependent_of_origin_eq (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume)
    (hdep : f =ᵐ[volume] 0 ∨ ∃ c : ℂ, g =ᵐ[volume] fun t ↦ c * f t)
    (h0 : ambiguity f 0 0 = ambiguity g 0 0) :
    ∀ x ω, ambiguity f x ω = ambiguity g x ω := by
  by_cases hf0 : f =ᵐ[volume] 0
  · have hg0 := (ambiguity_zero_zero_eq_zero_iff hg).mp
      (h0.symm.trans ((ambiguity_zero_zero_eq_zero_iff hf).mpr hf0))
    exact ambiguity_ae_eq (hf0.trans hg0.symm)
  · obtain ⟨c, hc⟩ := hdep.resolve_left hf0
    have hAw := (ambiguity_zero_zero_eq_zero_iff hf).not.mpr hf0
    have hprod : 1 * ambiguity f 0 0 = (c * star c) * ambiguity f 0 0 := by
      simpa [ambiguity_ae_eq hc, ambiguity_const_mul] using h0
    have hc1 := mul_right_cancel₀ hAw hprod
    intro x ω
    rw [ambiguity_ae_eq hc x ω, ambiguity_const_mul, ← hc1, one_mul]

end AmbiguityHoles.Analysis
