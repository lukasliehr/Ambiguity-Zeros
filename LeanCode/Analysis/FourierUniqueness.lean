module

public import LeanCode.Analysis.Definitions
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

public section

noncomputable section
open MeasureTheory
open scoped FourierTransform ContDiff RealInnerProductSpace

namespace AmbiguityHoles.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Fourier uniqueness on integrable functions, tested against Schwartz functions. -/
theorem integrable_fourier_eq_zero_ae (f : E → ℂ) (hf : Integrable f volume)
    (hz : 𝓕 f = 0) : f =ᵐ[volume] 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable
  intro g hg hgs
  let s := (hgs.comp_left (show Complex.ofRealCLM 0 = 0 by simp)).toSchwartzMap
    (show ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) from Complex.ofRealCLM.contDiff.comp hg)
  change (∫ t, s t * f t) = 0
  let r : SchwartzMap E ℂ := 𝓕⁻ s
  have hr : 𝓕 r = s := FourierInvPair.fourier_fourierInv_eq s
  have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
      (e := Real.fourierChar) (μ := (volume : Measure E)) (ν := volume) (L := innerₗ E)
      Real.continuous_fourierChar continuous_inner (f := (r : E → ℂ)) (g := f) r.integrable hf
  have he : (∫ t, (𝓕 (r : E → ℂ)) t * f t) = ∫ t, r t * (𝓕 f) t := by
    simpa only [Real.fourier_eq, VectorFourier.fourierIntegral, smul_eq_mul,
      ContinuousLinearMap.flip_apply, innerₗ_apply_apply, real_inner_comm] using hswap
  rw [← hr, SchwartzMap.fourier_coe, he, hz]
  simp

end AmbiguityHoles.Analysis
