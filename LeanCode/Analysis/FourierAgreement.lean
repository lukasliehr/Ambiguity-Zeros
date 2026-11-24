module

public import LeanCode.Analysis.Definitions
public import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.TemperedDistribution

public section

noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap ENNReal ContDiff RealInnerProductSpace

namespace AmbiguityHoles.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem fourier_tempered (u : Lp (α := E) ℂ 2 volume) :
    Lp.toTemperedDistribution (𝓕 u) = 𝓕 (Lp.toTemperedDistribution u) :=
  (Lp.fourier_toTemperedDistribution_eq u).symm

/-- The Plancherel transform agrees almost everywhere with the integral Fourier transform on
functions in both spaces. -/
theorem fourier_toLp_ae {f : E → ℂ} (h1 : Integrable f) (h2 : MemLp f 2) :
    (𝓕 (h2.toLp f) : Lp (α := E) ℂ 2 volume) =ᵐ[volume] 𝓕 f := by
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ h1
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 (h2.toLp f))).locallyIntegrable (by norm_num)) hcont.locallyIntegrable
  intro g hg hs
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let s := (hs.comp_left (show Complex.ofRealCLM 0 = 0 by simp)).toSchwartzMap hg'
  have he := congrArg (fun d => d s) (fourier_tempered (h2.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at he
  change (∫ x, s x • (𝓕 (h2.toLp f) : Lp (α := E) ℂ 2 volume) x) = ∫ x, s x • 𝓕 f x
  rw [he]
  calc
    _ = ∫ x, (𝓕 s) x • f x :=
      integral_congr_ae (h2.coeFn_toLp.mono fun x hx => by rw [hx])
    _ = _ := by
      simp only [smul_eq_mul, SchwartzMap.fourier_coe]
      simpa only [Real.fourier_eq, VectorFourier.fourierIntegral, smul_eq_mul, mul_comm,
        ContinuousLinearMap.flip_apply, LinearMap.flip_apply, innerₗ_apply_apply,
        real_inner_comm] using
        (VectorFourier.integral_fourierIntegral_smul_eq_flip
          (L := innerₗ E) Real.continuous_fourierChar continuous_inner h1 s.integrable).symm

end AmbiguityHoles.Analysis
