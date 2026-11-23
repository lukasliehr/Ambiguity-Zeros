import LeanCode.GaussianObstruction
import AmbiguityZeros.ToMathlib.STFT
import Mathlib.Tactic.LinearCombination

/-! The spectrogram identity `symplecticFourier_stft_sq`, applied to the ambiguity density. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace AmbiguityHoles.GaussianObstruction

open AmbiguityZeros.ToMathlib

def density (f : ℝ → ℂ) (z : Plane) : ℂ :=
  ((‖ambiguity f z.fst z.snd‖ ^ 2 : ℝ) : ℂ)

theorem stft_self_norm {f : ℝ → ℂ} (hf : MemLp f 2 volume) (x ω : ℝ) :
    ‖stft f f x ω‖ = ‖ambiguity f x ω‖ := by
  rw [stft_eq_crossAmbiguity hf hf]
  simp [ambiguity]

theorem density_continuous {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    Continuous (density f) := by
  have h := (ambiguity_continuous hf).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).continuous
  exact (Complex.continuous_ofReal.comp (h.norm.pow 2))

theorem density_integrable {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    Integrable (density f) := by
  have h := stft_sq_complex_integrable hf hf
  simp_rw [stft_self_norm hf] at h
  exact ((WithLp.volume_preserving_ofLp ℝ ℝ).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (ℝ × ℝ)).symm.measurableEmbedding).2 h

theorem fourier_rotation_eq_symplectic {F : Plane → ℂ} (hF : Integrable F) (z : Plane) :
    𝓕 F (rotation z) =
      symplecticFourier (fun x ω ↦ F (WithLp.toLp 2 (x, ω))) z.fst z.snd := by
  rw [Real.fourier_eq, ← (WithLp.volume_preserving_toLp ℝ ℝ).integral_comp
    (MeasurableEquiv.toLp 2 (ℝ × ℝ)).measurableEmbedding]
  have hint := ((WithLp.volume_preserving_toLp ℝ ℝ).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (ℝ × ℝ)).measurableEmbedding).2
    ((Real.fourierIntegral_convergent_iff (rotation z)).2 hF)
  change (∫ p : ℝ × ℝ, Real.fourierChar (-inner ℝ (WithLp.toLp 2 p) (rotation z)) •
    F (WithLp.toLp 2 p) ∂(volume.prod volume)) = _
  rw [integral_prod _ (by simpa only [Function.comp_def] using hint)]
  unfold symplecticFourier
  apply integral_congr_ae
  filter_upwards [] with x
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [Circle.smul_def]
  change (Real.fourierChar (-(z.snd * x + (-z.fst) * ω)) : ℂ) * F (WithLp.toLp 2 (x, ω)) = _
  rw [mul_comm]
  rw [show -(z.snd * x + (-z.fst) * ω) = -(z.snd * x - z.fst * ω) by ring]

theorem density_fixed {f : ℝ → ℂ} (hf : MemLp f 2 volume) (z : Plane) :
    𝓕 (density f) (rotation z) = density f z := by
  rw [fourier_rotation_eq_symplectic (density_integrable hf)]
  have h := symplecticFourier_stft_sq hf hf z.fst z.snd
  simp_rw [stft_self_norm hf] at h
  convert h using 1
  simp [density, Complex.mul_conj', Complex.ofReal_pow]

theorem density_zero_pos {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hne : ¬ f =ᵐ[volume] 0) : 0 < (density f 0).re := by
  have hn : eLpNorm f 2 volume ≠ 0 :=
    fun h ↦ hne ((eLpNorm_eq_zero_iff hf.aestronglyMeasurable (by norm_num)).1 h)
  have hp := ENNReal.toReal_pos hn hf.eLpNorm_ne_top
  change 0 < ‖ambiguity f 0 0‖ ^ 2
  rw [ambiguity_zero_zero hf]
  exact sq_pos_of_pos (norm_pos_iff.mpr
    (Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 hp.ne')))

theorem density_certificate_integrable {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    Integrable (fun z ↦ density f z * certificate z) := by
  apply (density_integrable hf).mul_bdd certificate_continuous.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  have hb := VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar
    (volume : Measure Plane) (innerₗ Plane) certificate z
  change ‖𝓕 certificate z‖ ≤ _ at hb
  simpa only [fourier_certificate, Pi.neg_apply, norm_neg] using hb

theorem density_certificate_orthogonal {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    ∫ z, density f z * certificate z = 0 := by
  have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (L := innerₗ Plane) Real.continuous_fourierChar
    (by simpa using (continuous_fst.inner continuous_snd :
      Continuous fun p : Plane × Plane ↦ inner ℝ p.1 p.2))
    (density_integrable hf) certificate_integrable
  change (∫ z, 𝓕 (density f) z * certificate z) = _ at hswap
  simp only [flip_innerₗ] at hswap
  change (∫ z, 𝓕 (density f) z * certificate z) =
    ∫ z, density f z * 𝓕 certificate z at hswap
  have hrot := rotation.measurePreserving.integral_comp
    rotation.toMeasurableEquiv.measurableEmbedding
    (fun z ↦ 𝓕 (density f) z * certificate z)
  simp only [density_fixed hf, certificate_rotation] at hrot
  rw [← hrot] at hswap
  simp only [fourier_certificate, Pi.neg_apply, mul_neg, integral_neg] at hswap
  linear_combination (1 / 2 : ℂ) * hswap

end AmbiguityHoles.GaussianObstruction
