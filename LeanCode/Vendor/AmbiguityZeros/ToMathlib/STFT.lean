import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import AmbiguityZeros.ToMathlib.Ambiguity
import AmbiguityZeros.ToMathlib.TranslationModulation

namespace AmbiguityZeros.ToMathlib

noncomputable section

open MeasureTheory
open Filter
open scoped ComplexConjugate

variable {w u v : ℝ → ℂ}

def stft (w u : ℝ → ℂ) (x ω : ℝ) : ℂ :=
  ∫ t, u t * star (w (t - x)) * (Real.fourierChar (-(ω * t)) : ℂ)

theorem stft_eq_crossAmbiguity (hw : MemLp w 2 volume) (hu : MemLp u 2 volume)
    (x ω : ℝ) :
    stft w u x ω = (Real.fourierChar (-(ω * x / 2)) : ℂ) * crossAmbiguity u w x ω := by
  rw [stft, crossAmbiguity_eq_integral (f := u) (g := w) hu hw x ω]
  have hrew :
      ∫ t, u t * star (w (t - x)) * (Real.fourierChar (-(ω * t)) : ℂ) =
        ∫ t, u t * star (modulate ω (translate x w) t) := by
    simp [modulate, translate, mul_assoc, mul_comm]
  rw [hrew]
  have hcancel :
      (Real.fourierChar (-(ω * x / 2)) : ℂ) *
        (Real.fourierChar (ω * x / 2) : ℂ) = 1 := by
    rw [Real.fourierChar_apply, Real.fourierChar_apply, ← Complex.exp_add]
    simp [mul_comm, mul_left_comm]
  rw [← mul_assoc, hcancel, one_mul]

theorem stft_zero_window (_hu : MemLp u 2 volume) (x ω : ℝ) :
    stft 0 u x ω = 0 := by
  simp [stft]

theorem stft_zero_signal (_hw : MemLp w 2 volume) (x ω : ℝ) :
    stft w 0 x ω = 0 := by
  simp [stft]

theorem stft_integrand_integrable
    (hw : MemLp w 2 volume) (hu : MemLp u 2 volume) (x ω : ℝ) :
    Integrable (fun t ↦ u t * star (w (t - x)) * (Real.fourierChar (-(ω * t)) : ℂ))
      volume := by
  have hslice : Integrable (fun t ↦ u t * star (w (t - x))) volume := by
    simpa [translate] using
      integrable_mul_of_memLp hu (conj_memLp (translate_memLp x hw))
  have hmeas : AEStronglyMeasurable (fun t ↦ (Real.fourierChar (-(ω * t)) : ℂ)) volume := by
    fun_prop
  have hbound : ∀ᵐ t ∂volume, ‖(Real.fourierChar (-(ω * t)) : ℂ)‖ ≤ (1 : ℝ) := by
    filter_upwards [Filter.Eventually.of_forall (fun t ↦ norm_fourierChar (-(ω * t)))] with t ht
    exact le_of_eq ht
  simpa [mul_assoc] using hslice.mul_bdd hmeas hbound

theorem stft_slice_aestronglyMeasurable
    (hw : AEStronglyMeasurable w volume) (hu : AEStronglyMeasurable u volume)
    (x : ℝ) :
    AEStronglyMeasurable (fun t ↦ u t * star (w (t - x))) volume := by
  simpa [translate] using
    hu.mul (conj_aestronglyMeasurable (translate_aestronglyMeasurable x hw))

theorem stft_slice_integrable (hw : MemLp w 2 volume) (hu : MemLp u 2 volume) (x : ℝ) :
    Integrable (fun t ↦ u t * star (w (t - x))) volume := by
  simpa [translate] using
    integrable_mul_of_memLp hu (conj_memLp (translate_memLp x hw))

theorem stft_eq_fourierIntegral (_hw : MemLp w 2 volume) (_hu : MemLp u 2 volume) (x : ℝ) :
    stft w u x = FourierTransform.fourier (fun t ↦ u t * star (w (t - x))) := by
  ext ω
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp [stft, Real.fourierChar_apply, mul_neg, neg_mul, mul_assoc, mul_left_comm,
    mul_comm]

theorem stft_eq_fourierIntegral_apply
    (hw : MemLp w 2 volume) (hu : MemLp u 2 volume) (x ω : ℝ) :
    stft w u x ω = FourierTransform.fourier (fun t ↦ u t * star (w (t - x))) ω := by
  simpa using congrArg (fun f : ℝ → ℂ => f ω) (stft_eq_fourierIntegral (w := w) (u := u) hw hu x)

private def stftWindowSchwartz (x : ℝ) (w : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) (F := ℂ) (G := ℂ) Complex.conjCLE
    (w.compSubConstCLM ℂ x)

@[simp] private theorem stftWindowSchwartz_apply
    (x t : ℝ) (w : SchwartzMap ℝ ℂ) :
    stftWindowSchwartz x w t = star (w (t - x)) := by
  simp [stftWindowSchwartz, Complex.conjCLE_apply]

private def stftSliceSchwartz (w u : SchwartzMap ℝ ℂ) (x : ℝ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ)
    (stftWindowSchwartz x w).hasTemperateGrowth u

@[simp] private theorem stftSliceSchwartz_apply
    (w u : SchwartzMap ℝ ℂ) (x t : ℝ) :
    stftSliceSchwartz w u x t = u t * star (w (t - x)) := by
  simp [stftSliceSchwartz]

theorem stft_eq_fourierIntegral_schwartz (w u : SchwartzMap ℝ ℂ) (x : ℝ) :
    stft w u x = FourierTransform.fourier (fun t ↦ stftSliceSchwartz w u x t) := by
  ext ω
  simpa [stftSliceSchwartz_apply] using
    stft_eq_fourierIntegral_apply (w := (w : ℝ → ℂ)) (u := (u : ℝ → ℂ))
      (hw := w.memLp 2 volume) (hu := u.memLp 2 volume) x ω

theorem stft_eq_fourierIntegral_schwartz_apply
    (w u : SchwartzMap ℝ ℂ) (x ω : ℝ) :
    stft w u x ω = FourierTransform.fourier (fun t ↦ stftSliceSchwartz w u x t) ω := by
  simpa using congrArg (fun f : ℝ → ℂ => f ω) (stft_eq_fourierIntegral_schwartz w u x)

private theorem integral_norm_sq_stft_slice_schwartz
    (w u : SchwartzMap ℝ ℂ) (x : ℝ) :
    ∫ ω, ‖stft w u x ω‖ ^ 2 = ∫ t, ‖stftSliceSchwartz w u x t‖ ^ 2 := by
  rw [stft_eq_fourierIntegral_schwartz w u x]
  simpa using SchwartzMap.integral_norm_sq_fourier (stftSliceSchwartz w u x)

private theorem stft_slice_parseval_shift_schwartz
    (w u : SchwartzMap ℝ ℂ) (x y : ℝ) :
    ∫ η, inner ℂ (modulate (-x / 2) (FourierTransform.fourier (stftSliceSchwartz w u y)) η)
        (modulate (x / 2) (FourierTransform.fourier (stftSliceSchwartz w u y)) η) =
      ∫ t, inner ℂ (translate (x / 2) (stftSliceSchwartz w u y) t)
        (translate (-x / 2) (stftSliceSchwartz w u y) t) := by
  let s : SchwartzMap ℝ ℂ := stftSliceSchwartz w u y
  have h :
      ∫ η, inner ℂ (FourierTransform.fourier (s.compSubConstCLM ℂ (x / 2)) η)
          (FourierTransform.fourier (s.compSubConstCLM ℂ (-x / 2)) η) =
        ∫ t, inner ℂ (s.compSubConstCLM ℂ (x / 2) t) (s.compSubConstCLM ℂ (-x / 2) t) := by
    simpa using
      (SchwartzMap.integral_sesq_fourier_fourier
        (f := s.compSubConstCLM ℂ (x / 2))
        (g := s.compSubConstCLM ℂ (-x / 2))
        (M := innerSL ℂ))
  rw [fourier_compSubConstCLM_eq_modulate (f := s) (x := x / 2),
    fourier_compSubConstCLM_eq_modulate (f := s) (x := -x / 2)] at h
  simpa [s, SchwartzMap.compSubConstCLM_apply, stftSliceSchwartz_apply, modulate, translate,
    mul_assoc, mul_left_comm, mul_comm] using h

private theorem stft_continuous_schwartz (w u : SchwartzMap ℝ ℂ) :
    Continuous (fun p : ℝ × ℝ ↦ stft w u p.1 p.2) := by
  have hw : MemLp (w : ℝ → ℂ) 2 volume := w.memLp 2 volume
  have hu : MemLp (u : ℝ → ℂ) 2 volume := u.memLp 2 volume
  have hcont1 : Continuous (fun p : ℝ × ℝ ↦ (Real.fourierChar (-(p.2 * p.1 / 2)) : ℂ)) := by
    exact (continuous_subtype_val.comp
      (by simpa using
        (Real.continuous_fourierChar.comp
          (by fun_prop : Continuous fun p : ℝ × ℝ ↦ -(p.2 * p.1 / 2)))))
  have hcont2 : Continuous (fun p : ℝ × ℝ ↦ crossAmbiguity u w p.1 p.2) :=
    crossAmbiguity_continuous (f := (u : ℝ → ℂ)) (g := (w : ℝ → ℂ)) hu hw
  have hcont : Continuous (fun p : ℝ × ℝ ↦
      (Real.fourierChar (-(p.2 * p.1 / 2)) : ℂ) * crossAmbiguity u w p.1 p.2) := hcont1.mul hcont2
  have hEq : (fun p : ℝ × ℝ ↦ stft w u p.1 p.2) =
      fun p : ℝ × ℝ ↦ (Real.fourierChar (-(p.2 * p.1 / 2)) : ℂ) * crossAmbiguity u w p.1 p.2 := by
    funext p
    simpa [stft] using stft_eq_crossAmbiguity (w := (w : ℝ → ℂ)) (u := (u : ℝ → ℂ)) hw hu p.1 p.2
  rw [hEq]
  exact hcont

private theorem integrable_norm_sq_schwartz (f : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ ↦ ‖f x‖ ^ 2) volume := by
  exact
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (μ := volume) (f := (f : ℝ → ℂ)) f.continuous.aestronglyMeasurable).mp (f.memLp 2 volume)

private theorem integral_norm_sq_eq_eLpNorm_sq {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    ∫ t, ‖f t‖ ^ 2 = (eLpNorm f 2 volume).toReal ^ 2 := by
  have h := hf.eLpNorm_eq_integral_rpow_norm (μ := volume) (p := (2 : ENNReal))
    (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)
  norm_num at h
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_ofReal (by positivity)] at h'
  have h'' := congrArg (fun x : ℝ => x ^ 2) h'
  have hpow :
      ((∫ t, ‖f t‖ ^ 2 : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = ∫ t, ‖f t‖ ^ 2 := by
    by_cases hzero : (∫ t, ‖f t‖ ^ 2 : ℝ) = 0
    · simp [hzero]
    · have hx0 : 0 ≤ (∫ t, ‖f t‖ ^ 2 : ℝ) := by positivity
      have hx : 0 < (∫ t, ‖f t‖ ^ 2 : ℝ) := lt_of_le_of_ne hx0 (by simpa [eq_comm] using hzero)
      have hmul := Real.rpow_add hx (1 / 2) (1 / 2)
      norm_num at hmul
      simpa [sq] using hmul.symm
  simpa [sq] using (h''.trans hpow).symm

private theorem integrable_norm_sq_neg_schwartz (w : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ ↦ ‖w (-x)‖ ^ 2) volume := by
  simpa using (integrable_norm_sq_schwartz w).comp_neg

private theorem integrable_norm_sq_translate_sub_schwartz
    (w : SchwartzMap ℝ ℂ) (t : ℝ) :
    Integrable (fun x : ℝ ↦ ‖w (t - x)‖ ^ 2) volume := by
  simpa [sub_eq_add_neg] using (integrable_norm_sq_neg_schwartz w).comp_sub_right t

private theorem integral_norm_sq_translate_sub_schwartz
    (w : SchwartzMap ℝ ℂ) (t : ℝ) :
    ∫ x, ‖w (t - x)‖ ^ 2 = ∫ x, ‖w x‖ ^ 2 := by
  calc
    ∫ x, ‖w (t - x)‖ ^ 2 = ∫ x, ‖w (-x)‖ ^ 2 := by
      simpa [sub_eq_add_neg] using
        (integral_sub_right_eq_self (μ := (volume : Measure ℝ))
          (f := fun x : ℝ ↦ ‖w (-x)‖ ^ 2) t)
    _ = ∫ x, ‖w x‖ ^ 2 := by
      simpa using
        (integral_neg_eq_self (μ := (volume : Measure ℝ)) (f := fun x : ℝ ↦ ‖w x‖ ^ 2))

private theorem integral_stft_kernel_slice_schwartz
    (w u : SchwartzMap ℝ ℂ) (t : ℝ) :
    ∫ x, ‖u t‖ ^ 2 * ‖w (t - x)‖ ^ 2 =
      ‖u t‖ ^ 2 * ∫ x, ‖w x‖ ^ 2 := by
  calc
    ∫ x, ‖u t‖ ^ 2 * ‖w (t - x)‖ ^ 2
        = ‖u t‖ ^ 2 * ∫ x, ‖w (t - x)‖ ^ 2 := by
            simpa using
              (MeasureTheory.integral_const_mul
                (r := ‖u t‖ ^ 2) (f := fun x : ℝ ↦ ‖w (t - x)‖ ^ 2))
    _ = ‖u t‖ ^ 2 * ∫ x, ‖w x‖ ^ 2 := by
          rw [integral_norm_sq_translate_sub_schwartz w t]

private theorem integrable_stft_kernel_schwartz
    (w u : SchwartzMap ℝ ℂ) :
    Integrable (fun p : ℝ × ℝ ↦ ‖u p.1‖ ^ 2 * ‖w (p.1 - p.2)‖ ^ 2) (volume.prod volume) := by
  let K : ℝ × ℝ → ℝ := fun p ↦ ‖u p.1‖ ^ 2 * ‖w (p.1 - p.2)‖ ^ 2
  have hK_meas : AEStronglyMeasurable K (volume.prod volume) := by
    exact (by fun_prop : Measurable K).aestronglyMeasurable
  refine (MeasureTheory.integrable_prod_iff hK_meas).2 ?_
  constructor
  · refine Filter.Eventually.of_forall ?_
    intro t
    have hw_slice : Integrable (fun x : ℝ ↦ ‖w (t - x)‖ ^ 2) volume :=
      integrable_norm_sq_translate_sub_schwartz w t
    simpa [K, mul_comm] using hw_slice.const_mul (‖u t‖ ^ 2)
  · have hu_sq : Integrable (fun t : ℝ ↦ ‖u t‖ ^ 2) volume := integrable_norm_sq_schwartz u
    have h_outer :
        (fun t : ℝ => ∫ x, ‖K (t, x)‖ ∂volume) =
          fun t : ℝ => ‖u t‖ ^ 2 * ∫ x, ‖w x‖ ^ 2 := by
      funext t
      calc
        ∫ x, ‖K (t, x)‖
            = ∫ x, ‖u t‖ ^ 2 * ‖w (t - x)‖ ^ 2 := by
                refine integral_congr_ae ?_
                filter_upwards with x
                simp [K]
        _ = ‖u t‖ ^ 2 * ∫ x, ‖w x‖ ^ 2 := by
              exact integral_stft_kernel_slice_schwartz w u t
    rw [h_outer]
    simpa [mul_comm] using hu_sq.const_mul (∫ x, ‖w x‖ ^ 2)

private theorem integrable_stft_sq_slice_schwartz
    (w u : SchwartzMap ℝ ℂ) (x : ℝ) :
    Integrable (fun ω : ℝ ↦ ‖stft w u x ω‖ ^ 2) volume := by
  have h_fourier :
      Integrable
        (fun ω : ℝ ↦ ‖(FourierTransform.fourier (stftSliceSchwartz w u x)) ω‖ ^ 2)
        volume := by
    exact integrable_norm_sq_schwartz (FourierTransform.fourier (stftSliceSchwartz w u x))
  simpa [stft_eq_fourierIntegral_schwartz w u x] using h_fourier

private theorem crossAmbiguity_le_lpNorm
    {f g : ℝ → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (x ω : ℝ) :
    ‖crossAmbiguity f g x ω‖ ≤ lpNorm f 2 volume * lpNorm g 2 volume := by
  simpa [MeasureTheory.toReal_eLpNorm hf.aestronglyMeasurable,
    MeasureTheory.toReal_eLpNorm hg.aestronglyMeasurable] using
    crossAmbiguity_le (f := f) (g := g) hf hg x ω

private theorem norm_stft_sub_le_lpNorm
    {w₁ w₂ u₁ u₂ : ℝ → ℂ}
    (hw₁ : MemLp w₁ 2 volume) (hw₂ : MemLp w₂ 2 volume)
    (hu₁ : MemLp u₁ 2 volume) (hu₂ : MemLp u₂ 2 volume)
    (x ω : ℝ) :
    ‖stft w₁ u₁ x ω - stft w₂ u₂ x ω‖ ≤
      lpNorm (u₁ - u₂) 2 volume * lpNorm w₁ 2 volume +
        lpNorm u₂ 2 volume * lpNorm (w₁ - w₂) 2 volume := by
  let phase : ℂ := (Real.fourierChar (-(ω * x / 2)) : ℂ)
  have hwsub : MemLp (w₁ - w₂) 2 volume := hw₁.sub hw₂
  have husub : MemLp (u₁ - u₂) 2 volume := hu₁.sub hu₂
  have hphase₁ := stft_eq_crossAmbiguity (w := w₁) (u := u₁) hw₁ hu₁ x ω
  have hphase₂ := stft_eq_crossAmbiguity (w := w₂) (u := u₂) hw₂ hu₂ x ω
  calc
    ‖stft w₁ u₁ x ω - stft w₂ u₂ x ω‖
        = ‖crossAmbiguity u₁ w₁ x ω - crossAmbiguity u₂ w₂ x ω‖ := by
            rw [hphase₁, hphase₂]
            calc
              ‖phase * crossAmbiguity u₁ w₁ x ω - phase * crossAmbiguity u₂ w₂ x ω‖
                  = ‖phase * (crossAmbiguity u₁ w₁ x ω - crossAmbiguity u₂ w₂ x ω)‖ := by
                      ring_nf
              _ = ‖crossAmbiguity u₁ w₁ x ω - crossAmbiguity u₂ w₂ x ω‖ := by
                    simp [phase]
    _ ≤ ‖crossAmbiguity (u₁ - u₂) w₁ x ω‖ + ‖crossAmbiguity u₂ (w₁ - w₂) x ω‖ := by
          have hsplit :
              crossAmbiguity u₁ w₁ x ω - crossAmbiguity u₂ w₂ x ω =
                crossAmbiguity (u₁ - u₂) w₁ x ω + crossAmbiguity u₂ (w₁ - w₂) x ω := by
            calc
              crossAmbiguity u₁ w₁ x ω - crossAmbiguity u₂ w₂ x ω
                  = (crossAmbiguity u₁ w₁ x ω - crossAmbiguity u₂ w₁ x ω) +
                      (crossAmbiguity u₂ w₁ x ω - crossAmbiguity u₂ w₂ x ω) := by
                        ring
              _ = crossAmbiguity (u₁ - u₂) w₁ x ω + crossAmbiguity u₂ (w₁ - w₂) x ω := by
                    rw [← crossAmbiguity_sub_left hu₁ hu₂ hw₁ x ω,
                      ← crossAmbiguity_sub_right hu₂ hw₁ hw₂ x ω]
          rw [hsplit]
          exact norm_add_le _ _
    _ ≤ lpNorm (u₁ - u₂) 2 volume * lpNorm w₁ 2 volume +
          lpNorm u₂ 2 volume * lpNorm (w₁ - w₂) 2 volume := by
          exact add_le_add
            (crossAmbiguity_le_lpNorm husub hw₁ x ω)
            (crossAmbiguity_le_lpNorm hu₂ hwsub x ω)

private theorem exists_schwartz_lpNorm_sub_le
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : SchwartzMap ℝ ℂ, lpNorm (f - (s : ℝ → ℂ)) 2 volume ≤ ε := by
  obtain ⟨g, hg₁, hg₂, hg₃⟩ :=
    MeasureTheory.MemLp.exist_eLpNorm_sub_le (μ := volume) (p := (2 : ENNReal))
      (by norm_num : (2 : ENNReal) ≠ ⊤) (by norm_num : 1 ≤ (2 : ENNReal)) hf hε
  let s : SchwartzMap ℝ ℂ := hg₁.toSchwartzMap hg₂
  have hs : MemLp (f - (s : ℝ → ℂ)) 2 volume := hf.sub (s.memLp 2 volume)
  have hg₃' : eLpNorm (f - (s : ℝ → ℂ)) 2 volume ≤ ENNReal.ofReal ε := by
    simpa [s] using hg₃
  refine ⟨s, ?_⟩
  rw [← MeasureTheory.toReal_eLpNorm hs.aestronglyMeasurable]
  exact (ENNReal.toReal_le_toReal hs.eLpNorm_ne_top (by simp)).mpr hg₃' |>.trans_eq
    (ENNReal.toReal_ofReal hε.le)

private noncomputable def schwartzApprox
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) (n : ℕ) : SchwartzMap ℝ ℂ :=
  Classical.choose <|
    exists_schwartz_lpNorm_sub_le (f := f) hf
      (ε := 1 / ((n : ℝ) + 1)) (by positivity)

private theorem schwartzApprox_lpNorm_sub_le
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) (n : ℕ) :
    lpNorm (f - (schwartzApprox hf n : ℝ → ℂ)) 2 volume ≤ 1 / ((n : ℝ) + 1) :=
  Classical.choose_spec <|
    exists_schwartz_lpNorm_sub_le (f := f) hf
      (ε := 1 / ((n : ℝ) + 1)) (by positivity)

private theorem schwartzApprox_lpNorm_le
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) (n : ℕ) :
    lpNorm (schwartzApprox hf n : ℝ → ℂ) 2 volume ≤
      lpNorm f 2 volume + 1 / ((n : ℝ) + 1) := by
  have hs : MemLp (schwartzApprox hf n : ℝ → ℂ) 2 volume := (schwartzApprox hf n).memLp 2 volume
  have hsub : MemLp (f - (schwartzApprox hf n : ℝ → ℂ)) 2 volume := hf.sub hs
  calc
    lpNorm (schwartzApprox hf n : ℝ → ℂ) 2 volume
        = lpNorm (f - (f - (schwartzApprox hf n : ℝ → ℂ))) 2 volume := by
            congr 1
            funext t
            simp
    _ ≤ lpNorm f 2 volume + lpNorm (f - (schwartzApprox hf n : ℝ → ℂ)) 2 volume := by
          exact lpNorm_sub_le (f := f) (g := f - (schwartzApprox hf n : ℝ → ℂ)) hf (by norm_num)
    _ ≤ lpNorm f 2 volume + 1 / ((n : ℝ) + 1) := by
          gcongr
          exact schwartzApprox_lpNorm_sub_le hf n

private theorem schwartzApprox_lpNorm_le_add_one
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) (n : ℕ) :
    lpNorm (schwartzApprox hf n : ℝ → ℂ) 2 volume ≤ lpNorm f 2 volume + 1 := by
  refine le_trans (schwartzApprox_lpNorm_le hf n) ?_
  gcongr
  have hnat : 0 ≤ (n : ℝ) := by positivity
  have hdenom : (1 : ℝ) ≤ (n : ℝ) + 1 := by nlinarith
  simpa using one_div_le_one_div_of_le (by positivity : 0 < (1 : ℝ)) hdenom

private theorem schwartzApprox_tendsto_lpNorm_sub_zero
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    Tendsto (fun n : ℕ ↦ lpNorm (f - (schwartzApprox hf n : ℝ → ℂ)) 2 volume) atTop (nhds 0) := by
  have hε :
      Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0) := by
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0))
  exact squeeze_zero (fun n => MeasureTheory.lpNorm_nonneg) (schwartzApprox_lpNorm_sub_le hf) hε

private theorem schwartzApprox_tendsto_lpNorm
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    Tendsto (fun n : ℕ ↦ lpNorm (schwartzApprox hf n : ℝ → ℂ) 2 volume) atTop
      (nhds (lpNorm f 2 volume)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hε :
      Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0) := by
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0))
  have hbound :
      ∀ n : ℕ,
        |lpNorm (schwartzApprox hf n : ℝ → ℂ) 2 volume - lpNorm f 2 volume| ≤
          1 / ((n : ℝ) + 1) := by
    intro n
    have hs : MemLp (schwartzApprox hf n : ℝ → ℂ) 2 volume := (schwartzApprox hf n).memLp 2 volume
    have h₁ :
        lpNorm (schwartzApprox hf n : ℝ → ℂ) 2 volume ≤
          lpNorm f 2 volume + 1 / ((n : ℝ) + 1) :=
      schwartzApprox_lpNorm_le hf n
    have h₂ :
        lpNorm f 2 volume ≤
          lpNorm (schwartzApprox hf n : ℝ → ℂ) 2 volume + 1 / ((n : ℝ) + 1) := by
      calc
        lpNorm f 2 volume
            = lpNorm ((schwartzApprox hf n : ℝ → ℂ) -
                ((schwartzApprox hf n : ℝ → ℂ) - f)) 2 volume := by
                  congr 1
                  funext t
                  simp
        _ ≤ lpNorm (schwartzApprox hf n : ℝ → ℂ) 2 volume +
              lpNorm ((schwartzApprox hf n : ℝ → ℂ) - f) 2 volume := by
                exact
                  lpNorm_sub_le
                    (f := (schwartzApprox hf n : ℝ → ℂ))
                    (g := (schwartzApprox hf n : ℝ → ℂ) - f) hs (by norm_num)
        _ ≤ lpNorm (schwartzApprox hf n : ℝ → ℂ) 2 volume + 1 / ((n : ℝ) + 1) := by
              gcongr
              simpa [MeasureTheory.lpNorm_sub_comm] using schwartzApprox_lpNorm_sub_le hf n
    rw [abs_sub_le_iff]
    constructor <;> linarith
  simpa [Real.dist_eq] using squeeze_zero (fun n => abs_nonneg _) hbound hε

private theorem stft_tendsto_schwartzApprox
    (hw : MemLp w 2 volume) (hu : MemLp u 2 volume) (x ω : ℝ) :
    Tendsto
      (fun n : ℕ ↦ stft (schwartzApprox hw n) (schwartzApprox hu n) x ω)
      atTop (nhds (stft w u x ω)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have herr_u :
      Tendsto (fun n : ℕ ↦ lpNorm ((schwartzApprox hu n : ℝ → ℂ) - u) 2 volume) atTop (nhds 0) := by
    simpa [MeasureTheory.lpNorm_sub_comm] using schwartzApprox_tendsto_lpNorm_sub_zero hu
  have herr_w :
      Tendsto (fun n : ℕ ↦ lpNorm ((schwartzApprox hw n : ℝ → ℂ) - w) 2 volume) atTop (nhds 0) := by
    simpa [MeasureTheory.lpNorm_sub_comm] using schwartzApprox_tendsto_lpNorm_sub_zero hw
  have hbound_tendsto :
      Tendsto
        (fun n : ℕ ↦
          lpNorm ((schwartzApprox hu n : ℝ → ℂ) - u) 2 volume * (lpNorm w 2 volume + 1) +
            lpNorm u 2 volume * lpNorm ((schwartzApprox hw n : ℝ → ℂ) - w) 2 volume)
        atTop (nhds 0) := by
    have h₁ :
        Tendsto
          (fun n : ℕ ↦
            lpNorm ((schwartzApprox hu n : ℝ → ℂ) - u) 2 volume * (lpNorm w 2 volume + 1))
          atTop (nhds 0) := by
      simpa [mul_comm] using herr_u.const_mul (lpNorm w 2 volume + 1)
    have h₂ :
        Tendsto
          (fun n : ℕ ↦ lpNorm u 2 volume * lpNorm ((schwartzApprox hw n : ℝ → ℂ) - w) 2 volume)
          atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul herr_w)
    simpa using h₁.add h₂
  refine squeeze_zero (fun n ↦ norm_nonneg _) ?_ hbound_tendsto
  intro n
  have hwN : MemLp (schwartzApprox hw n : ℝ → ℂ) 2 volume := (schwartzApprox hw n).memLp 2 volume
  have huN : MemLp (schwartzApprox hu n : ℝ → ℂ) 2 volume := (schwartzApprox hu n).memLp 2 volume
  calc
    ‖stft (schwartzApprox hw n) (schwartzApprox hu n) x ω - stft w u x ω‖
        ≤ lpNorm ((schwartzApprox hu n : ℝ → ℂ) - u) 2 volume *
              lpNorm (schwartzApprox hw n : ℝ → ℂ) 2 volume +
            lpNorm u 2 volume * lpNorm ((schwartzApprox hw n : ℝ → ℂ) - w) 2 volume := by
              simpa [MeasureTheory.lpNorm_sub_comm] using
                norm_stft_sub_le_lpNorm hwN hw huN hu x ω
    _ ≤ lpNorm ((schwartzApprox hu n : ℝ → ℂ) - u) 2 volume * (lpNorm w 2 volume + 1) +
          lpNorm u 2 volume * lpNorm ((schwartzApprox hw n : ℝ → ℂ) - w) 2 volume := by
            refine add_le_add ?_ le_rfl
            exact mul_le_mul_of_nonneg_left
              (schwartzApprox_lpNorm_le_add_one hw n) (MeasureTheory.lpNorm_nonneg)

def symplecticFourier (F : ℝ → ℝ → ℂ) (x ω : ℝ) : ℂ :=
  ∫ y, ∫ η, F y η * (Real.fourierChar (-(ω * y - x * η)) : ℂ)

theorem stft_sq_integrable_schwartz (w u : SchwartzMap ℝ ℂ) :
    Integrable (fun p : ℝ × ℝ ↦ ‖stft w u p.1 p.2‖ ^ 2) (volume.prod volume) := by
  let F : ℝ × ℝ → ℝ := fun p ↦ ‖stft w u p.1 p.2‖ ^ 2
  have hF_meas : AEStronglyMeasurable F (volume.prod volume) := by
    exact ((stft_continuous_schwartz w u).norm.pow 2).aestronglyMeasurable
  refine (MeasureTheory.integrable_prod_iff hF_meas).2 ?_
  constructor
  · refine Filter.Eventually.of_forall ?_
    intro x
    simpa [F] using integrable_stft_sq_slice_schwartz w u x
  · have hkernel :
      Integrable (fun p : ℝ × ℝ ↦ ‖u p.1‖ ^ 2 * ‖w (p.1 - p.2)‖ ^ 2)
        (volume.prod volume) :=
    integrable_stft_kernel_schwartz w u
    have h_outer :
        (fun x : ℝ => ∫ ω, ‖F (x, ω)‖ ∂volume) =
          fun x : ℝ => ∫ t, ‖u t‖ ^ 2 * ‖w (t - x)‖ ^ 2 := by
      funext x
      calc
        ∫ ω, ‖F (x, ω)‖
            = ∫ ω, ‖stft w u x ω‖ ^ 2 := by
                refine integral_congr_ae ?_
                filter_upwards with ω
                simp [F]
        _ = ∫ t, ‖u t‖ ^ 2 * ‖w (t - x)‖ ^ 2 := by
              rw [integral_norm_sq_stft_slice_schwartz w u x]
              refine integral_congr_ae ?_
              filter_upwards with t
              simp [stftSliceSchwartz_apply, pow_two, mul_assoc, mul_left_comm, mul_comm]
    rw [h_outer]
    simpa using hkernel.integral_norm_prod_right

theorem stft_sq_complex_integrable_schwartz (w u : SchwartzMap ℝ ℂ) :
    Integrable (fun p : ℝ × ℝ ↦ ((‖stft w u p.1 p.2‖ ^ 2 : ℝ) : ℂ)) (volume.prod volume) := by
  simpa using (stft_sq_integrable_schwartz w u).ofReal (𝕜 := ℂ)

theorem integral_stft_sq_schwartz (w u : SchwartzMap ℝ ℂ) :
    ∫ x, ∫ ω, ‖stft w u x ω‖ ^ 2 =
      (eLpNorm (u : ℝ → ℂ) 2 volume).toReal ^ 2 * (eLpNorm (w : ℝ → ℂ) 2 volume).toReal ^ 2 := by
  have hkernel :
      Integrable (fun p : ℝ × ℝ ↦ ‖u p.1‖ ^ 2 * ‖w (p.1 - p.2)‖ ^ 2)
        (volume.prod volume) :=
    integrable_stft_kernel_schwartz w u
  have hkernel_swap : Integrable (Function.uncurry (fun x t : ℝ ↦ ‖u t‖ ^ 2 * ‖w (t - x)‖ ^ 2))
      (volume.prod volume) := by
    simpa [Function.uncurry, Function.comp] using hkernel.swap
  calc
    ∫ x, ∫ ω, ‖stft w u x ω‖ ^ 2
        = ∫ x, ∫ t, ‖u t‖ ^ 2 * ‖w (t - x)‖ ^ 2 := by
            refine integral_congr_ae ?_
            filter_upwards with x
            rw [integral_norm_sq_stft_slice_schwartz w u x]
            refine integral_congr_ae ?_
            filter_upwards with t
            simp [stftSliceSchwartz_apply, pow_two, mul_assoc, mul_left_comm, mul_comm]
    _ = ∫ t, ∫ x, ‖u t‖ ^ 2 * ‖w (t - x)‖ ^ 2 := by
          simpa using
            (MeasureTheory.integral_integral_swap
              (f := fun x t : ℝ ↦ ‖u t‖ ^ 2 * ‖w (t - x)‖ ^ 2) hkernel_swap)
    _ = ∫ t, ‖u t‖ ^ 2 * ∫ x, ‖w x‖ ^ 2 := by
          refine integral_congr_ae ?_
          filter_upwards with t
          exact integral_stft_kernel_slice_schwartz w u t
    _ = (∫ t, ‖u t‖ ^ 2) * ∫ x, ‖w x‖ ^ 2 := by
          simpa [mul_comm] using
            (MeasureTheory.integral_const_mul
              (r := ∫ x, ‖w x‖ ^ 2) (f := fun t : ℝ ↦ ‖u t‖ ^ 2))
    _ = (eLpNorm (u : ℝ → ℂ) 2 volume).toReal ^ 2 * (eLpNorm (w : ℝ → ℂ) 2 volume).toReal ^ 2 := by
          rw [integral_norm_sq_eq_eLpNorm_sq (f := (u : ℝ → ℂ)) (hf := u.memLp 2 volume),
            integral_norm_sq_eq_eLpNorm_sq (f := (w : ℝ → ℂ)) (hf := w.memLp 2 volume)]

private theorem integral_fourier_sq_phase_schwartz
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    ∫ η, ((‖(FourierTransform.fourier f) η‖ ^ 2 : ℝ) : ℂ) * (Real.fourierChar (x * η) : ℂ) =
      ∫ t, star (f t) * f (t + x) := by
  have h :=
    SchwartzMap.integral_inner_fourier_fourier f (f.compSubConstCLM ℂ (-x))
  simpa [fourier_compSubConstCLM_eq_modulate,
    SchwartzMap.compSubConstCLM_apply, modulate, RCLike.inner_apply', RCLike.mul_conj, pow_two,
    mul_assoc, mul_comm, mul_left_comm] using h

private theorem integral_stft_sq_phase_slice_schwartz
    (w u : SchwartzMap ℝ ℂ) (y x : ℝ) :
    ∫ η, ((‖stft w u y η‖ ^ 2 : ℝ) : ℂ) * (Real.fourierChar (x * η) : ℂ) =
      ∫ t, star (stftSliceSchwartz w u y t) * stftSliceSchwartz w u y (t + x) := by
  simpa [stft_eq_fourierIntegral_schwartz_apply] using
    integral_fourier_sq_phase_schwartz (stftSliceSchwartz w u y) x

private theorem signal_autocorr_integrable_schwartz
    (u : SchwartzMap ℝ ℂ) (x : ℝ) :
    Integrable (fun t : ℝ ↦ star (u t) * u (t + x)) volume := by
  have hshift : MemLp (translate (-x) (u : ℝ → ℂ)) 2 volume :=
    translate_memLp (-x) (u.memLp 2 volume)
  convert
    integrable_mul_of_memLp hshift (conj_memLp (u.memLp 2 volume)) using 1
  funext t
  simp [translate, mul_comm]

private theorem reflected_memLp_schwartz
    (w : SchwartzMap ℝ ℂ) :
    MemLp (fun y : ℝ ↦ w (-y)) 2 volume := by
  simpa using
    (w.memLp 2 volume).comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))

private theorem window_autocorr_integrable_schwartz
    (w : SchwartzMap ℝ ℂ) (t x : ℝ) :
    Integrable (fun y : ℝ ↦ w (t - y) * star (w (t + x - y))) volume := by
  have hneg : MemLp (fun y : ℝ ↦ w (-y)) 2 volume := reflected_memLp_schwartz w
  have hleft' : MemLp (translate t (fun y : ℝ ↦ w (-y))) 2 volume :=
    translate_memLp t hneg
  have hright' : MemLp (translate (t + x) (fun y : ℝ ↦ w (-y))) 2 volume :=
    translate_memLp (t + x) hneg
  have hleft : MemLp (fun y : ℝ ↦ w (t - y)) 2 volume := by
    convert hleft' using 1
    funext y
    simp [translate]
  have hright : MemLp (fun y : ℝ ↦ w (t + x - y)) 2 volume := by
    convert hright' using 1
    funext y
    simp [translate]
  exact integrable_mul_of_memLp hleft (conj_memLp hright)

private theorem integral_window_autocorr_norm_schwartz
    (w : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ∫ y, ‖w (t - y) * star (w (t + x - y))‖ =
      ∫ y, ‖w (-y) * star (w (x - y))‖ := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (integral_sub_right_eq_self (μ := (volume : Measure ℝ))
      (f := fun y : ℝ ↦ ‖w (-y) * star (w (x - y))‖) t)

private theorem autocorr_kernel_integrable_schwartz
    (u w : SchwartzMap ℝ ℂ) (x : ℝ) :
    Integrable
      (fun p : ℝ × ℝ ↦
        (star (u p.1) * u (p.1 + x)) *
        (w (p.1 - p.2) * star (w (p.1 + x - p.2))))
      (volume.prod volume) := by
  let A : ℝ → ℂ := fun t ↦ star (u t) * u (t + x)
  let B : ℝ × ℝ → ℂ := fun p ↦ w (p.1 - p.2) * star (w (p.1 + x - p.2))
  have hA : Integrable A volume := signal_autocorr_integrable_schwartz u x
  have hB : ∀ᵐ t ∂volume, Integrable (fun y : ℝ ↦ A t * B (t, y)) volume := by
    refine Filter.Eventually.of_forall ?_
    intro t
    simpa [A, B, translate, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc,
      mul_left_comm, mul_comm] using
      (window_autocorr_integrable_schwartz w t x).const_mul (A t)
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ A p.1 * B p) (volume.prod volume) := by
    fun_prop
  refine (MeasureTheory.integrable_prod_iff hmeas).2 ?_
  constructor
  · exact hB
  · have hA_norm : Integrable (fun t : ℝ ↦ ‖A t‖) volume := hA.norm
    let C : ℝ := ∫ y, ‖w (-y) * star (w (x - y))‖
    have hC : ∀ t : ℝ, ∫ y, ‖B (t, y)‖ = C := by
      intro t
      simpa [B, C] using integral_window_autocorr_norm_schwartz w t x
    have houter : Integrable (fun t : ℝ ↦ ∫ y, ‖A t‖ * ‖B (t, y)‖ ∂volume) volume := by
      have hconst : ∀ t : ℝ, ∫ y, ‖A t‖ * ‖B (t, y)‖ ∂volume = ‖A t‖ * C := by
        intro t
        calc
          ∫ y, ‖A t‖ * ‖B (t, y)‖
              = ‖A t‖ * ∫ y, ‖B (t, y)‖ := by
                simpa using
                  (MeasureTheory.integral_const_mul
                    (r := ‖A t‖)
                    (f := fun y : ℝ ↦ ‖B (t, y)‖))
          _ = ‖A t‖ * C := by rw [hC t]
      have houterEq : (fun t : ℝ ↦ ∫ y, ‖A t‖ * ‖B (t, y)‖ ∂volume) = fun t : ℝ ↦ ‖A t‖ * C := by
        funext t
        exact hconst t
      simpa [houterEq, mul_comm] using hA_norm.const_mul C
    simpa [A, B, norm_mul, mul_assoc, mul_left_comm, mul_comm] using houter

private theorem integral_window_autocorr_phase_schwartz
    (w : SchwartzMap ℝ ℂ) (t x ω : ℝ) :
    ∫ y, w (t - y) * star (w (t + x - y)) * (Real.fourierChar (-(ω * y)) : ℂ) =
      (Real.fourierChar (-(ω * (t + x / 2))) : ℂ) * star (ambiguity w x ω) := by
  have hphase_t :
      ∀ y : ℝ,
        (Real.fourierChar (-(ω * y)) : ℂ) =
          (Real.fourierChar (-(ω * t)) : ℂ) *
            (Real.fourierChar (-(ω * (y - t))) : ℂ) := by
    intro y
    have hmul := Real.fourierChar.map_add_eq_mul' (-(ω * t)) (-(ω * (y - t)))
    simpa [show -(ω * y) = -(ω * t) + -(ω * (y - t)) by ring,
      mul_comm, mul_left_comm, mul_assoc] using congrArg (fun z : Circle ↦ (z : ℂ)) hmul
  have hshift_t :
      ∫ y, w (t - y) * star (w (t + x - y)) * (Real.fourierChar (-(ω * y)) : ℂ) =
        (Real.fourierChar (-(ω * t)) : ℂ) *
          ∫ y, w (-y) * star (w (x - y)) * (Real.fourierChar (-(ω * y)) : ℂ) := by
    calc
      ∫ y, w (t - y) * star (w (t + x - y)) * (Real.fourierChar (-(ω * y)) : ℂ)
          = ∫ y, (Real.fourierChar (-(ω * t)) : ℂ) *
              (w (t - y) * star (w (t + x - y)) * (Real.fourierChar (-(ω * (y - t))) : ℂ)) := by
                refine integral_congr_ae ?_
                filter_upwards with y
                rw [hphase_t y]
                ring_nf
      _ = (Real.fourierChar (-(ω * t)) : ℂ) *
            ∫ y, w (t - y) * star (w (t + x - y)) * (Real.fourierChar (-(ω * (y - t))) : ℂ) := by
              simpa [mul_assoc] using
                (MeasureTheory.integral_const_mul
                  (r := (Real.fourierChar (-(ω * t)) : ℂ))
                  (f := fun y : ℝ ↦
                    w (t - y) * star (w (t + x - y)) * (Real.fourierChar (-(ω * (y - t))) : ℂ)))
      _ = (Real.fourierChar (-(ω * t)) : ℂ) *
            ∫ y, w (-y) * star (w (x - y)) * (Real.fourierChar (-(ω * y)) : ℂ) := by
              congr 1
              simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
                (integral_sub_right_eq_self (μ := (volume : Measure ℝ))
                  (f := fun y : ℝ ↦
                    w (-y) * star (w (x - y)) * (Real.fourierChar (-(ω * y)) : ℂ)) t)
  have hneg :
      ∫ y, w (-y) * star (w (x - y)) * (Real.fourierChar (-(ω * y)) : ℂ) =
        ∫ y, w y * star (w (x + y)) * (Real.fourierChar (ω * y) : ℂ) := by
    simpa [sub_eq_add_neg, mul_assoc] using
      (integral_neg_eq_self (μ := (volume : Measure ℝ))
        (f := fun y : ℝ ↦
          w y * star (w (x + y)) * (Real.fourierChar (ω * y) : ℂ)))
  have hphase_x :
      ∀ y : ℝ,
        (Real.fourierChar (ω * y) : ℂ) =
          (Real.fourierChar (-(ω * (x / 2))) : ℂ) *
            (Real.fourierChar (ω * (y + x / 2)) : ℂ) := by
    intro y
    have hmul := Real.fourierChar.map_add_eq_mul' (-(ω * (x / 2))) (ω * (y + x / 2))
    simpa [show ω * y = -(ω * (x / 2)) + ω * (y + x / 2) by ring,
      mul_comm, mul_left_comm, mul_assoc] using congrArg (fun z : Circle ↦ (z : ℂ)) hmul
  have hshift_x :
      ∫ y, w y * star (w (x + y)) * (Real.fourierChar (ω * y) : ℂ) =
        (Real.fourierChar (-(ω * (x / 2))) : ℂ) *
          ∫ y, w (y - x / 2) * star (w (y + x / 2)) * (Real.fourierChar (ω * y) : ℂ) := by
    calc
      ∫ y, w y * star (w (x + y)) * (Real.fourierChar (ω * y) : ℂ)
          = ∫ y, (Real.fourierChar (-(ω * (x / 2))) : ℂ) *
              (w y * star (w (x + y)) * (Real.fourierChar (ω * (y + x / 2)) : ℂ)) := by
                refine integral_congr_ae ?_
                filter_upwards with y
                rw [hphase_x y]
                ring_nf
      _ = (Real.fourierChar (-(ω * (x / 2))) : ℂ) *
            ∫ y, w y * star (w (x + y)) * (Real.fourierChar (ω * (y + x / 2)) : ℂ) := by
              simpa [mul_assoc] using
                (MeasureTheory.integral_const_mul
                  (r := (Real.fourierChar (-(ω * (x / 2))) : ℂ))
                  (f := fun y : ℝ ↦
                    w y * star (w (x + y)) * (Real.fourierChar (ω * (y + x / 2)) : ℂ)))
      _ = (Real.fourierChar (-(ω * (x / 2))) : ℂ) *
            ∫ y, w (y - x / 2) * star (w (y + x / 2)) * (Real.fourierChar (ω * y) : ℂ) := by
              congr 1
              simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
                (integral_add_right_eq_self (μ := (volume : Measure ℝ))
                  (f := fun y : ℝ ↦
                    w (y - x / 2) * star (w (y + x / 2)) * (Real.fourierChar (ω * y) : ℂ))
                  (x / 2))
  have hamb :
      ∫ y, w (y - x / 2) * star (w (y + x / 2)) * (Real.fourierChar (ω * y) : ℂ) =
        ambiguity w (-x) (-ω) := by
    rw [ambiguity, crossAmbiguity]
    refine integral_congr_ae ?_
    filter_upwards with y
    congr 1 <;> ring_nf
  have hphase_tx :
      (Real.fourierChar (-(ω * t)) : ℂ) * (Real.fourierChar (-(ω * (x / 2))) : ℂ) =
        (Real.fourierChar (-(ω * (t + x / 2))) : ℂ) := by
    have hmul := Real.fourierChar.map_add_eq_mul (-(ω * t)) (-(ω * (x / 2)))
    simpa [show -(ω * (t + x / 2)) = -(ω * t) + -(ω * (x / 2)) by ring,
      mul_comm, mul_left_comm, mul_assoc] using (congrArg (fun z : Circle ↦ (z : ℂ)) hmul).symm
  calc
    ∫ y, w (t - y) * star (w (t + x - y)) * (Real.fourierChar (-(ω * y)) : ℂ)
        = (Real.fourierChar (-(ω * t)) : ℂ) *
            ∫ y, w (-y) * star (w (x - y)) * (Real.fourierChar (-(ω * y)) : ℂ) := hshift_t
    _ = (Real.fourierChar (-(ω * t)) : ℂ) *
          ((Real.fourierChar (-(ω * (x / 2))) : ℂ) * ambiguity w (-x) (-ω)) := by
            rw [hneg, hshift_x, hamb]
    _ = (Real.fourierChar (-(ω * (t + x / 2))) : ℂ) * star (ambiguity w x ω) := by
          rw [ambiguity_neg_neg (f := (w : ℝ → ℂ)) (hf := w.memLp 2 volume) x ω, ← mul_assoc,
            hphase_tx]

private theorem integral_signal_autocorr_phase_schwartz
    (u : SchwartzMap ℝ ℂ) (x ω : ℝ) :
    ∫ t, star (u t) * u (t + x) * (Real.fourierChar (-(ω * (t + x / 2))) : ℂ) =
      ambiguity u x ω := by
  simpa [ambiguity, crossAmbiguity, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    mul_assoc, mul_left_comm, mul_comm] using
    (integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (f := fun t : ℝ ↦
        u (t + x / 2) * star (u (t - x / 2)) * (Real.fourierChar (-(ω * t)) : ℂ))
      (x / 2))

theorem symplecticFourier_stft_sq_schwartz
    (w u : SchwartzMap ℝ ℂ) (x ω : ℝ) :
    symplecticFourier (fun y η ↦ ((‖stft w u y η‖ ^ 2 : ℝ) : ℂ)) x ω =
      ambiguity u x ω * star (ambiguity w x ω) := by
  let K : ℝ → ℝ → ℂ := fun y t ↦
    (star (u t) * u (t + x)) *
      (w (t - y) * star (w (t + x - y))) *
      (Real.fourierChar (-(ω * y)) : ℂ)
  let G : ℝ × ℝ → ℂ := fun p ↦
    ((star (u p.1) * u (p.1 + x)) *
      (w (p.1 - p.2) * star (w (p.1 + x - p.2)))) *
      (Real.fourierChar (-(ω * p.2)) : ℂ)
  have hphase_meas :
      AEStronglyMeasurable (fun p : ℝ × ℝ ↦ (Real.fourierChar (-(ω * p.2)) : ℂ))
        (volume.prod volume) := by
    exact
      (by fun_prop :
        Measurable fun p : ℝ × ℝ ↦ (Real.fourierChar (-(ω * p.2)) : ℂ)).aestronglyMeasurable
  have hphase_bound :
      ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), ‖(Real.fourierChar (-(ω * p.2)) : ℂ)‖ ≤ (1 : ℝ) := by
    filter_upwards [Filter.Eventually.of_forall (fun p : ℝ × ℝ ↦ norm_fourierChar (-(ω * p.2)))]
      with p hp
    exact le_of_eq hp
  have hG :
      Integrable G (volume.prod volume) := by
    simpa [G, mul_assoc] using
      (autocorr_kernel_integrable_schwartz u w x).mul_bdd hphase_meas hphase_bound
  have hK :
      Integrable (Function.uncurry K) (volume.prod volume) := by
    simpa [K, G, Function.uncurry, mul_assoc, mul_left_comm, mul_comm] using hG.swap
  calc
    symplecticFourier (fun y η ↦ ((‖stft w u y η‖ ^ 2 : ℝ) : ℂ)) x ω
        = ∫ y, (Real.fourierChar (-(ω * y)) : ℂ) *
            ∫ t, star (stftSliceSchwartz w u y t) * stftSliceSchwartz w u y (t + x) := by
              unfold symplecticFourier
              refine integral_congr_ae ?_
              filter_upwards with y
              have hphase_y :
                  ∀ η : ℝ,
                    (Real.fourierChar (-(ω * y - x * η)) : ℂ) =
                      (Real.fourierChar (-(ω * y)) : ℂ) * (Real.fourierChar (x * η) : ℂ) := by
                intro η
                have hmul := Real.fourierChar.map_add_eq_mul' (-(ω * y)) (x * η)
                simpa [show -(ω * y - x * η) = -(ω * y) + x * η by ring,
                  mul_comm, mul_left_comm, mul_assoc] using
                  congrArg (fun z : Circle ↦ (z : ℂ)) hmul
              calc
                ∫ η, ((‖stft w u y η‖ ^ 2 : ℝ) : ℂ) * (Real.fourierChar (-(ω * y - x * η)) : ℂ)
                    = ∫ η, (Real.fourierChar (-(ω * y)) : ℂ) *
                        (((‖stft w u y η‖ ^ 2 : ℝ) : ℂ) * (Real.fourierChar (x * η) : ℂ)) := by
                          refine integral_congr_ae ?_
                          filter_upwards with η
                          rw [hphase_y η]
                          ring_nf
                _ = (Real.fourierChar (-(ω * y)) : ℂ) *
                      ∫ η, ((‖stft w u y η‖ ^ 2 : ℝ) : ℂ) * (Real.fourierChar (x * η) : ℂ) := by
                        exact
                          MeasureTheory.integral_const_mul
                            (r := (Real.fourierChar (-(ω * y)) : ℂ))
                            (f := fun η : ℝ ↦
                              ((‖stft w u y η‖ ^ 2 : ℝ) : ℂ) * (Real.fourierChar (x * η) : ℂ))
                _ = (Real.fourierChar (-(ω * y)) : ℂ) *
                      ∫ t, star (stftSliceSchwartz w u y t) * stftSliceSchwartz w u y (t + x) := by
                        rw [integral_stft_sq_phase_slice_schwartz w u y x]
    _ = ∫ y, ∫ t, K y t := by
          refine integral_congr_ae ?_
          filter_upwards with y
          calc
            (Real.fourierChar (-(ω * y)) : ℂ) *
                ∫ t, star (stftSliceSchwartz w u y t) * stftSliceSchwartz w u y (t + x)
                = ∫ t, (Real.fourierChar (-(ω * y)) : ℂ) *
                    (star (stftSliceSchwartz w u y t) * stftSliceSchwartz w u y (t + x)) := by
                      simpa [mul_assoc] using
                        (MeasureTheory.integral_const_mul
                          (r := (Real.fourierChar (-(ω * y)) : ℂ))
                          (f := fun t : ℝ ↦
                            star (stftSliceSchwartz w u y t) *
                              stftSliceSchwartz w u y (t + x))).symm
            _ = ∫ t, K y t := by
                  refine integral_congr_ae ?_
                  filter_upwards with t
                  simp [K, stftSliceSchwartz_apply, mul_left_comm, mul_comm]
    _ = ∫ t, ∫ y, K y t := by
          exact MeasureTheory.integral_integral_swap hK
    _ = ∫ t, (star (u t) * u (t + x)) *
          ((Real.fourierChar (-(ω * (t + x / 2))) : ℂ) * star (ambiguity w x ω)) := by
          refine integral_congr_ae ?_
          filter_upwards with t
          calc
            ∫ y, K y t
                = ∫ y, (star (u t) * u (t + x)) *
                    (w (t - y) * star (w (t + x - y)) * (Real.fourierChar (-(ω * y)) : ℂ)) := by
                      refine integral_congr_ae ?_
                      filter_upwards with y
                      simp [K, mul_left_comm, mul_comm]
            _ = (star (u t) * u (t + x)) *
                  ∫ y, w (t - y) * star (w (t + x - y)) * (Real.fourierChar (-(ω * y)) : ℂ) := by
                    simpa [mul_assoc] using
                      (MeasureTheory.integral_const_mul
                        (r := star (u t) * u (t + x))
                        (f := fun y : ℝ ↦
                          w (t - y) * star (w (t + x - y)) * (Real.fourierChar (-(ω * y)) : ℂ)))
            _ = (star (u t) * u (t + x)) *
                  ((Real.fourierChar (-(ω * (t + x / 2))) : ℂ) * star (ambiguity w x ω)) := by
                    rw [integral_window_autocorr_phase_schwartz w t x ω]
    _ = star (ambiguity w x ω) *
          ∫ t, (star (u t) * u (t + x)) * (Real.fourierChar (-(ω * (t + x / 2))) : ℂ) := by
          calc
            ∫ t, (star (u t) * u (t + x)) *
                ((Real.fourierChar (-(ω * (t + x / 2))) : ℂ) * star (ambiguity w x ω))
                = ∫ t, star (ambiguity w x ω) *
                    ((star (u t) * u (t + x)) * (Real.fourierChar (-(ω * (t + x / 2))) : ℂ)) := by
                      refine integral_congr_ae ?_
                      filter_upwards with t
                      ring_nf
            _ = star (ambiguity w x ω) *
                  ∫ t, (star (u t) * u (t + x)) * (Real.fourierChar (-(ω * (t + x / 2))) : ℂ) := by
                    simpa [mul_assoc] using
                      (MeasureTheory.integral_const_mul
                        (r := star (ambiguity w x ω))
                        (f := fun t : ℝ ↦
                          (star (u t) * u (t + x)) * (Real.fourierChar (-(ω * (t + x / 2))) : ℂ)))
    _ = star (ambiguity w x ω) * ambiguity u x ω := by
          rw [integral_signal_autocorr_phase_schwartz u x ω]
    _ = ambiguity u x ω * star (ambiguity w x ω) := by
          ring

private theorem stft_memLp_schwartz
    (w u : SchwartzMap ℝ ℂ) :
    MemLp (fun p : ℝ × ℝ ↦ stft w u p.1 p.2) 2 (volume.prod volume) := by
  exact
    (memLp_two_iff_integrable_sq_norm ((stft_continuous_schwartz w u).aestronglyMeasurable)).2
      (stft_sq_integrable_schwartz w u)

private theorem lpNorm_stft_schwartz
    (w u : SchwartzMap ℝ ℂ) :
    lpNorm (fun p : ℝ × ℝ ↦ stft w u p.1 p.2) 2 (volume.prod volume) =
      lpNorm (u : ℝ → ℂ) 2 volume * lpNorm (w : ℝ → ℂ) 2 volume := by
  rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
      (μ := volume.prod volume) (p := (2 : ENNReal))
      (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)
      ((stft_continuous_schwartz w u).aestronglyMeasurable)]
  norm_num
  rw [(MeasureTheory.integral_integral
      (f := fun x ω : ℝ ↦ ‖stft w u x ω‖ ^ 2)
      (by simpa [Function.uncurry] using stft_sq_integrable_schwartz w u)).symm]
  rw [integral_stft_sq_schwartz w u]
  rw [MeasureTheory.toReal_eLpNorm (u.memLp 2 volume).aestronglyMeasurable,
    MeasureTheory.toReal_eLpNorm (w.memLp 2 volume).aestronglyMeasurable]
  have hnonneg :
      0 ≤ lpNorm (u : ℝ → ℂ) 2 volume * lpNorm (w : ℝ → ℂ) 2 volume := by
    exact mul_nonneg MeasureTheory.lpNorm_nonneg MeasureTheory.lpNorm_nonneg
  rw [show
      (lpNorm (u : ℝ → ℂ) 2 volume ^ 2) * (lpNorm (w : ℝ → ℂ) 2 volume ^ 2) =
        (lpNorm (u : ℝ → ℂ) 2 volume * lpNorm (w : ℝ → ℂ) 2 volume) ^ 2 by ring]
  rw [← Real.sqrt_eq_rpow]
  simp [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]

private theorem eLpNorm_stft_schwartz_eq
    (w u : SchwartzMap ℝ ℂ) :
    eLpNorm (fun p : ℝ × ℝ ↦ stft w u p.1 p.2) 2 (volume.prod volume) =
      ENNReal.ofReal (lpNorm (u : ℝ → ℂ) 2 volume * lpNorm (w : ℝ → ℂ) 2 volume) := by
  calc
    eLpNorm (fun p : ℝ × ℝ ↦ stft w u p.1 p.2) 2 (volume.prod volume)
        = ENNReal.ofReal (lpNorm (fun p : ℝ × ℝ ↦ stft w u p.1 p.2) 2 (volume.prod volume)) := by
            symm
            exact MeasureTheory.ofReal_lpNorm (stft_memLp_schwartz w u)
    _ = ENNReal.ofReal (lpNorm (u : ℝ → ℂ) 2 volume * lpNorm (w : ℝ → ℂ) 2 volume) := by
          rw [lpNorm_stft_schwartz]

private theorem stft_continuous_of_memLp (hw : MemLp w 2 volume) (hu : MemLp u 2 volume) :
    Continuous (fun p : ℝ × ℝ ↦ stft w u p.1 p.2) := by
  have hcont1 : Continuous (fun p : ℝ × ℝ ↦ (Real.fourierChar (-(p.2 * p.1 / 2)) : ℂ)) := by
    exact (continuous_subtype_val.comp
      (by simpa using
        (Real.continuous_fourierChar.comp
          (by fun_prop : Continuous fun p : ℝ × ℝ ↦ -(p.2 * p.1 / 2)))))
  have hcont2 : Continuous (fun p : ℝ × ℝ ↦ crossAmbiguity u w p.1 p.2) :=
    crossAmbiguity_continuous (f := u) (g := w) hu hw
  have hcont : Continuous (fun p : ℝ × ℝ ↦
      (Real.fourierChar (-(p.2 * p.1 / 2)) : ℂ) * crossAmbiguity u w p.1 p.2) := hcont1.mul hcont2
  have hEq : (fun p : ℝ × ℝ ↦ stft w u p.1 p.2) =
      fun p : ℝ × ℝ ↦ (Real.fourierChar (-(p.2 * p.1 / 2)) : ℂ) * crossAmbiguity u w p.1 p.2 := by
    funext p
    simpa [stft] using stft_eq_crossAmbiguity (w := w) (u := u) hw hu p.1 p.2
  rw [hEq]
  exact hcont

private theorem stft_aestronglyMeasurable_of_memLp (hw : MemLp w 2 volume) (hu : MemLp u 2 volume) :
    AEStronglyMeasurable (fun p : ℝ × ℝ ↦ stft w u p.1 p.2) (volume.prod volume) := by
  exact (stft_continuous_of_memLp hw hu).aestronglyMeasurable

private theorem eLpNorm_stft_le
    (hw : MemLp w 2 volume) (hu : MemLp u 2 volume) :
    eLpNorm (fun p : ℝ × ℝ ↦ stft w u p.1 p.2) 2 (volume.prod volume) ≤
      ENNReal.ofReal (lpNorm u 2 volume * lpNorm w 2 volume) := by
  let F : ℝ × ℝ → ℂ := fun p ↦ stft w u p.1 p.2
  let Fₙ : ℕ → ℝ × ℝ → ℂ := fun n p ↦
    stft (schwartzApprox hw n) (schwartzApprox hu n) p.1 p.2
  have hpoint :
      ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), Tendsto (fun n : ℕ ↦ Fₙ n p) atTop (nhds (F p)) := by
    filter_upwards with p
    exact stft_tendsto_schwartzApprox hw hu p.1 p.2
  have hmeas :
      ∀ n : ℕ, AEStronglyMeasurable (Fₙ n) (volume.prod volume) := by
    intro n
    exact
      (stft_continuous_schwartz (schwartzApprox hw n) (schwartzApprox hu n)).aestronglyMeasurable
  have hliminf :
      eLpNorm F 2 (volume.prod volume) ≤
        atTop.liminf (fun n : ℕ ↦ eLpNorm (Fₙ n) 2 (volume.prod volume)) := by
    exact MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm hmeas F hpoint
  have hprod :
      Tendsto
        (fun n : ℕ ↦
          lpNorm (schwartzApprox hu n : ℝ → ℂ) 2 volume *
            lpNorm (schwartzApprox hw n : ℝ → ℂ) 2 volume)
        atTop (nhds (lpNorm u 2 volume * lpNorm w 2 volume)) := by
    exact (schwartzApprox_tendsto_lpNorm hu).mul (schwartzApprox_tendsto_lpNorm hw)
  have hnorms' :
      Tendsto
        (fun n : ℕ ↦
          ENNReal.ofReal
            (lpNorm (schwartzApprox hu n : ℝ → ℂ) 2 volume *
              lpNorm (schwartzApprox hw n : ℝ → ℂ) 2 volume))
        atTop (nhds (ENNReal.ofReal (lpNorm u 2 volume * lpNorm w 2 volume))) := by
    exact (ENNReal.continuous_ofReal.tendsto (lpNorm u 2 volume * lpNorm w 2 volume)).comp hprod
  have hnorms :
      Tendsto
        (fun n : ℕ ↦ eLpNorm (Fₙ n) 2 (volume.prod volume))
        atTop (nhds (ENNReal.ofReal (lpNorm u 2 volume * lpNorm w 2 volume))) := by
    simpa only [Fₙ, eLpNorm_stft_schwartz_eq] using hnorms'
  calc
    eLpNorm F 2 (volume.prod volume)
        ≤ atTop.liminf (fun n : ℕ ↦ eLpNorm (Fₙ n) 2 (volume.prod volume)) := hliminf
    _ = ENNReal.ofReal (lpNorm u 2 volume * lpNorm w 2 volume) := by
          rw [hnorms.liminf_eq]

theorem stft_sq_integrable (hw : MemLp w 2 volume) (hu : MemLp u 2 volume) :
    Integrable (fun p : ℝ × ℝ ↦ ‖stft w u p.1 p.2‖ ^ 2) (volume.prod volume) := by
  have hfinite_rhs :
      ENNReal.ofReal (lpNorm u 2 volume * lpNorm w 2 volume) < ⊤ := by
    simpa [ENNReal.ofReal_mul, MeasureTheory.lpNorm_nonneg] using
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top :
        ENNReal.ofReal (lpNorm u 2 volume) * ENNReal.ofReal (lpNorm w 2 volume) < ⊤)
  have hfin :
      eLpNorm (fun p : ℝ × ℝ ↦ stft w u p.1 p.2) 2 (volume.prod volume) < ⊤ :=
    lt_of_le_of_lt (eLpNorm_stft_le (w := w) (u := u) hw hu) hfinite_rhs
  have hmem :
      MemLp (fun p : ℝ × ℝ ↦ stft w u p.1 p.2) 2 (volume.prod volume) :=
    ⟨stft_aestronglyMeasurable_of_memLp (w := w) (u := u) hw hu, hfin⟩
  exact (memLp_two_iff_integrable_sq_norm
    (stft_aestronglyMeasurable_of_memLp (w := w) (u := u) hw hu)).mp hmem

theorem stft_sq_complex_integrable (hw : MemLp w 2 volume) (hu : MemLp u 2 volume) :
    Integrable (fun p : ℝ × ℝ ↦ ((‖stft w u p.1 p.2‖ ^ 2 : ℝ) : ℂ)) (volume.prod volume) := by
  simpa using (stft_sq_integrable (w := w) (u := u) hw hu).ofReal (𝕜 := ℂ)

private theorem stft_memLp (hw : MemLp w 2 volume) (hu : MemLp u 2 volume) :
    MemLp (fun p : ℝ × ℝ ↦ stft w u p.1 p.2) 2 (volume.prod volume) := by
  exact (memLp_two_iff_integrable_sq_norm
    (stft_aestronglyMeasurable_of_memLp (w := w) (u := u) hw hu)).2
      (stft_sq_integrable (w := w) (u := u) hw hu)

private theorem lpNorm_stft_le (hw : MemLp w 2 volume) (hu : MemLp u 2 volume) :
    lpNorm (fun p : ℝ × ℝ ↦ stft w u p.1 p.2) 2 (volume.prod volume) ≤
      lpNorm u 2 volume * lpNorm w 2 volume := by
  have hmem : MemLp (fun p : ℝ × ℝ ↦ stft w u p.1 p.2) 2 (volume.prod volume) :=
    stft_memLp (w := w) (u := u) hw hu
  rw [← MeasureTheory.toReal_eLpNorm hmem.aestronglyMeasurable]
  simpa using
    (ENNReal.toReal_le_toReal hmem.eLpNorm_ne_top ENNReal.ofReal_ne_top).mpr
      (eLpNorm_stft_le (w := w) (u := u) hw hu)

private theorem stft_sub_eq_add
    {w₁ w₂ u₁ u₂ : ℝ → ℂ}
    (hw₁ : MemLp w₁ 2 volume) (hw₂ : MemLp w₂ 2 volume)
    (hu₁ : MemLp u₁ 2 volume) (hu₂ : MemLp u₂ 2 volume)
    (x ω : ℝ) :
    stft w₁ u₁ x ω - stft w₂ u₂ x ω =
      stft w₁ (u₁ - u₂) x ω + stft (w₁ - w₂) u₂ x ω := by
  let phase : ℂ := (Real.fourierChar (-(ω * x / 2)) : ℂ)
  have hwsub : MemLp (w₁ - w₂) 2 volume := hw₁.sub hw₂
  have husub : MemLp (u₁ - u₂) 2 volume := hu₁.sub hu₂
  have hphase₁ := stft_eq_crossAmbiguity (w := w₁) (u := u₁) hw₁ hu₁ x ω
  have hphase₂ := stft_eq_crossAmbiguity (w := w₂) (u := u₂) hw₂ hu₂ x ω
  have hsplit :
      crossAmbiguity u₁ w₁ x ω - crossAmbiguity u₂ w₂ x ω =
        crossAmbiguity (u₁ - u₂) w₁ x ω + crossAmbiguity u₂ (w₁ - w₂) x ω := by
    calc
      crossAmbiguity u₁ w₁ x ω - crossAmbiguity u₂ w₂ x ω
          = (crossAmbiguity u₁ w₁ x ω - crossAmbiguity u₂ w₁ x ω) +
              (crossAmbiguity u₂ w₁ x ω - crossAmbiguity u₂ w₂ x ω) := by
                ring
      _ = crossAmbiguity (u₁ - u₂) w₁ x ω + crossAmbiguity u₂ (w₁ - w₂) x ω := by
            rw [← crossAmbiguity_sub_left hu₁ hu₂ hw₁ x ω,
              ← crossAmbiguity_sub_right hu₂ hw₁ hw₂ x ω]
  calc
    stft w₁ u₁ x ω - stft w₂ u₂ x ω
        = phase * crossAmbiguity u₁ w₁ x ω - phase * crossAmbiguity u₂ w₂ x ω := by
            rw [hphase₁, hphase₂]
    _ = phase * (crossAmbiguity u₁ w₁ x ω - crossAmbiguity u₂ w₂ x ω) := by
          ring
    _ = phase * (crossAmbiguity (u₁ - u₂) w₁ x ω + crossAmbiguity u₂ (w₁ - w₂) x ω) := by
          rw [hsplit]
    _ = phase * crossAmbiguity (u₁ - u₂) w₁ x ω + phase * crossAmbiguity u₂ (w₁ - w₂) x ω := by
          ring
    _ = stft w₁ (u₁ - u₂) x ω + phase * crossAmbiguity u₂ (w₁ - w₂) x ω := by
          rw [← stft_eq_crossAmbiguity (w := w₁) (u := u₁ - u₂) hw₁ husub x ω]
    _ = stft w₁ (u₁ - u₂) x ω + stft (w₁ - w₂) u₂ x ω := by
          rw [← stft_eq_crossAmbiguity (w := w₁ - w₂) (u := u₂) hwsub hu₂ x ω]

private theorem lpNorm_stft_sub_le
    {w₁ w₂ u₁ u₂ : ℝ → ℂ}
    (hw₁ : MemLp w₁ 2 volume) (hw₂ : MemLp w₂ 2 volume)
    (hu₁ : MemLp u₁ 2 volume) (hu₂ : MemLp u₂ 2 volume) :
    lpNorm (fun p : ℝ × ℝ ↦ stft w₁ u₁ p.1 p.2 - stft w₂ u₂ p.1 p.2) 2 (volume.prod volume) ≤
      lpNorm (u₁ - u₂) 2 volume * lpNorm w₁ 2 volume +
        lpNorm u₂ 2 volume * lpNorm (w₁ - w₂) 2 volume := by
  have hwsub : MemLp (w₁ - w₂) 2 volume := hw₁.sub hw₂
  have husub : MemLp (u₁ - u₂) 2 volume := hu₁.sub hu₂
  have hmem₁ : MemLp (fun p : ℝ × ℝ ↦ stft w₁ (u₁ - u₂) p.1 p.2) 2 (volume.prod volume) :=
    stft_memLp (w := w₁) (u := u₁ - u₂) hw₁ husub
  have hmem₂ : MemLp (fun p : ℝ × ℝ ↦ stft (w₁ - w₂) u₂ p.1 p.2) 2 (volume.prod volume) :=
    stft_memLp (w := w₁ - w₂) (u := u₂) hwsub hu₂
  calc
    lpNorm (fun p : ℝ × ℝ ↦ stft w₁ u₁ p.1 p.2 - stft w₂ u₂ p.1 p.2) 2 (volume.prod volume)
        = lpNorm
            ((fun p : ℝ × ℝ ↦ stft w₁ (u₁ - u₂) p.1 p.2) +
              fun p : ℝ × ℝ ↦ stft (w₁ - w₂) u₂ p.1 p.2)
            2 (volume.prod volume) := by
              congr 1
              funext p
              exact stft_sub_eq_add hw₁ hw₂ hu₁ hu₂ p.1 p.2
    _ ≤ lpNorm (fun p : ℝ × ℝ ↦ stft w₁ (u₁ - u₂) p.1 p.2) 2 (volume.prod volume) +
          lpNorm (fun p : ℝ × ℝ ↦ stft (w₁ - w₂) u₂ p.1 p.2) 2 (volume.prod volume) := by
            exact MeasureTheory.lpNorm_add_le hmem₁ (by norm_num)
    _ ≤ lpNorm (u₁ - u₂) 2 volume * lpNorm w₁ 2 volume +
          lpNorm u₂ 2 volume * lpNorm (w₁ - w₂) 2 volume := by
            gcongr
            · exact lpNorm_stft_le (w := w₁) (u := u₁ - u₂) hw₁ husub
            · exact lpNorm_stft_le (w := w₁ - w₂) (u := u₂) hwsub hu₂

private theorem lpNorm_stft_tendsto_schwartzApprox
    (hw : MemLp w 2 volume) (hu : MemLp u 2 volume) :
    Tendsto
      (fun n : ℕ ↦
        lpNorm
          (fun p : ℝ × ℝ ↦
            stft (schwartzApprox hw n) (schwartzApprox hu n) p.1 p.2 - stft w u p.1 p.2)
          2 (volume.prod volume))
      atTop (nhds 0) := by
  have herr_u :
      Tendsto (fun n : ℕ ↦ lpNorm ((schwartzApprox hu n : ℝ → ℂ) - u) 2 volume) atTop (nhds 0) := by
    simpa [MeasureTheory.lpNorm_sub_comm] using schwartzApprox_tendsto_lpNorm_sub_zero hu
  have herr_w :
      Tendsto (fun n : ℕ ↦ lpNorm ((schwartzApprox hw n : ℝ → ℂ) - w) 2 volume) atTop (nhds 0) := by
    simpa [MeasureTheory.lpNorm_sub_comm] using schwartzApprox_tendsto_lpNorm_sub_zero hw
  have hbound_tendsto :
      Tendsto
        (fun n : ℕ ↦
          lpNorm ((schwartzApprox hu n : ℝ → ℂ) - u) 2 volume * (lpNorm w 2 volume + 1) +
            lpNorm u 2 volume * lpNorm ((schwartzApprox hw n : ℝ → ℂ) - w) 2 volume)
        atTop (nhds 0) := by
    have h₁ :
        Tendsto
          (fun n : ℕ ↦
            lpNorm ((schwartzApprox hu n : ℝ → ℂ) - u) 2 volume * (lpNorm w 2 volume + 1))
          atTop (nhds 0) := by
      simpa [mul_comm] using herr_u.const_mul (lpNorm w 2 volume + 1)
    have h₂ :
        Tendsto
          (fun n : ℕ ↦ lpNorm u 2 volume * lpNorm ((schwartzApprox hw n : ℝ → ℂ) - w) 2 volume)
          atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul herr_w)
    simpa using h₁.add h₂
  refine squeeze_zero (fun n ↦ MeasureTheory.lpNorm_nonneg) ?_ hbound_tendsto
  intro n
  have hwN : MemLp (schwartzApprox hw n : ℝ → ℂ) 2 volume := (schwartzApprox hw n).memLp 2 volume
  have huN : MemLp (schwartzApprox hu n : ℝ → ℂ) 2 volume := (schwartzApprox hu n).memLp 2 volume
  calc
    lpNorm
        (fun p : ℝ × ℝ ↦
          stft (schwartzApprox hw n) (schwartzApprox hu n) p.1 p.2 - stft w u p.1 p.2)
        2 (volume.prod volume)
        ≤ lpNorm ((schwartzApprox hu n : ℝ → ℂ) - u) 2 volume *
            lpNorm (schwartzApprox hw n : ℝ → ℂ) 2 volume +
          lpNorm u 2 volume * lpNorm ((schwartzApprox hw n : ℝ → ℂ) - w) 2 volume := by
            exact lpNorm_stft_sub_le hwN hw huN hu
    _ ≤ lpNorm ((schwartzApprox hu n : ℝ → ℂ) - u) 2 volume * (lpNorm w 2 volume + 1) +
          lpNorm u 2 volume * lpNorm ((schwartzApprox hw n : ℝ → ℂ) - w) 2 volume := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left
                (schwartzApprox_lpNorm_le_add_one hw n)
                MeasureTheory.lpNorm_nonneg
            · exact le_rfl

private theorem lpNorm_stft_eq (hw : MemLp w 2 volume) (hu : MemLp u 2 volume) :
    lpNorm (fun p : ℝ × ℝ ↦ stft w u p.1 p.2) 2 (volume.prod volume) =
      lpNorm u 2 volume * lpNorm w 2 volume := by
  let F : ℝ × ℝ → ℂ := fun p ↦ stft w u p.1 p.2
  let Fₙ : ℕ → ℝ × ℝ → ℂ := fun n p ↦
    stft (schwartzApprox hw n) (schwartzApprox hu n) p.1 p.2
  have hdiff :
      Tendsto (fun n : ℕ ↦ lpNorm (fun p : ℝ × ℝ ↦ Fₙ n p - F p) 2 (volume.prod volume))
        atTop (nhds 0) := by
    simpa [F, Fₙ] using lpNorm_stft_tendsto_schwartzApprox (w := w) (u := u) hw hu
  have hnorm :
      Tendsto (fun n : ℕ ↦ lpNorm (Fₙ n) 2 (volume.prod volume))
        atTop (nhds (lpNorm F 2 (volume.prod volume))) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hbound :
        ∀ n : ℕ,
          |lpNorm (Fₙ n) 2 (volume.prod volume) - lpNorm F 2 (volume.prod volume)| ≤
            lpNorm (fun p : ℝ × ℝ ↦ Fₙ n p - F p) 2 (volume.prod volume) := by
      intro n
      have hwN : MemLp (schwartzApprox hw n : ℝ → ℂ) 2 volume :=
        (schwartzApprox hw n).memLp 2 volume
      have huN : MemLp (schwartzApprox hu n : ℝ → ℂ) 2 volume :=
        (schwartzApprox hu n).memLp 2 volume
      have hmemFn : MemLp (Fₙ n) 2 (volume.prod volume) := by
        dsimp [Fₙ]
        exact stft_memLp
          (w := (schwartzApprox hw n : ℝ → ℂ)) (u := (schwartzApprox hu n : ℝ → ℂ))
          hwN huN
      have hmemF : MemLp F 2 (volume.prod volume) := by
        dsimp [F]
        exact stft_memLp (w := w) (u := u) hw hu
      have h₁ :
          lpNorm (Fₙ n) 2 (volume.prod volume) ≤
            lpNorm F 2 (volume.prod volume) +
              lpNorm (fun p : ℝ × ℝ ↦ Fₙ n p - F p) 2 (volume.prod volume) := by
        exact
          MeasureTheory.lpNorm_le_lpNorm_add_lpNorm_sub' (f := Fₙ n) (g := F) hmemF (by norm_num)
      have h₂ :
          lpNorm F 2 (volume.prod volume) ≤
            lpNorm (Fₙ n) 2 (volume.prod volume) +
              lpNorm (fun p : ℝ × ℝ ↦ Fₙ n p - F p) 2 (volume.prod volume) := by
        have h₂' :
            lpNorm F 2 (volume.prod volume) ≤
              lpNorm (Fₙ n) 2 (volume.prod volume) + lpNorm (F - Fₙ n) 2 (volume.prod volume) :=
          MeasureTheory.lpNorm_le_lpNorm_add_lpNorm_sub' (f := F) (g := Fₙ n) hmemFn
            (by norm_num)
        have hsubcomm :
            lpNorm (F - Fₙ n) 2 (volume.prod volume) =
              lpNorm (fun p : ℝ × ℝ ↦ Fₙ n p - F p) 2 (volume.prod volume) := by
          dsimp [F, Fₙ]
          simpa using
            (MeasureTheory.lpNorm_sub_comm
              (f := fun p : ℝ × ℝ ↦ stft w u p.1 p.2)
              (g := fun p : ℝ × ℝ ↦ stft (schwartzApprox hw n) (schwartzApprox hu n) p.1 p.2)
              (p := (2 : ENNReal)) (μ := volume.prod volume))
        exact h₂'.trans_eq (by rw [hsubcomm])
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    simpa [Real.dist_eq] using squeeze_zero (fun n ↦ abs_nonneg _) hbound hdiff
  have hnorms :
      Tendsto
        (fun n : ℕ ↦
          lpNorm (Fₙ n) 2 (volume.prod volume))
        atTop (nhds (lpNorm u 2 volume * lpNorm w 2 volume)) := by
    simpa [Fₙ, lpNorm_stft_schwartz] using
      (schwartzApprox_tendsto_lpNorm hu).mul (schwartzApprox_tendsto_lpNorm hw)
  simpa [F] using tendsto_nhds_unique hnorm hnorms

theorem integral_stft_sq (hw : MemLp w 2 volume) (hu : MemLp u 2 volume) :
    ∫ x, ∫ ω, ‖stft w u x ω‖ ^ 2 =
      (eLpNorm u 2 volume).toReal ^ 2 * (eLpNorm w 2 volume).toReal ^ 2 := by
  let F : ℝ × ℝ → ℂ := fun p ↦ stft w u p.1 p.2
  have hcalc : (∫ x, ∫ ω, ‖stft w u x ω‖ ^ 2) ^ (1 / (2 : ℝ)) =
      lpNorm u 2 volume * lpNorm w 2 volume := by
    calc
      (∫ x, ∫ ω, ‖stft w u x ω‖ ^ 2) ^ (1 / (2 : ℝ))
          = lpNorm F 2 (volume.prod volume) := by
              symm
              rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
                (μ := volume.prod volume) (p := (2 : ENNReal))
                (by norm_num : (2 : ENNReal) ≠ 0)
                (by norm_num : (2 : ENNReal) ≠ ⊤)
                (stft_aestronglyMeasurable_of_memLp (w := w) (u := u) hw hu)]
              norm_num
              rw [(MeasureTheory.integral_integral
                (f := fun x ω : ℝ ↦ ‖stft w u x ω‖ ^ 2)
                (by simpa [Function.uncurry] using
                  stft_sq_integrable (w := w) (u := u) hw hu)).symm]
      _ = lpNorm u 2 volume * lpNorm w 2 volume := by
            simpa [F] using lpNorm_stft_eq (w := w) (u := u) hw hu
  rw [← Real.sqrt_eq_rpow] at hcalc
  have hint_nonneg : 0 ≤ ∫ x, ∫ ω, ‖stft w u x ω‖ ^ 2 := by
    refine integral_nonneg ?_
    intro x
    refine integral_nonneg ?_
    intro ω
    positivity
  have hsquare :
      Real.sqrt (∫ x, ∫ ω, ‖stft w u x ω‖ ^ 2) *
          Real.sqrt (∫ x, ∫ ω, ‖stft w u x ω‖ ^ 2) =
        (lpNorm u 2 volume * lpNorm w 2 volume) *
          (lpNorm u 2 volume * lpNorm w 2 volume) := by
    simpa [pow_two] using congrArg (fun z : ℝ ↦ z * z) hcalc
  rw [MeasureTheory.toReal_eLpNorm hu.aestronglyMeasurable,
    MeasureTheory.toReal_eLpNorm hw.aestronglyMeasurable]
  calc
    ∫ x, ∫ ω, ‖stft w u x ω‖ ^ 2
        = Real.sqrt (∫ x, ∫ ω, ‖stft w u x ω‖ ^ 2) *
            Real.sqrt (∫ x, ∫ ω, ‖stft w u x ω‖ ^ 2) := by
              symm
              simpa [pow_two] using (Real.sq_sqrt hint_nonneg)
    _ = (lpNorm u 2 volume * lpNorm w 2 volume) *
          (lpNorm u 2 volume * lpNorm w 2 volume) := hsquare
    _ = lpNorm u 2 volume ^ 2 * lpNorm w 2 volume ^ 2 := by
          ring

private theorem lpNorm_mul_le_real
    {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    lpNorm (fun x ↦ f x * g x) 1 μ ≤ lpNorm f 2 μ * lpNorm g 2 μ := by
  have hmem : MemLp (fun x ↦ f x * g x) 1 μ := by
    simpa [mul_comm] using hg.mul hf
  rw [MeasureTheory.lpNorm_one_eq_integral_norm hmem.aestronglyMeasurable]
  have hpq : Real.HolderConjugate 2 2 := by
    constructor <;> norm_num
  have hf_abs : MemLp (fun x ↦ |f x|) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa [Real.norm_eq_abs] using hf.norm
  have hg_abs : MemLp (fun x ↦ |g x|) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa [Real.norm_eq_abs] using hg.norm
  have hf_nonneg : 0 ≤ᵐ[μ] fun x ↦ |f x| :=
    Filter.Eventually.of_forall fun _ ↦ abs_nonneg _
  have hg_nonneg : 0 ≤ᵐ[μ] fun x ↦ |g x| :=
    Filter.Eventually.of_forall fun _ ↦ abs_nonneg _
  have hholder := @MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg α _ μ 2 2 hpq
    (fun x ↦ |f x|) (fun x ↦ |g x|) hf_nonneg hg_nonneg hf_abs hg_abs
  have hf_lp :
      (∫ x, |f x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = lpNorm f 2 μ := by
    have h := hf.eLpNorm_eq_integral_rpow_norm (μ := μ) (p := (2 : ENNReal))
      (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)
    norm_num at h
    have h' := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_ofReal (by positivity),
      MeasureTheory.toReal_eLpNorm hf.aestronglyMeasurable] at h'
    simpa [Real.norm_eq_abs] using h'.symm
  have hg_lp :
      (∫ x, |g x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = lpNorm g 2 μ := by
    have h := hg.eLpNorm_eq_integral_rpow_norm (μ := μ) (p := (2 : ENNReal))
      (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)
    norm_num at h
    have h' := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_ofReal (by positivity),
      MeasureTheory.toReal_eLpNorm hg.aestronglyMeasurable] at h'
    simpa [Real.norm_eq_abs] using h'.symm
  have hleft :
      ∫ x, ‖f x * g x‖ ∂μ = ∫ x, |f x| * |g x| ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with x
    simp [Real.norm_eq_abs]
  rw [hleft]
  rw [hf_lp, hg_lp] at hholder
  exact hholder

private theorem lpNorm_stft_sq_sub_tendsto_zero
    (hw : MemLp w 2 volume) (hu : MemLp u 2 volume) :
    Tendsto
      (fun n : ℕ ↦
        lpNorm
          (fun p : ℝ × ℝ ↦
            (((‖stft (schwartzApprox hw n) (schwartzApprox hu n) p.1 p.2‖ ^ 2 : ℝ) : ℂ) -
              ((‖stft w u p.1 p.2‖ ^ 2 : ℝ) : ℂ)))
          1 (volume.prod volume))
      atTop (nhds 0) := by
  let F : ℝ × ℝ → ℂ := fun p ↦ stft w u p.1 p.2
  let Fₙ : ℕ → ℝ × ℝ → ℂ := fun n p ↦
    stft (schwartzApprox hw n) (schwartzApprox hu n) p.1 p.2
  let Dₙ : ℕ → ℝ × ℝ → ℂ := fun n p ↦
    (((‖Fₙ n p‖ ^ 2 : ℝ) : ℂ) - ((‖F p‖ ^ 2 : ℝ) : ℂ))
  let Aₙ : ℕ → ℝ × ℝ → ℝ := fun n p ↦ ‖Fₙ n p‖ + ‖F p‖
  let Bₙ : ℕ → ℝ × ℝ → ℝ := fun n p ↦ ‖Fₙ n p - F p‖
  let C : ℝ :=
    (lpNorm u 2 volume + 1) * (lpNorm w 2 volume + 1) + lpNorm u 2 volume * lpNorm w 2 volume
  have hdiff :
      Tendsto (fun n : ℕ ↦ lpNorm (fun p : ℝ × ℝ ↦ Fₙ n p - F p) 2 (volume.prod volume))
        atTop (nhds 0) := by
    simpa [F, Fₙ] using lpNorm_stft_tendsto_schwartzApprox (w := w) (u := u) hw hu
  have hCtendsto :
      Tendsto
        (fun n : ℕ ↦ C * lpNorm (fun p : ℝ × ℝ ↦ Fₙ n p - F p) 2 (volume.prod volume))
        atTop (nhds 0) := by
    simpa [C] using (tendsto_const_nhds.mul hdiff)
  refine squeeze_zero (fun n ↦ MeasureTheory.lpNorm_nonneg) ?_ hCtendsto
  intro n
  have hwN : MemLp (schwartzApprox hw n : ℝ → ℂ) 2 volume := (schwartzApprox hw n).memLp 2 volume
  have huN : MemLp (schwartzApprox hu n : ℝ → ℂ) 2 volume := (schwartzApprox hu n).memLp 2 volume
  have hmemFn : MemLp (Fₙ n) 2 (volume.prod volume) := by
    dsimp [Fₙ]
    exact stft_memLp (w := (schwartzApprox hw n : ℝ → ℂ)) (u := (schwartzApprox hu n : ℝ → ℂ))
      hwN huN
  have hmemF : MemLp F 2 (volume.prod volume) := by
    dsimp [F]
    exact stft_memLp (w := w) (u := u) hw hu
  have hmemDiff : MemLp (fun p : ℝ × ℝ ↦ Fₙ n p - F p) 2 (volume.prod volume) := hmemFn.sub hmemF
  have hAmem : MemLp (Aₙ n) 2 (volume.prod volume) := by
    dsimp [Aₙ]
    exact hmemFn.norm.add hmemF.norm
  have hBmem : MemLp (Bₙ n) 2 (volume.prod volume) := by
    dsimp [Bₙ]
    exact hmemDiff.norm
  have hHmem : MemLp (fun p : ℝ × ℝ ↦ Aₙ n p * Bₙ n p) 1 (volume.prod volume) := by
    simpa [Aₙ, Bₙ, Pi.mul_apply] using
      (hBmem.mul hAmem : MemLp (Aₙ n * Bₙ n) 1 (volume.prod volume))
  have hpoint :
      ∀ p : ℝ × ℝ, ‖Dₙ n p‖ ≤ Aₙ n p * Bₙ n p := by
    intro p
    have hsum_nonneg : 0 ≤ ‖Fₙ n p‖ + ‖F p‖ := by positivity
    calc
      ‖Dₙ n p‖ = ‖(((‖Fₙ n p‖ ^ 2 : ℝ) : ℂ) - ((‖F p‖ ^ 2 : ℝ) : ℂ))‖ := by
        rfl
      _ = |‖Fₙ n p‖ ^ 2 - ‖F p‖ ^ 2| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      _ = (‖Fₙ n p‖ + ‖F p‖) * |‖Fₙ n p‖ - ‖F p‖| := by
        rw [sq_sub_sq, abs_mul, abs_of_nonneg hsum_nonneg]
      _ ≤ (‖Fₙ n p‖ + ‖F p‖) * ‖Fₙ n p - F p‖ := by
        exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le _ _) hsum_nonneg
      _ = Aₙ n p * Bₙ n p := by
        simp [Aₙ, Bₙ]
  have hD_le :
      lpNorm (Dₙ n) 1 (volume.prod volume) ≤
        lpNorm (fun p : ℝ × ℝ ↦ Aₙ n p * Bₙ n p) 1 (volume.prod volume) :=
    MeasureTheory.lpNorm_mono_real hHmem hpoint
  have hAB_le :
      lpNorm (fun p : ℝ × ℝ ↦ Aₙ n p * Bₙ n p) 1 (volume.prod volume) ≤
        lpNorm (Aₙ n) 2 (volume.prod volume) * lpNorm (Bₙ n) 2 (volume.prod volume) :=
    lpNorm_mul_le_real hAmem hBmem
  have hA_le :
      lpNorm (Aₙ n) 2 (volume.prod volume) ≤ C := by
    calc
      lpNorm (Aₙ n) 2 (volume.prod volume)
          ≤ lpNorm (fun p : ℝ × ℝ ↦ ‖Fₙ n p‖) 2 (volume.prod volume) +
              lpNorm (fun p : ℝ × ℝ ↦ ‖F p‖) 2 (volume.prod volume) := by
                dsimp [Aₙ]
                exact
                  MeasureTheory.lpNorm_add_le hmemFn.norm
                    (g := fun p : ℝ × ℝ ↦ ‖F p‖) (by norm_num)
      _ = lpNorm (Fₙ n) 2 (volume.prod volume) + lpNorm F 2 (volume.prod volume) := by
            simp [MeasureTheory.lpNorm_norm, hmemFn.aestronglyMeasurable,
              hmemF.aestronglyMeasurable]
      _ = lpNorm (schwartzApprox hu n : ℝ → ℂ) 2 volume *
            lpNorm (schwartzApprox hw n : ℝ → ℂ) 2 volume +
          lpNorm u 2 volume * lpNorm w 2 volume := by
            rw [show lpNorm (Fₙ n) 2 (volume.prod volume) =
                lpNorm (fun p : ℝ × ℝ ↦
                  stft (schwartzApprox hw n) (schwartzApprox hu n) p.1 p.2) 2
                  (volume.prod volume) by
                  rfl,
              lpNorm_stft_schwartz,
              show lpNorm F 2 (volume.prod volume) =
                lpNorm (fun p : ℝ × ℝ ↦ stft w u p.1 p.2) 2 (volume.prod volume) by
                  rfl,
              lpNorm_stft_eq (w := w) (u := u) hw hu]
      _ ≤ (lpNorm u 2 volume + 1) * (lpNorm w 2 volume + 1) +
          lpNorm u 2 volume * lpNorm w 2 volume := by
            refine add_le_add ?_ le_rfl
            have happrox_nonneg : 0 ≤ lpNorm (schwartzApprox hw n : ℝ → ℂ) 2 volume :=
              MeasureTheory.lpNorm_nonneg
            have hu_bound_nonneg : 0 ≤ lpNorm u 2 volume + 1 :=
              add_nonneg MeasureTheory.lpNorm_nonneg zero_le_one
            exact mul_le_mul
              (schwartzApprox_lpNorm_le_add_one hu n)
              (schwartzApprox_lpNorm_le_add_one hw n)
              happrox_nonneg
              hu_bound_nonneg
  calc
    lpNorm (Dₙ n) 1 (volume.prod volume)
        ≤ lpNorm (fun p : ℝ × ℝ ↦ Aₙ n p * Bₙ n p) 1 (volume.prod volume) := hD_le
    _ ≤ lpNorm (Aₙ n) 2 (volume.prod volume) * lpNorm (Bₙ n) 2 (volume.prod volume) := hAB_le
    _ ≤ C * lpNorm (fun p : ℝ × ℝ ↦ Fₙ n p - F p) 2 (volume.prod volume) := by
          rw [show lpNorm (Bₙ n) 2 (volume.prod volume) =
              lpNorm (fun p : ℝ × ℝ ↦ Fₙ n p - F p) 2 (volume.prod volume) by
                simp [Bₙ, MeasureTheory.lpNorm_norm, hmemDiff.aestronglyMeasurable]]
          exact mul_le_mul_of_nonneg_right hA_le MeasureTheory.lpNorm_nonneg

private theorem ambiguity_tendsto_schwartzApprox
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) (x ω : ℝ) :
    Tendsto (fun n : ℕ ↦ ambiguity (schwartzApprox hf n : ℝ → ℂ) x ω) atTop
      (nhds (ambiguity f x ω)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have herr :
      Tendsto (fun n : ℕ ↦ lpNorm ((schwartzApprox hf n : ℝ → ℂ) - f) 2 volume) atTop (nhds 0) := by
    simpa [MeasureTheory.lpNorm_sub_comm] using schwartzApprox_tendsto_lpNorm_sub_zero hf
  have hbound_tendsto :
      Tendsto
        (fun n : ℕ ↦
          2 * lpNorm f 2 volume * lpNorm ((schwartzApprox hf n : ℝ → ℂ) - f) 2 volume +
            lpNorm ((schwartzApprox hf n : ℝ → ℂ) - f) 2 volume ^ 2)
        atTop (nhds 0) := by
    have h₁ :
        Tendsto
          (fun n : ℕ ↦ 2 * lpNorm f 2 volume * lpNorm ((schwartzApprox hf n : ℝ → ℂ) - f) 2 volume)
          atTop (nhds 0) := by
      have h₁' :
          Tendsto
            (fun n : ℕ ↦
              (2 * lpNorm f 2 volume) * lpNorm ((schwartzApprox hf n : ℝ → ℂ) - f) 2 volume)
            atTop (nhds ((2 * lpNorm f 2 volume) * 0)) := by
        exact tendsto_const_nhds.mul herr
      have h₁'' :
          Tendsto
            (fun n : ℕ ↦
              (2 * lpNorm f 2 volume) * lpNorm ((schwartzApprox hf n : ℝ → ℂ) - f) 2 volume)
            atTop (nhds 0) := by
        simpa using h₁'
      simpa [mul_assoc] using h₁''
    have h₂ :
        Tendsto
          (fun n : ℕ ↦ lpNorm ((schwartzApprox hf n : ℝ → ℂ) - f) 2 volume ^ 2)
          atTop (nhds 0) := by
      simpa using herr.pow 2
    simpa using h₁.add h₂
  refine squeeze_zero (fun n ↦ norm_nonneg _) ?_ hbound_tendsto
  intro n
  have hs : MemLp (schwartzApprox hf n : ℝ → ℂ) 2 volume := (schwartzApprox hf n).memLp 2 volume
  have herrMem : MemLp ((schwartzApprox hf n : ℝ → ℂ) - f) 2 volume := hs.sub hf
  have hdecompAmb :
      ambiguity (schwartzApprox hf n : ℝ → ℂ) x ω =
        ambiguity (f + ((schwartzApprox hf n : ℝ → ℂ) - f)) x ω := by
    congr 1
    funext t
    simp
  calc
    ‖ambiguity (schwartzApprox hf n : ℝ → ℂ) x ω - ambiguity f x ω‖
        = ‖ambiguity (f + ((schwartzApprox hf n : ℝ → ℂ) - f)) x ω - ambiguity f x ω‖ := by
            rw [hdecompAmb]
    _ ≤ 2 * (eLpNorm f 2 volume).toReal *
          (eLpNorm ((schwartzApprox hf n : ℝ → ℂ) - f) 2 volume).toReal +
          (eLpNorm ((schwartzApprox hf n : ℝ → ℂ) - f) 2 volume).toReal ^ 2 := by
            exact ambiguity_sub_le (f := f) (u := (schwartzApprox hf n : ℝ → ℂ) - f) hf herrMem x ω
    _ = 2 * lpNorm f 2 volume * lpNorm ((schwartzApprox hf n : ℝ → ℂ) - f) 2 volume +
          lpNorm ((schwartzApprox hf n : ℝ → ℂ) - f) 2 volume ^ 2 := by
            rw [MeasureTheory.toReal_eLpNorm hf.aestronglyMeasurable,
              MeasureTheory.toReal_eLpNorm herrMem.aestronglyMeasurable]

private theorem symplecticFourier_sub_le_lpNorm_one
    {G₁ G₂ : ℝ → ℝ → ℂ}
    (h1 : Integrable (fun p : ℝ × ℝ ↦ G₁ p.1 p.2) (volume.prod volume))
    (h2 : Integrable (fun p : ℝ × ℝ ↦ G₂ p.1 p.2) (volume.prod volume))
    (x ω : ℝ) :
    ‖symplecticFourier G₁ x ω - symplecticFourier G₂ x ω‖ ≤
      lpNorm (fun p : ℝ × ℝ ↦ G₁ p.1 p.2 - G₂ p.1 p.2) 1 (volume.prod volume) := by
  let φ : ℝ × ℝ → ℂ := fun p ↦ (Real.fourierChar (-(ω * p.1 - x * p.2)) : ℂ)
  have hφ_meas : AEStronglyMeasurable φ (volume.prod volume) := by
    exact (by fun_prop : Measurable φ).aestronglyMeasurable
  have hφ_bound : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), ‖φ p‖ ≤ (1 : ℝ) := by
    filter_upwards [Filter.Eventually.of_forall
      (fun p : ℝ × ℝ ↦ norm_fourierChar (-(ω * p.1 - x * p.2)))] with p hp
    exact le_of_eq hp
  have hdiff : Integrable (fun p : ℝ × ℝ ↦ G₁ p.1 p.2 - G₂ p.1 p.2) (volume.prod volume) :=
    h1.sub h2
  have h1φ : Integrable (fun p : ℝ × ℝ ↦ G₁ p.1 p.2 * φ p) (volume.prod volume) :=
    h1.mul_bdd hφ_meas hφ_bound
  have h2φ : Integrable (fun p : ℝ × ℝ ↦ G₂ p.1 p.2 * φ p) (volume.prod volume) :=
    h2.mul_bdd hφ_meas hφ_bound
  have hdiffφ :
      Integrable (fun p : ℝ × ℝ ↦ (G₁ p.1 p.2 - G₂ p.1 p.2) * φ p) (volume.prod volume) :=
    hdiff.mul_bdd hφ_meas hφ_bound
  calc
    ‖symplecticFourier G₁ x ω - symplecticFourier G₂ x ω‖
        = ‖∫ p : ℝ × ℝ, (G₁ p.1 p.2 - G₂ p.1 p.2) * φ p ∂(volume.prod volume)‖ := by
            unfold symplecticFourier
            rw [← MeasureTheory.integral_prod (f := fun p : ℝ × ℝ ↦ G₁ p.1 p.2 * φ p) h1φ,
              ← MeasureTheory.integral_prod (f := fun p : ℝ × ℝ ↦ G₂ p.1 p.2 * φ p) h2φ,
              ← MeasureTheory.integral_sub h1φ h2φ]
            have hfun :
                (fun p : ℝ × ℝ ↦ G₁ p.1 p.2 * φ p - G₂ p.1 p.2 * φ p) =
                  (fun p : ℝ × ℝ ↦ (G₁ p.1 p.2 - G₂ p.1 p.2) * φ p) := by
              funext p
              simp [sub_mul]
            rw [hfun]
    _ ≤ ∫ p : ℝ × ℝ, ‖(G₁ p.1 p.2 - G₂ p.1 p.2) * φ p‖ ∂(volume.prod volume) := by
          exact norm_integral_le_integral_norm _
    _ = ∫ p : ℝ × ℝ, ‖G₁ p.1 p.2 - G₂ p.1 p.2‖ ∂(volume.prod volume) := by
          refine integral_congr_ae ?_
          filter_upwards [Filter.Eventually.of_forall
            (fun p : ℝ × ℝ ↦ norm_fourierChar (-(ω * p.1 - x * p.2)))] with p hp
          simp [φ]
    _ = lpNorm (fun p : ℝ × ℝ ↦ G₁ p.1 p.2 - G₂ p.1 p.2) 1 (volume.prod volume) := by
          symm
          exact MeasureTheory.lpNorm_one_eq_integral_norm hdiff.aestronglyMeasurable

theorem symplecticFourier_stft_sq
    (hw : MemLp w 2 volume) (hu : MemLp u 2 volume) (x ω : ℝ) :
    symplecticFourier (fun y η ↦ ((‖stft w u y η‖ ^ 2 : ℝ) : ℂ)) x ω =
      ambiguity u x ω * star (ambiguity w x ω) := by
  let G : ℝ → ℝ → ℂ := fun y η ↦ ((‖stft w u y η‖ ^ 2 : ℝ) : ℂ)
  let Gₙ : ℕ → ℝ → ℝ → ℂ := fun n y η ↦
    ((‖stft (schwartzApprox hw n) (schwartzApprox hu n) y η‖ ^ 2 : ℝ) : ℂ)
  have hleft :
      Tendsto (fun n : ℕ ↦ symplecticFourier (Gₙ n) x ω) atTop
        (nhds (symplecticFourier G x ω)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hG : Integrable (fun p : ℝ × ℝ ↦ G p.1 p.2) (volume.prod volume) := by
      simpa [G] using stft_sq_complex_integrable (w := w) (u := u) hw hu
    have hGₙ :
        ∀ n : ℕ, Integrable (fun p : ℝ × ℝ ↦ Gₙ n p.1 p.2) (volume.prod volume) := by
      intro n
      simpa [Gₙ] using
        stft_sq_complex_integrable
          (w := (schwartzApprox hw n : ℝ → ℂ)) (u := (schwartzApprox hu n : ℝ → ℂ))
          ((schwartzApprox hw n).memLp 2 volume) ((schwartzApprox hu n).memLp 2 volume)
    refine
      squeeze_zero (fun n ↦ norm_nonneg _) ?_
        (lpNorm_stft_sq_sub_tendsto_zero (w := w) (u := u) hw hu)
    intro n
    simpa [G, Gₙ] using
      symplecticFourier_sub_le_lpNorm_one (G₁ := Gₙ n) (G₂ := G) (h1 := hGₙ n) (h2 := hG) x ω
  have huRight :
      Tendsto (fun n : ℕ ↦ ambiguity (schwartzApprox hu n : ℝ → ℂ) x ω) atTop
        (nhds (ambiguity u x ω)) :=
    ambiguity_tendsto_schwartzApprox (f := u) hu x ω
  have hwRight :
      Tendsto (fun n : ℕ ↦ ambiguity (schwartzApprox hw n : ℝ → ℂ) x ω) atTop
        (nhds (ambiguity w x ω)) :=
    ambiguity_tendsto_schwartzApprox (f := w) hw x ω
  have hwStar :
      Tendsto (fun n : ℕ ↦ star (ambiguity (schwartzApprox hw n : ℝ → ℂ) x ω)) atTop
        (nhds (star (ambiguity w x ω))) := by
    exact (continuous_star.tendsto (ambiguity w x ω)).comp hwRight
  have hright :
      Tendsto
        (fun n : ℕ ↦ ambiguity (schwartzApprox hu n : ℝ → ℂ) x ω *
          star (ambiguity (schwartzApprox hw n : ℝ → ℂ) x ω))
        atTop (nhds (ambiguity u x ω * star (ambiguity w x ω))) := by
    exact huRight.mul hwStar
  have hright' :
      Tendsto (fun n : ℕ ↦ symplecticFourier (Gₙ n) x ω) atTop
        (nhds (ambiguity u x ω * star (ambiguity w x ω))) := by
    have hEq :
        (fun n : ℕ ↦ symplecticFourier (Gₙ n) x ω) =
          fun n : ℕ ↦ ambiguity (schwartzApprox hu n : ℝ → ℂ) x ω *
            star (ambiguity (schwartzApprox hw n : ℝ → ℂ) x ω) := by
              funext n
              simpa [Gₙ] using
                symplecticFourier_stft_sq_schwartz (schwartzApprox hw n) (schwartzApprox hu n) x ω
    rw [hEq]
    exact hright
  exact tendsto_nhds_unique hleft hright'

theorem stft_sq_eq_implies_ambiguity_eq
    (hw : MemLp w 2 volume) (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (h : ∀ x ω, ‖stft w u x ω‖ = ‖stft w v x ω‖) :
    ∀ x ω, (ambiguity u x ω - ambiguity v x ω) * star (ambiguity w x ω) = 0 := by
  intro x ω
  have hSF :
      symplecticFourier (fun y η ↦ ((‖stft w u y η‖ ^ 2 : ℝ) : ℂ)) x ω =
        symplecticFourier (fun y η ↦ ((‖stft w v y η‖ ^ 2 : ℝ) : ℂ)) x ω := by
    simp [symplecticFourier, h]
  rw [symplecticFourier_stft_sq (w := w) (u := u) hw hu x ω,
    symplecticFourier_stft_sq (w := w) (u := v) hw hv x ω] at hSF
  calc
    (ambiguity u x ω - ambiguity v x ω) * star (ambiguity w x ω)
        = ambiguity u x ω * star (ambiguity w x ω) -
            ambiguity v x ω * star (ambiguity w x ω) := by
              ring
    _ = 0 := by
      rw [hSF]
      ring

theorem stft_sq_eq_implies_ambiguity_eq_schwartz
    (w u v : SchwartzMap ℝ ℂ)
    (h : ∀ x ω, ‖stft w u x ω‖ = ‖stft w v x ω‖) :
    ∀ x ω, (ambiguity u x ω - ambiguity v x ω) * star (ambiguity w x ω) = 0 := by
  intro x ω
  have hSF :
      symplecticFourier (fun y η ↦ ((‖stft w u y η‖ ^ 2 : ℝ) : ℂ)) x ω =
        symplecticFourier (fun y η ↦ ((‖stft w v y η‖ ^ 2 : ℝ) : ℂ)) x ω := by
    simp [symplecticFourier, h]
  rw [symplecticFourier_stft_sq_schwartz w u x ω,
    symplecticFourier_stft_sq_schwartz w v x ω] at hSF
  calc
    (ambiguity u x ω - ambiguity v x ω) * star (ambiguity w x ω)
        = ambiguity u x ω * star (ambiguity w x ω) -
            ambiguity v x ω * star (ambiguity w x ω) := by
              ring_nf
    _ = 0 := by
      rw [hSF]
      ring_nf

theorem stft_continuous (hw : MemLp w 2 volume) (hu : MemLp u 2 volume) :
    Continuous (fun p : ℝ × ℝ ↦ stft w u p.1 p.2) := by
  have hcont1 : Continuous (fun p : ℝ × ℝ ↦ (Real.fourierChar (-(p.2 * p.1 / 2)) : ℂ)) := by
    exact (continuous_subtype_val.comp
      (by simpa using
        (Real.continuous_fourierChar.comp
          (by fun_prop : Continuous fun p : ℝ × ℝ ↦ -(p.2 * p.1 / 2)))))
  have hcont2 : Continuous (fun p : ℝ × ℝ ↦ crossAmbiguity u w p.1 p.2) :=
    crossAmbiguity_continuous (f := u) (g := w) hu hw
  have hcont : Continuous (fun p : ℝ × ℝ ↦
      (Real.fourierChar (-(p.2 * p.1 / 2)) : ℂ) * crossAmbiguity u w p.1 p.2) := hcont1.mul hcont2
  have hEq : (fun p : ℝ × ℝ ↦ stft w u p.1 p.2) =
      fun p : ℝ × ℝ ↦ (Real.fourierChar (-(p.2 * p.1 / 2)) : ℂ) * crossAmbiguity u w p.1 p.2 := by
    funext p
    simpa [stft] using stft_eq_crossAmbiguity (w := w) (u := u) hw hu p.1 p.2
  rw [hEq]
  exact hcont

theorem stft_aestronglyMeasurable
    (hw : MemLp w 2 volume) (hu : MemLp u 2 volume) :
    AEStronglyMeasurable (fun p : ℝ × ℝ ↦ stft w u p.1 p.2) (volume.prod volume) := by
  exact (stft_continuous (w := w) (u := u) hw hu).aestronglyMeasurable

theorem stft_measurable
    (hw : MemLp w 2 volume) (hu : MemLp u 2 volume) :
    Measurable (fun p : ℝ × ℝ ↦ stft w u p.1 p.2) := by
  exact (stft_continuous (w := w) (u := u) hw hu).measurable

theorem stft_sq_measurable (hw : MemLp w 2 volume) (hu : MemLp u 2 volume) :
    Measurable (fun p : ℝ × ℝ ↦ ‖stft w u p.1 p.2‖ ^ 2) := by
  have hcont : Continuous (fun p : ℝ × ℝ ↦ ‖stft w u p.1 p.2‖) :=
    (stft_continuous (w := w) (u := u) hw hu).norm
  exact (hcont.pow 2).measurable

theorem stft_sq_aestronglyMeasurable (hw : MemLp w 2 volume) (hu : MemLp u 2 volume) :
    AEStronglyMeasurable (fun p : ℝ × ℝ ↦ ‖stft w u p.1 p.2‖ ^ 2) (volume.prod volume) := by
  exact ((stft_continuous (w := w) (u := u) hw hu).norm.pow 2).aestronglyMeasurable

private theorem stft_slice_product_integrable
    (x y : ℝ)
    (hsliceL2 : MemLp (fun t ↦ u t * star (w (t - y))) 2 volume) :
    Integrable
      (fun t ↦ (u (t + x / 2) * star (w (t + x / 2 - y))) *
        star (u (t - x / 2) * star (w (t - x / 2 - y)))) volume := by
  let s : ℝ → ℂ := fun t ↦ u t * star (w (t - y))
  have hsL2 : MemLp s 2 volume := by
    simpa [s] using hsliceL2
  have hsL2_left : MemLp (translate (-x / 2) s) 2 volume := translate_memLp (-x / 2) hsL2
  have hsL2_right : MemLp (translate (x / 2) s) 2 volume := translate_memLp (x / 2) hsL2
  have h :
      Integrable (fun t ↦ star (translate (x / 2) s t) * translate (-x / 2) s t) volume := by
    exact integrable_mul_of_memLp (conj_memLp hsL2_right) hsL2_left
  convert h using 1
  funext t
  have hx₁ : t + -(-x / 2) = t + x / 2 := by ring
  simp [s, translate, sub_eq_add_neg, star_mul, hx₁, mul_left_comm, mul_comm]

theorem stft_slice_parseval_shift
    (_hw : MemLp w 2 volume) (_hu : MemLp u 2 volume)
    (x y : ℝ) (hsliceL2 : MemLp (fun t ↦ u t * star (w (t - y))) 2 volume) :
    let s : ℝ → ℂ := fun t ↦ u t * star (w (t - y))
    inner ℂ
        (FourierTransform.fourier ((translate_memLp (x / 2) hsliceL2).toLp
          (translate (x / 2) s)))
        (FourierTransform.fourier ((translate_memLp (-x / 2) hsliceL2).toLp
          (translate (-x / 2) s))) =
      inner ℂ ((translate_memLp (x / 2) hsliceL2).toLp (translate (x / 2) s))
        ((translate_memLp (-x / 2) hsliceL2).toLp (translate (-x / 2) s)) := by
  -- Auxiliary `Lp` identity for a fixed slice; the primary STFT route is now
  -- Schwartz-first with density, so this is no longer a foundational API lemma.
  dsimp
  exact
    MeasureTheory.Lp.inner_fourier_eq
      (f := (translate_memLp (x / 2) hsliceL2).toLp
        (translate (x / 2) fun t ↦ u t * star (w (t - y))))
      (g := (translate_memLp (-x / 2) hsliceL2).toLp
        (translate (-x / 2) fun t ↦ u t * star (w (t - y))))

end

end AmbiguityZeros.ToMathlib
