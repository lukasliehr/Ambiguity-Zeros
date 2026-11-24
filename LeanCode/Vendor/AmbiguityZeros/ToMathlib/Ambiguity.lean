module

public import AmbiguityZeros.ToMathlib.TranslationModulation

@[expose] public section

namespace AmbiguityZeros.ToMathlib

noncomputable section

open MeasureTheory

variable {f g f₁ f₂ u v : ℝ → ℂ}

def crossAmbiguity (f g : ℝ → ℂ) (x ω : ℝ) : ℂ :=
  ∫ t, f (t + x / 2) * star (g (t - x / 2)) * (Real.fourierChar (-(ω * t)) : ℂ)

def ambiguity (f : ℝ → ℂ) : ℝ → ℝ → ℂ :=
  crossAmbiguity f f

theorem crossAmbiguity_eq_integral (_hf : MemLp f 2 volume) (_hg : MemLp g 2 volume)
    (x ω : ℝ) :
    crossAmbiguity f g x ω =
      (Real.fourierChar (ω * x / 2) : ℂ) *
        ∫ t, f t * star ((modulate ω (translate x g)) t) := by
  have hchar : ∀ t : ℝ,
      (Real.fourierChar (ω * x / 2 - ω * t) : ℂ) =
        (Real.fourierChar (ω * x / 2) : ℂ) * (Real.fourierChar (-ω * t) : ℂ) := by
    intro t
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc, mul_left_comm, mul_comm]
      using congrArg (fun z : Circle => (z : ℂ))
        (Real.fourierChar.map_add_eq_mul (ω * x / 2) (-ω * t))
  have hshift :
      ∫ t, f (t + x / 2) * star (g (t - x / 2)) * (Real.fourierChar (-(ω * t)) : ℂ) =
        ∫ t, f t * star (g (t - x)) * (Real.fourierChar (ω * x / 2 - ω * t) : ℂ) := by
    have h := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (f := fun t : ℝ =>
        f t * star (g (t - x)) * (Real.fourierChar (ω * x / 2 - ω * t) : ℂ))
      (x / 2)
    ring_nf at h
    simpa [div_eq_mul_inv, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc, add_comm,
      add_left_comm, add_assoc] using h
  have hfactor :
      ∫ t, f t * star (g (t - x)) * (Real.fourierChar (ω * x / 2 - ω * t) : ℂ) =
        (Real.fourierChar (ω * x / 2) : ℂ) *
          ∫ t, f t * star ((modulate ω (translate x g)) t) := by
    have hchar' : ∀ t : ℝ,
        (Real.fourierChar (ω * x / 2 - ω * t) : ℂ) =
          (Real.fourierChar (ω * x / 2) : ℂ) * (Real.fourierChar (-ω * t) : ℂ) := by
      intro t
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc, mul_left_comm, mul_comm]
        using congrArg (fun z : Circle => (z : ℂ))
          (Real.fourierChar.map_add_eq_mul (ω * x / 2) (-ω * t))
    calc
      ∫ t, f t * star (g (t - x)) * (Real.fourierChar (ω * x / 2 - ω * t) : ℂ)
          = ∫ t, (Real.fourierChar (ω * x / 2) : ℂ) *
              (f t * star (g (t - x)) * (Real.fourierChar (-ω * t) : ℂ)) := by
                congr with t
                rw [hchar']
                ring_nf
      _ = (Real.fourierChar (ω * x / 2) : ℂ) *
            ∫ t, f t * star (g (t - x)) * (Real.fourierChar (-ω * t) : ℂ) := by
                simpa [mul_assoc] using
                  (MeasureTheory.integral_const_mul
                    (r := (Real.fourierChar (ω * x / 2) : ℂ))
                    (f := fun t : ℝ =>
                      f t * star (g (t - x)) * (Real.fourierChar (-ω * t) : ℂ)))
      _ = (Real.fourierChar (ω * x / 2) : ℂ) *
            ∫ t, f t * star ((modulate ω (translate x g)) t) := by
                simp [modulate, translate, mul_assoc, mul_comm]
  calc
    crossAmbiguity f g x ω =
        ∫ t, f (t + x / 2) * star (g (t - x / 2)) * (Real.fourierChar (-(ω * t)) : ℂ) := rfl
    _ = ∫ t, f t * star (g (t - x)) * (Real.fourierChar (ω * x / 2 - ω * t) : ℂ) := hshift
    _ = (Real.fourierChar (ω * x / 2) : ℂ) *
          ∫ t, f t * star ((modulate ω (translate x g)) t) := hfactor

theorem crossAmbiguity_eq_inner'
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (x ω : ℝ) :
    crossAmbiguity f g x ω =
      (Real.fourierChar (ω * x / 2) : ℂ) *
        inner ℂ (modulateLp ω (translateLp x (hg.toLp g))) (hf.toLp f) := by
  have hmod :
      modulateLp ω (translateLp x (hg.toLp g)) =
        (modulate_memLp ω (translate_memLp x hg)).toLp (modulate ω (translate x g)) := by
    rw [translateLp_toLp x hg]
    simpa using (modulateLp_toLp ω (f := translate x g) (hf := translate_memLp x hg))
  rw [crossAmbiguity_eq_integral hf hg x ω, hmod, MeasureTheory.L2.inner_def]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp,
    (modulate_memLp ω (translate_memLp x hg)).coeFn_toLp] with t hft hgt
  simp [hft, hgt]

private theorem crossAmbiguity_integrand_integrable
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (x ω : ℝ) :
    Integrable (fun t ↦ f (t + x / 2) * star (g (t - x / 2)) *
      (Real.fourierChar (-(ω * t)) : ℂ)) volume := by
  have hx : -(-x / 2) = x / 2 := by ring_nf
  have h0 : Integrable (fun t ↦ f (t - -x / 2) * star (g (t - x / 2))) volume := by
    simpa [translate, hx] using
      integrable_mul_of_memLp (translate_memLp (-x / 2) hf)
        (conj_memLp (translate_memLp (x / 2) hg))
  have hslice : Integrable (fun t ↦ f (t + x / 2) * star (g (t - x / 2))) volume := by
    change Integrable (fun t ↦ f (t + x / 2) * star (g (t - x / 2))) volume
    simpa [sub_eq_add_neg, hx, add_comm, add_left_comm, add_assoc] using h0
  have hchar : AEStronglyMeasurable (fun t ↦ (Real.fourierChar (-(ω * t)) : ℂ)) volume := by
    fun_prop
  have hbound : ∀ᵐ t ∂volume, ‖(Real.fourierChar (-(ω * t)) : ℂ)‖ ≤ (1 : ℝ) := by
    filter_upwards [Filter.Eventually.of_forall (fun t ↦ norm_fourierChar (-(ω * t)))] with t ht
    exact le_of_eq ht
  simpa [mul_assoc] using hslice.mul_bdd hchar hbound

theorem crossAmbiguity_add_left
    (hf₁ : MemLp f₁ 2 volume) (hf₂ : MemLp f₂ 2 volume) (hg : MemLp g 2 volume)
    (x ω : ℝ) :
    crossAmbiguity (f₁ + f₂) g x ω = crossAmbiguity f₁ g x ω + crossAmbiguity f₂ g x ω := by
  have h1 : Integrable (fun t ↦ f₁ (t + x / 2) * star (g (t - x / 2)) *
      (Real.fourierChar (-(ω * t)) : ℂ)) volume :=
    crossAmbiguity_integrand_integrable hf₁ hg x ω
  have h2 : Integrable (fun t ↦ f₂ (t + x / 2) * star (g (t - x / 2)) *
      (Real.fourierChar (-(ω * t)) : ℂ)) volume :=
    crossAmbiguity_integrand_integrable hf₂ hg x ω
  simpa [crossAmbiguity, add_mul, mul_add, mul_assoc] using
    (MeasureTheory.integral_add h1 h2)

theorem crossAmbiguity_add_right
    (hf : MemLp f 2 volume) (hg₁ : MemLp g₁ 2 volume) (hg₂ : MemLp g₂ 2 volume)
    (x ω : ℝ) :
    crossAmbiguity f (g₁ + g₂) x ω = crossAmbiguity f g₁ x ω + crossAmbiguity f g₂ x ω := by
  have h1 : Integrable (fun t ↦ f (t + x / 2) * star (g₁ (t - x / 2)) *
      (Real.fourierChar (-(ω * t)) : ℂ)) volume :=
    crossAmbiguity_integrand_integrable hf hg₁ x ω
  have h2 : Integrable (fun t ↦ f (t + x / 2) * star (g₂ (t - x / 2)) *
      (Real.fourierChar (-(ω * t)) : ℂ)) volume :=
    crossAmbiguity_integrand_integrable hf hg₂ x ω
  simpa [crossAmbiguity, add_mul, mul_add, mul_assoc] using
    (MeasureTheory.integral_add h1 h2)

theorem crossAmbiguity_smul_left (c : ℂ) (_hf : MemLp f 2 volume) (_hg : MemLp g 2 volume)
    (x ω : ℝ) :
    crossAmbiguity (c • f) g x ω = c * crossAmbiguity f g x ω := by
  calc
    crossAmbiguity (c • f) g x ω
        = ∫ t, ((c • f) (t + x / 2) * star (g (t - x / 2)) *
            (Real.fourierChar (-(ω * t)) : ℂ)) := by
            rfl
    _ = ∫ t, c * (f (t + x / 2) * star (g (t - x / 2)) *
            (Real.fourierChar (-(ω * t)) : ℂ)) := by
            simp [smul_eq_mul, mul_assoc]
    _ = c * crossAmbiguity f g x ω := by
            simpa [crossAmbiguity, mul_assoc] using
              (MeasureTheory.integral_const_mul c
                (fun t ↦ f (t + x / 2) * star (g (t - x / 2)) *
                  (Real.fourierChar (-(ω * t)) : ℂ)))

theorem crossAmbiguity_smul_right (c : ℂ) (_hf : MemLp f 2 volume) (_hg : MemLp g 2 volume)
    (x ω : ℝ) :
    crossAmbiguity f (c • g) x ω = star c * crossAmbiguity f g x ω := by
  calc
    crossAmbiguity f (c • g) x ω
        = ∫ t, (f (t + x / 2) * star ((c • g) (t - x / 2)) *
            (Real.fourierChar (-(ω * t)) : ℂ)) := by
            rfl
    _ = ∫ t, star c * (f (t + x / 2) * star (g (t - x / 2)) *
            (Real.fourierChar (-(ω * t)) : ℂ)) := by
            simp [smul_eq_mul, mul_assoc, mul_left_comm]
    _ = star c * crossAmbiguity f g x ω := by
            simpa [crossAmbiguity, mul_assoc] using
              (MeasureTheory.integral_const_mul (star c)
                (fun t ↦ f (t + x / 2) * star (g (t - x / 2)) *
                  (Real.fourierChar (-(ω * t)) : ℂ)))

theorem crossAmbiguity_sub_left
    (hf₁ : MemLp f₁ 2 volume) (hf₂ : MemLp f₂ 2 volume) (hg : MemLp g 2 volume)
    (x ω : ℝ) :
    crossAmbiguity (f₁ - f₂) g x ω = crossAmbiguity f₁ g x ω - crossAmbiguity f₂ g x ω := by
  calc
    crossAmbiguity (f₁ - f₂) g x ω
        = crossAmbiguity (f₁ + -f₂) g x ω := by rfl
    _ = crossAmbiguity f₁ g x ω + crossAmbiguity (-f₂) g x ω := by
          simpa using
            crossAmbiguity_add_left (f₁ := f₁) (f₂ := -f₂) (g := g) hf₁ hf₂.neg hg
              x ω
    _ = crossAmbiguity f₁ g x ω - crossAmbiguity f₂ g x ω := by
          simpa [sub_eq_add_neg] using
            congrArg (fun z : ℂ ↦ crossAmbiguity f₁ g x ω + z)
              (crossAmbiguity_smul_left (f := f₂) (g := g) (-1 : ℂ) hf₂ hg x ω)

theorem crossAmbiguity_sub_right
    (hf : MemLp f 2 volume) (hg₁ : MemLp g₁ 2 volume) (hg₂ : MemLp g₂ 2 volume)
    (x ω : ℝ) :
    crossAmbiguity f (g₁ - g₂) x ω = crossAmbiguity f g₁ x ω - crossAmbiguity f g₂ x ω := by
  calc
    crossAmbiguity f (g₁ - g₂) x ω
        = crossAmbiguity f (g₁ + -g₂) x ω := by rfl
    _ = crossAmbiguity f g₁ x ω + crossAmbiguity f (-g₂) x ω := by
          simpa using
            crossAmbiguity_add_right (f := f) (g₁ := g₁) (g₂ := -g₂) hf hg₁ hg₂.neg
              x ω
    _ = crossAmbiguity f g₁ x ω - crossAmbiguity f g₂ x ω := by
          simpa [sub_eq_add_neg] using
            congrArg (fun z : ℂ ↦ crossAmbiguity f g₁ x ω + z)
              (crossAmbiguity_smul_right (f := f) (g := g₂) (-1 : ℂ) hf hg₂ x ω)

theorem ambiguity_add (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (x ω : ℝ) :
    ambiguity (f + g) x ω =
      ambiguity f x ω + crossAmbiguity f g x ω + crossAmbiguity g f x ω + ambiguity g x ω := by
  have hfg : MemLp (f + g) 2 volume := hf.add hg
  calc
    ambiguity (f + g) x ω = crossAmbiguity (f + g) (f + g) x ω := rfl
    _ = crossAmbiguity f (f + g) x ω + crossAmbiguity g (f + g) x ω := by
      simpa using
        (crossAmbiguity_add_left (f₁ := f) (f₂ := g) (g := f + g) hf hg hfg x ω)
    _ = (crossAmbiguity f f x ω + crossAmbiguity f g x ω) +
        (crossAmbiguity g f x ω + crossAmbiguity g g x ω) := by
      rw [crossAmbiguity_add_right (f := f) (g₁ := f) (g₂ := g) hf hf hg x ω,
        crossAmbiguity_add_right (f := g) (g₁ := f) (g₂ := g) hg hf hg x ω]
    _ = ambiguity f x ω + crossAmbiguity f g x ω + crossAmbiguity g f x ω + ambiguity g x ω := by
      simp [ambiguity, add_assoc]

theorem crossAmbiguity_neg_neg (_hf : MemLp f 2 volume) (_hg : MemLp g 2 volume)
    (x ω : ℝ) :
    crossAmbiguity f g (-x) (-ω) = star (crossAmbiguity g f x ω) := by
  have hfourier : ∀ x : ℝ, star ((Real.fourierChar x : ℂ)) = Real.fourierChar (-x) := by
    intro x
    rw [Real.fourierChar_apply, Real.fourierChar_apply]
    have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := by
      simpa using (Complex.conj_ofReal (2 : ℝ))
    have h : star (Complex.exp (Complex.I * (↑x * (↑Real.pi * 2) : ℂ))) =
        Complex.exp (-(Complex.I * (↑x * (↑Real.pi * 2) : ℂ))) := by
      simpa [mul_comm, mul_left_comm, mul_assoc, h2] using
        (Complex.exp_conj (Complex.I * (↑x * (↑Real.pi * 2) : ℂ))).symm
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hchar : ∀ t : ℝ, star ((Real.fourierChar (-(ω * t)) : ℂ)) = Real.fourierChar (ω * t) := by
    intro t
    rw [hfourier (-(ω * t))]
    simp
  rw [crossAmbiguity, crossAmbiguity]
  have hconj : star (∫ t, g (t + x / 2) * star (f (t - x / 2)) *
      (Real.fourierChar (-(ω * t)) : ℂ)) =
      ∫ t, star (g (t + x / 2) * star (f (t - x / 2)) *
          (Real.fourierChar (-(ω * t)) : ℂ)) := by
    simpa using (integral_conj (f := fun t : ℝ =>
      g (t + x / 2) * star (f (t - x / 2)) * (Real.fourierChar (-(ω * t)) : ℂ))).symm
  rw [hconj]
  congr with t
  have hx : t + -x / 2 = t + -(x / 2) := by ring_nf
  have hgx : t + -(-x / 2) = t + x / 2 := by ring_nf
  simp [star_mul, mul_assoc, mul_comm, mul_left_comm, sub_eq_add_neg, hchar t, hx, hgx]

theorem ambiguity_neg_neg (hf : MemLp f 2 volume) (x ω : ℝ) :
    ambiguity f (-x) (-ω) = star (ambiguity f x ω) := by
  simpa [ambiguity, crossAmbiguity] using
    (crossAmbiguity_neg_neg (f := f) (g := f) hf hf x ω)

theorem crossAmbiguity_zero_zero (_hf : MemLp f 2 volume) (_hg : MemLp g 2 volume) :
    crossAmbiguity f g 0 0 = ∫ t, f t * star (g t) := by
  simp [crossAmbiguity]

private theorem memLp_integral_norm_sqrt (hf : MemLp f 2 volume) :
    (∫ t, ‖f t‖ ^ 2) ^ (2 : ℝ)⁻¹ = (eLpNorm f 2 volume).toReal := by
  have h := hf.eLpNorm_eq_integral_rpow_norm (μ := volume) (p := (2 : ENNReal))
    (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)
  norm_num at h
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_ofReal (by positivity)] at h'
  simp at h'
  exact h'.symm

private theorem memLp_integral_norm_sq (hf : MemLp f 2 volume) :
    ∫ t, ‖f t‖ ^ 2 = (eLpNorm f 2 volume).toReal ^ 2 := by
  have hsqrt := memLp_integral_norm_sqrt (f := f) hf
  have hnonneg : 0 ≤ ∫ t, ‖f t‖ ^ 2 := by positivity
  have hsqrt' : Real.sqrt (∫ t, ‖f t‖ ^ 2) = (eLpNorm f 2 volume).toReal := by
    simpa [Real.sqrt_eq_rpow] using hsqrt
  have hsq := congrArg (fun x : ℝ => x ^ 2) hsqrt'
  simpa [Real.sq_sqrt hnonneg] using hsq

theorem ambiguity_zero_zero (hf : MemLp f 2 volume) :
    ambiguity f 0 0 = (((eLpNorm f 2 volume).toReal ^ 2 : ℝ) : ℂ) := by
  calc
    ambiguity f 0 0 = crossAmbiguity f f 0 0 := by
      simp [ambiguity]
    _ = ∫ t, f t * star (f t) := by
      simpa using (crossAmbiguity_zero_zero (f := f) (g := f) hf hf)
    _ = ∫ t, (((‖f t‖ ^ 2 : ℝ) : ℂ)) := by
      congr with t
      simp [Complex.mul_conj']
    _ = (((eLpNorm f 2 volume).toReal ^ 2 : ℝ) : ℂ) := by
      have hco := (integral_ofReal (μ := volume) (𝕜 := ℂ) (f := fun t : ℝ => ‖f t‖ ^ 2))
      convert hco using 1
      simp [memLp_integral_norm_sq hf]

theorem crossAmbiguity_le (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (x ω : ℝ) :
    ‖crossAmbiguity f g x ω‖ ≤ (eLpNorm f 2 volume).toReal * (eLpNorm g 2 volume).toReal := by
  rw [crossAmbiguity_eq_integral (f := f) (g := g) hf hg x ω, norm_mul, norm_fourierChar, one_mul]
  have h₂ : ‖∫ t, f t * star ((modulate ω (translate x g)) t)‖ ≤
      ∫ t, ‖f t‖ * ‖(modulate ω (translate x g)) t‖ := by
    simpa [norm_mul, norm_star, mul_comm, mul_left_comm, mul_assoc] using
      (norm_integral_le_integral_norm (μ := volume)
        (f := fun t ↦ f t * star ((modulate ω (translate x g)) t)))
  have h₃ : ∫ t, ‖f t‖ * ‖(modulate ω (translate x g)) t‖ ≤
      ((eLpNorm f 2 volume).toReal) * ((eLpNorm g 2 volume).toReal) := by
    have hpq : Real.HolderConjugate 2 2 := Real.HolderConjugate.two_two
    have hf' : MemLp (fun t ↦ ‖f t‖) (ENNReal.ofReal (2 : ℝ)) volume := by
      simpa using hf.norm
    have hg' : MemLp (fun t ↦ ‖(modulate ω (translate x g)) t‖)
        (ENNReal.ofReal (2 : ℝ)) volume := by
      simpa [translate, sub_eq_add_neg] using
        (modulate_translate_memLp g ω x hg).norm
    have hf_nonneg : 0 ≤ᵐ[volume] fun t ↦ ‖f t‖ := by
      filter_upwards with t
      positivity
    have hg_nonneg : 0 ≤ᵐ[volume] fun t ↦ ‖(modulate ω (translate x g)) t‖ := by
      filter_upwards with t
      positivity
    have hholder := @MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg ℝ _ volume 2 2 hpq
      (fun t ↦ ‖f t‖) (fun t ↦ ‖(modulate ω (translate x g)) t‖) hf_nonneg hg_nonneg
      hf' hg'
    have hf_sqrt : (∫ t, ‖f t‖ * ‖f t‖ : ℝ) ^ (2 : ℝ)⁻¹ = (eLpNorm f 2 volume).toReal := by
      simpa [sq] using memLp_integral_norm_sqrt hf
    have hg_sqrt : (∫ t, ‖(modulate ω (translate x g)) t‖ *
        ‖(modulate ω (translate x g)) t‖ : ℝ) ^ (2 : ℝ)⁻¹ = (eLpNorm g 2 volume).toReal := by
      have hsqrt := memLp_integral_norm_sqrt (modulate_translate_memLp g ω x hg)
      have htrans : (eLpNorm (modulate ω (translate x g)) 2 volume).toReal =
          (eLpNorm g 2 volume).toReal := by
        rw [@AmbiguityZeros.ToMathlib.modulate_eLpNorm (p := 2) (f := translate x g) ω
            (translate_aestronglyMeasurable x hg.aestronglyMeasurable),
          @AmbiguityZeros.ToMathlib.translate_eLpNorm (p := 2) (f := g) x hg.aestronglyMeasurable]
      simpa [translate, sub_eq_add_neg, sq] using hsqrt.trans htrans
    simpa [sq, hf_sqrt, hg_sqrt, mul_comm, mul_left_comm, mul_assoc] using hholder
  exact le_trans h₂ h₃

theorem ambiguity_le (hf : MemLp f 2 volume) (x ω : ℝ) :
    ‖ambiguity f x ω‖ ≤ (eLpNorm f 2 volume).toReal ^ 2 := by
  simpa [ambiguity, sq] using
    (crossAmbiguity_le (f := f) (g := f) hf hf x ω)

theorem ambiguity_sub_le (hf : MemLp f 2 volume) (hu : MemLp u 2 volume) (x ω : ℝ) :
    ‖ambiguity (f + u) x ω - ambiguity f x ω‖ ≤
      2 * (eLpNorm f 2 volume).toReal * (eLpNorm u 2 volume).toReal +
        (eLpNorm u 2 volume).toReal ^ 2 := by
  have hdecomp :
      ambiguity (f + u) x ω - ambiguity f x ω =
        crossAmbiguity f u x ω + crossAmbiguity u f x ω + ambiguity u x ω := by
    rw [ambiguity_add hf hu x ω]
    ring_nf
  rw [hdecomp]
  have htri :
      ‖crossAmbiguity f u x ω + crossAmbiguity u f x ω + ambiguity u x ω‖ ≤
        ‖crossAmbiguity f u x ω‖ + ‖crossAmbiguity u f x ω‖ + ‖ambiguity u x ω‖ := by
    calc
      ‖crossAmbiguity f u x ω + crossAmbiguity u f x ω + ambiguity u x ω‖
          ≤ ‖crossAmbiguity f u x ω + crossAmbiguity u f x ω‖ + ‖ambiguity u x ω‖ := by
            simpa [add_assoc] using
              norm_add_le (crossAmbiguity f u x ω + crossAmbiguity u f x ω) (ambiguity u x ω)
      _ ≤ (‖crossAmbiguity f u x ω‖ + ‖crossAmbiguity u f x ω‖) + ‖ambiguity u x ω‖ := by
            gcongr
            exact norm_add_le (crossAmbiguity f u x ω) (crossAmbiguity u f x ω)
      _ = ‖crossAmbiguity f u x ω‖ + ‖crossAmbiguity u f x ω‖ + ‖ambiguity u x ω‖ := by
            ring_nf
  have hfu := crossAmbiguity_le (f := f) (g := u) hf hu x ω
  have huf := crossAmbiguity_le (f := u) (g := f) hu hf x ω
  have huu := ambiguity_le (f := u) hu x ω
  refine htri.trans ?_
  nlinarith [hfu, huf, huu]

theorem crossAmbiguity_continuous (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Continuous (fun p : ℝ × ℝ ↦ crossAmbiguity f g p.1 p.2) := by
  let F : MeasureTheory.Lp (α := ℝ) ℂ 2 volume := hf.toLp f
  let G : MeasureTheory.Lp (α := ℝ) ℂ 2 volume := hg.toLp g
  let τ : ℝ → C(ℝ, ℝ) := fun x ↦ ⟨fun t ↦ t - x, by continuity⟩
  have hτ : Continuous τ := by
    refine ContinuousMap.continuous_of_continuous_uncurry τ ?_
    exact (by
      continuity : Continuous fun p : ℝ × ℝ ↦ p.2 - p.1)
  have htransG : Continuous fun x : ℝ ↦ translateLp x G := by
    have hmp : ∀ x : ℝ, MeasurePreserving (τ x) volume volume := by
      intro x
      simpa [τ] using (MeasureTheory.measurePreserving_sub_right volume x)
    exact
      (Continuous.compMeasurePreservingLp (μ := volume) (ν := volume) (E := ℂ)
        (p := (2 : ENNReal)) (hf := continuous_const) (hg := hτ) (hgm := hmp)
        (by norm_num : (2 : ENNReal) ≠ ⊤))
  have hmodBoth :
      Continuous (fun p : ℝ × MeasureTheory.Lp (α := ℝ) ℂ 2 volume ↦
        modulateLp p.1 p.2) := by
    have htransBoth : Continuous
        (fun p : ℝ × MeasureTheory.Lp (α := ℝ) ℂ 2 volume ↦
          translateLp p.1 (FourierTransform.fourier p.2)) := by
      exact
        (Continuous.compMeasurePreservingLp (μ := volume) (ν := volume) (E := ℂ)
          (p := (2 : ENNReal))
          (hf := FourierTransform.continuous_fourier.comp continuous_snd)
          (hg := hτ.comp continuous_fst)
          (hgm := fun p ↦ by
            simpa [τ] using (MeasureTheory.measurePreserving_sub_right volume p.1))
          (by norm_num : (2 : ENNReal) ≠ ⊤))
    have hmodEq :
        ∀ p : ℝ × MeasureTheory.Lp (α := ℝ) ℂ 2 volume,
          modulateLp p.1 p.2 =
            FourierTransform.fourierInv (translateLp p.1 (FourierTransform.fourier p.2)) := by
      intro p
      have hFourier :
          FourierTransform.fourier (modulateLp p.1 p.2) =
            translateLp p.1 (FourierTransform.fourier p.2) := by
        simpa using
          (l2Fourier_modulate_lp (f := (p.2 : ℝ → ℂ)) (ω := p.1)
            (hf := MeasureTheory.Lp.memLp p.2))
      calc
        modulateLp p.1 p.2 =
            FourierTransform.fourierInv (FourierTransform.fourier (modulateLp p.1 p.2)) := by
              symm
              exact
                (FourierPair.fourierInv_fourier_eq
                  (E := MeasureTheory.Lp (α := ℝ) ℂ 2 volume)
                  (F := MeasureTheory.Lp (α := ℝ) ℂ 2 volume)
                  (f := modulateLp p.1 p.2))
        _ = FourierTransform.fourierInv (translateLp p.1 (FourierTransform.fourier p.2)) := by
              simp [hFourier]
    simpa [hmodEq, Function.comp_def] using
      (FourierTransform.continuous_fourierInv.comp htransBoth)
  have hphase : Continuous (fun p : ℝ × ℝ ↦ (Real.fourierChar (p.2 * p.1 / 2) : ℂ)) := by
    exact (continuous_subtype_val.comp
      (by
        exact
          (Real.continuous_fourierChar.comp
            (by fun_prop : Continuous fun p : ℝ × ℝ ↦ p.2 * p.1 / 2))))
  have hvec : Continuous
      (fun p : ℝ × ℝ ↦ modulateLp p.2 (translateLp p.1 G)) := by
    exact hmodBoth.comp (continuous_snd.prodMk (htransG.comp continuous_fst))
  have hinner : Continuous
      (fun p : ℝ × ℝ ↦ inner ℂ (modulateLp p.2 (translateLp p.1 G)) F) := by
    exact
      (continuous_inner.comp (hvec.prodMk continuous_const))
  have hEq :
      (fun p : ℝ × ℝ ↦ crossAmbiguity f g p.1 p.2) =
        fun p : ℝ × ℝ ↦
          (Real.fourierChar (p.2 * p.1 / 2) : ℂ) *
            inner ℂ (modulateLp p.2 (translateLp p.1 G)) F := by
    funext p
    simpa [F, G, mul_comm] using (crossAmbiguity_eq_inner' (f := f) (g := g) hf hg p.1 p.2)
  rw [hEq]
  exact hphase.mul hinner

theorem ambiguity_continuous (hf : MemLp f 2 volume) :
    Continuous (fun p : ℝ × ℝ ↦ ambiguity f p.1 p.2) := by
  simpa [ambiguity] using crossAmbiguity_continuous (f := f) (g := f) hf hf

end

end AmbiguityZeros.ToMathlib
