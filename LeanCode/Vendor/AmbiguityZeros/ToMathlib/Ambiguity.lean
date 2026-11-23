import AmbiguityZeros.ToMathlib.OscillatoryIntegral
import AmbiguityZeros.ToMathlib.TranslationModulation

namespace AmbiguityZeros.ToMathlib

noncomputable section

open MeasureTheory

variable {f g f₁ f₂ u v : ℝ → ℂ}

def crossAmbiguity (f g : ℝ → ℂ) (x ω : ℝ) : ℂ :=
  ∫ t, f (t + x / 2) * star (g (t - x / 2)) * (Real.fourierChar (-(ω * t)) : ℂ)

def ambiguity (f : ℝ → ℂ) : ℝ → ℝ → ℂ :=
  crossAmbiguity f f

theorem ambiguity_eq_crossAmbiguity (f : ℝ → ℂ) :
    ambiguity f = crossAmbiguity f f := rfl

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

private theorem crossAmbiguity_integrand_aestronglyMeasurable
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    (x ω : ℝ) :
    AEStronglyMeasurable
      (fun t ↦ f (t + x / 2) * star (g (t - x / 2)) * (Real.fourierChar (-(ω * t)) : ℂ))
      volume := by
  have htrans : translate (-x / 2) f = fun t ↦ f (t + x / 2) := by
    funext t
    simp [translate]
    congr 1
    ring_nf
  have hleft : AEStronglyMeasurable (fun t ↦ f (t + x / 2)) volume := by
    simpa [htrans] using (translate_aestronglyMeasurable (-x / 2) hf)
  have hright : AEStronglyMeasurable (fun t ↦ star (g (t - x / 2))) volume := by
    simpa [translate, sub_eq_add_neg] using
      (conj_aestronglyMeasurable (translate_aestronglyMeasurable (x / 2) hg))
  have hchar : AEStronglyMeasurable (fun t ↦ (Real.fourierChar (-(ω * t)) : ℂ)) volume := by
    exact (by fun_prop : Measurable fun t ↦ (Real.fourierChar (-(ω * t)) : ℂ)).aestronglyMeasurable
  have htmp : AEStronglyMeasurable
      (fun t ↦ star (g (t - x / 2)) * (Real.fourierChar (-(ω * t)) : ℂ)) volume :=
    hright.mul hchar
  simpa [mul_assoc] using hleft.mul htmp

theorem crossAmbiguity_translate_translate
    (_hf : MemLp f 2 volume) (_hg : MemLp g 2 volume) (a b x ω : ℝ) :
    crossAmbiguity (translate a f) (translate b g) x ω =
      (Real.fourierChar (-(ω * (a + b) / 2)) : ℂ) * crossAmbiguity f g (x - (a - b)) ω := by
  have hshift :
      ∫ t, f (t + x / 2 - a) * star (g (t - x / 2 - b)) * (Real.fourierChar (-(ω * t)) : ℂ) =
        ∫ t, f (t + (x - (a - b)) / 2) * star (g (t - (x - (a - b)) / 2)) *
          (Real.fourierChar (-(ω * (t + (a + b) / 2))) : ℂ) := by
    have h := MeasureTheory.integral_add_right_eq_self
      (μ := (volume : Measure ℝ))
      (f := fun t : ℝ ↦
        f (t + x / 2 - a) * star (g (t - x / 2 - b)) * (Real.fourierChar (-(ω * t)) : ℂ))
      ((a + b) / 2)
    convert h.symm using 1
    · congr with t
      ring_nf
  have hphase :
      ∀ t : ℝ,
        (Real.fourierChar (-(ω * (t + (a + b) / 2))) : ℂ) =
          (Real.fourierChar (-(ω * (a + b) / 2)) : ℂ) * (Real.fourierChar (-(ω * t)) : ℂ) := by
    intro t
    have harg : -(ω * (t + (a + b) / 2)) = -(ω * t) + -(ω * (a + b) / 2) := by
      ring_nf
    have hmul := Real.fourierChar.map_add_eq_mul' (-(ω * t)) (-(ω * (a + b) / 2))
    simpa [harg, mul_comm, mul_left_comm, mul_assoc] using
      congrArg (fun z : Circle ↦ (z : ℂ)) hmul
  have hfactor :
      ∫ t, f (t + (x - (a - b)) / 2) * star (g (t - (x - (a - b)) / 2)) *
          (Real.fourierChar (-(ω * (t + (a + b) / 2))) : ℂ) =
        (Real.fourierChar (-(ω * (a + b) / 2)) : ℂ) *
          ∫ t, f (t + (x - (a - b)) / 2) * star (g (t - (x - (a - b)) / 2)) *
            (Real.fourierChar (-(ω * t)) : ℂ) := by
    calc
      ∫ t, f (t + (x - (a - b)) / 2) * star (g (t - (x - (a - b)) / 2)) *
          (Real.fourierChar (-(ω * (t + (a + b) / 2))) : ℂ)
          = ∫ t, (Real.fourierChar (-(ω * (a + b) / 2)) : ℂ) *
              (f (t + (x - (a - b)) / 2) * star (g (t - (x - (a - b)) / 2)) *
                (Real.fourierChar (-(ω * t)) : ℂ)) := by
              congr with t
              rw [hphase]
              ring_nf
      _ = (Real.fourierChar (-(ω * (a + b) / 2)) : ℂ) *
            ∫ t, f (t + (x - (a - b)) / 2) * star (g (t - (x - (a - b)) / 2)) *
              (Real.fourierChar (-(ω * t)) : ℂ) := by
              simpa [mul_assoc] using
                (MeasureTheory.integral_const_mul
                  (r := (Real.fourierChar (-(ω * (a + b) / 2)) : ℂ))
                  (f := fun t : ℝ ↦
                    f (t + (x - (a - b)) / 2) * star (g (t - (x - (a - b)) / 2)) *
                      (Real.fourierChar (-(ω * t)) : ℂ)))
  calc
    crossAmbiguity (translate a f) (translate b g) x ω =
        ∫ t, f (t + x / 2 - a) * star (g (t - x / 2 - b)) *
          (Real.fourierChar (-(ω * t)) : ℂ) := by
            simp [crossAmbiguity, translate, sub_eq_add_neg, mul_assoc]
    _ = ∫ t, f (t + (x - (a - b)) / 2) * star (g (t - (x - (a - b)) / 2)) *
          (Real.fourierChar (-(ω * (t + (a + b) / 2))) : ℂ) := hshift
    _ = (Real.fourierChar (-(ω * (a + b) / 2)) : ℂ) *
          ∫ t, f (t + (x - (a - b)) / 2) * star (g (t - (x - (a - b)) / 2)) *
            (Real.fourierChar (-(ω * t)) : ℂ) := hfactor
    _ = (Real.fourierChar (-(ω * (a + b) / 2)) : ℂ) * crossAmbiguity f g (x - (a - b)) ω := by
          simp [crossAmbiguity]

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

theorem crossAmbiguity_congr_ae
    (hf₁ : MemLp f₁ 2 volume) (hf₂ : MemLp f₂ 2 volume)
    (hg₁ : MemLp g₁ 2 volume) (hg₂ : MemLp g₂ 2 volume)
    (hff : f₁ =ᵐ[volume] f₂) (hgg : g₁ =ᵐ[volume] g₂) (x ω : ℝ) :
    crossAmbiguity f₁ g₁ x ω = crossAmbiguity f₂ g₂ x ω := by
  have hf_eq : hf₁.toLp f₁ = hf₂.toLp f₂ :=
    MemLp.toLp_congr hf₁ hf₂ hff
  have hg_eq : hg₁.toLp g₁ = hg₂.toLp g₂ :=
    MemLp.toLp_congr hg₁ hg₂ hgg
  rw [crossAmbiguity_eq_inner' (f := f₁) (g := g₁) hf₁ hg₁ x ω,
    crossAmbiguity_eq_inner' (f := f₂) (g := g₂) hf₂ hg₂ x ω]
  simp [hf_eq, hg_eq]

theorem ambiguity_congr_ae
    (hf₁ : MemLp f₁ 2 volume) (hf₂ : MemLp f₂ 2 volume)
    (hff : f₁ =ᵐ[volume] f₂) (x ω : ℝ) :
    ambiguity f₁ x ω = ambiguity f₂ x ω := by
  exact crossAmbiguity_congr_ae hf₁ hf₂ hf₁ hf₂ hff hff x ω

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

theorem crossAmbiguity_zero_left (_hg : MemLp g 2 volume) (x ω : ℝ) :
    crossAmbiguity 0 g x ω = 0 := by
  simp [crossAmbiguity]

theorem crossAmbiguity_zero_right (_hf : MemLp f 2 volume) (x ω : ℝ) :
    crossAmbiguity f 0 x ω = 0 := by
  simp [crossAmbiguity]

theorem crossAmbiguity_zero_zero (_hf : MemLp f 2 volume) (_hg : MemLp g 2 volume) :
    crossAmbiguity f g 0 0 = ∫ t, f t * star (g t) := by
  simp [crossAmbiguity]

theorem ambiguity_zero (x ω : ℝ) :
    ambiguity 0 x ω = 0 := by
  simp [ambiguity, crossAmbiguity]

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
            (translate_aestronglyMeasurable x hg.1),
          @AmbiguityZeros.ToMathlib.translate_eLpNorm (p := 2) (f := g) x hg.1]
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

theorem crossAmbiguity_tendsto_right_of_eLpNorm_sub_tendsto_zero
    {ι : Type*} {l : Filter ι} {gₙ : ι → ℝ → ℂ} {f g : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hgₙ : ∀ n, MemLp (gₙ n) 2 volume)
    (hconv : Filter.Tendsto (fun n => eLpNorm (gₙ n - g) 2 volume) l (nhds 0))
    (x ω : ℝ) :
    Filter.Tendsto (fun n => crossAmbiguity f (gₙ n) x ω) l
      (nhds (crossAmbiguity f g x ω)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hconvReal :
      Filter.Tendsto (fun n => (eLpNorm (gₙ n - g) 2 volume).toReal) l
        (nhds (0 : ℝ)) := by
    simpa using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv
  have hbound :
      Filter.Tendsto
        (fun n => (eLpNorm f 2 volume).toReal * (eLpNorm (gₙ n - g) 2 volume).toReal)
        l (nhds 0) := by
    simpa using tendsto_const_nhds.mul hconvReal
  refine squeeze_zero (fun n => norm_nonneg _) ?_ hbound
  intro n
  have hgn : MemLp (gₙ n) 2 volume := hgₙ n
  have hsub := crossAmbiguity_sub_right (f := f) (g₁ := gₙ n) (g₂ := g) hf hgn hg x ω
  rw [← hsub]
  exact crossAmbiguity_le hf (hgn.sub hg) x ω

theorem crossAmbiguity_tendsto_left_of_eLpNorm_sub_tendsto_zero
    {ι : Type*} {l : Filter ι} {fₙ : ι → ℝ → ℂ} {f g : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hfₙ : ∀ n, MemLp (fₙ n) 2 volume)
    (hconv : Filter.Tendsto (fun n => eLpNorm (fₙ n - f) 2 volume) l (nhds 0))
    (x ω : ℝ) :
    Filter.Tendsto (fun n => crossAmbiguity (fₙ n) g x ω) l
      (nhds (crossAmbiguity f g x ω)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hconvReal :
      Filter.Tendsto (fun n => (eLpNorm (fₙ n - f) 2 volume).toReal) l
        (nhds (0 : ℝ)) := by
    simpa using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv
  have hbound :
      Filter.Tendsto
        (fun n => (eLpNorm (fₙ n - f) 2 volume).toReal * (eLpNorm g 2 volume).toReal)
        l (nhds 0) := by
    simpa using hconvReal.mul tendsto_const_nhds
  refine squeeze_zero (fun n => norm_nonneg _) ?_ hbound
  intro n
  have hfn : MemLp (fₙ n) 2 volume := hfₙ n
  have hsub := crossAmbiguity_sub_left (f₁ := fₙ n) (f₂ := f) (g := g) hfn hf hg x ω
  rw [← hsub]
  exact crossAmbiguity_le (hfn.sub hf) hg x ω

theorem ambiguity_tendsto_of_eLpNorm_sub_tendsto_zero
    {ι : Type*} {l : Filter ι} {fₙ : ι → ℝ → ℂ} {f : ℝ → ℂ}
    (hf : MemLp f 2 volume)
    (hfₙ : ∀ n, MemLp (fₙ n) 2 volume)
    (hconv : Filter.Tendsto (fun n => eLpNorm (fₙ n - f) 2 volume) l (nhds 0))
    (x ω : ℝ) :
    Filter.Tendsto (fun n => ambiguity (fₙ n) x ω) l (nhds (ambiguity f x ω)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hconvReal :
      Filter.Tendsto (fun n => (eLpNorm (fₙ n - f) 2 volume).toReal) l
        (nhds (0 : ℝ)) := by
    simpa using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv
  have hbound :
      Filter.Tendsto
        (fun n =>
          2 * (eLpNorm f 2 volume).toReal * (eLpNorm (fₙ n - f) 2 volume).toReal +
            (eLpNorm (fₙ n - f) 2 volume).toReal ^ 2)
        l (nhds 0) := by
    have hlinear :
        Filter.Tendsto
          (fun n =>
            (2 * (eLpNorm f 2 volume).toReal) *
              (eLpNorm (fₙ n - f) 2 volume).toReal)
          l (nhds 0) := by
      simpa using tendsto_const_nhds.mul hconvReal
    have hsquare :
        Filter.Tendsto (fun n => (eLpNorm (fₙ n - f) 2 volume).toReal ^ 2) l
          (nhds 0) := by
      simpa using hconvReal.pow 2
    simpa [mul_assoc] using hlinear.add hsquare
  refine squeeze_zero (fun n => norm_nonneg _) ?_ hbound
  intro n
  have hfn : MemLp (fₙ n) 2 volume := hfₙ n
  have herr : MemLp (fₙ n - f) 2 volume := hfn.sub hf
  have hdecomp : f + (fₙ n - f) = fₙ n := by
    funext t
    simp
  simpa [hdecomp] using ambiguity_sub_le (f := f) (u := fₙ n - f) hf herr x ω

theorem ambiguity_fourier (hf : MemLp f 2 volume) (x ω : ℝ) :
    ambiguity (l2Fourier f hf) x ω = ambiguity f (-ω) x := by
  have hfF : MemLp (l2Fourier f hf) 2 volume := l2Fourier_memLp f hf
  have himage :
      FourierTransform.fourier (translateLp (-ω) (modulateLp x (hf.toLp f))) =
        modulateLp ω (translateLp x (FourierTransform.fourier (hf.toLp f))) := by
    calc
      FourierTransform.fourier (translateLp (-ω) (modulateLp x (hf.toLp f)))
          = FourierTransform.fourier
              (translateLp (-ω) ((modulate_memLp x hf).toLp (modulate x f))) := by
                congr 1
                simpa using (modulateLp_toLp x (f := f) (hf := hf))
      _ = modulateLp ω (FourierTransform.fourier ((modulate_memLp x hf).toLp (modulate x f))) := by
            simpa using
              (l2Fourier_translate_lp (f := modulate x f) (x := -ω) (hf := modulate_memLp x hf))
      _ = modulateLp ω (translateLp x (FourierTransform.fourier (hf.toLp f))) := by
            congr 1
            simpa [modulateLp_toLp x (f := f) (hf := hf)] using
              (l2Fourier_modulate_lp (f := f) (ω := x) hf)
  have hslot :
      translateLp (-ω) (modulateLp x (hf.toLp f)) =
        (translate_memLp (-ω) (modulate_memLp x hf)).toLp (translate (-ω) (modulate x f)) := by
    rw [modulateLp_toLp x (f := f) (hf := hf)]
    simpa using
      (translateLp_toLp (-ω) (f := modulate x f) (hf := modulate_memLp x hf))
  have hcomm_inner :
      inner ℂ ((translate_memLp (-ω) (modulate_memLp x hf)).toLp (translate (-ω) (modulate x f)))
        (hf.toLp f) =
        (Real.fourierChar (-(ω * x)) : ℂ) *
          inner ℂ
            ((modulate_memLp x (translate_memLp (-ω) hf)).toLp (modulate x (translate (-ω) f)))
            (hf.toLp f) := by
    have hstar : ∀ y : ℝ, star ((Real.fourierChar y : ℂ)) = Real.fourierChar (-y) := by
      intro y
      rw [Real.fourierChar_apply, Real.fourierChar_apply]
      have h2 : (starRingEnd ℂ) (2 : ℂ) = (2 : ℂ) := by
        simpa using map_natCast (starRingEnd ℂ) 2
      have h := (Complex.exp_conj (2 * Real.pi * y * Complex.I)).symm
      simpa [h2, map_mul, Complex.conj_I, mul_comm, mul_left_comm, mul_assoc] using h
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    calc
      ∫ t,
          inner ℂ
            (((translate_memLp (-ω) (modulate_memLp x hf)).toLp (translate (-ω) (modulate x f))) t)
            ((hf.toLp f) t)
          =
            ∫ t,
              (Real.fourierChar (-(ω * x)) : ℂ) *
                inner ℂ
                  (((modulate_memLp x (translate_memLp (-ω) hf)).toLp
                    (modulate x (translate (-ω) f))) t)
                  ((hf.toLp f) t) := by
                    refine integral_congr_ae ?_
                    filter_upwards
                      [hf.coeFn_toLp,
                        (translate_memLp (-ω) (modulate_memLp x hf)).coeFn_toLp,
                        (modulate_memLp x (translate_memLp (-ω) hf)).coeFn_toLp] with
                      t hft hleft hright
                    have hcomm := translate_modulate_comm_apply (-ω) x f t
                    have hphase :
                        (Real.fourierChar (-(x * -ω)) : ℂ) =
                          Real.fourierChar (ω * x) := by
                      congr 1
                      ring_nf
                    simp [hft, hleft, hright, hcomm, mul_assoc, mul_comm]
      _ =
          (Real.fourierChar (-(ω * x)) : ℂ) *
            ∫ t,
              inner ℂ
                (((modulate_memLp x (translate_memLp (-ω) hf)).toLp
                  (modulate x (translate (-ω) f))) t)
                ((hf.toLp f) t) := by
                  simpa using
                    (MeasureTheory.integral_const_mul
                      (r := (Real.fourierChar (-(ω * x)) : ℂ))
                      (f := fun t : ℝ ↦
                        inner ℂ
                          (((modulate_memLp x (translate_memLp (-ω) hf)).toLp
                            (modulate x (translate (-ω) f))) t)
                          ((hf.toLp f) t)))
  have hphase :
      (Real.fourierChar (ω * x / 2) : ℂ) * (Real.fourierChar (-(ω * x)) : ℂ) =
        Real.fourierChar (-(ω * x / 2)) := by
    have hmul := congrArg (fun z : Circle ↦ (z : ℂ))
      (Real.fourierChar.map_add_eq_mul (-(ω * x)) (ω * x / 2))
    have harg : -(ω * x) + ω * x / 2 = -(ω * x / 2) := by ring_nf
    rw [harg] at hmul
    simpa [mul_comm] using hmul.symm
  have hfinal :
      ((modulate_memLp x (translate_memLp (-ω) hf)).toLp (modulate x (translate (-ω) f))) =
        modulateLp x (translateLp (-ω) (hf.toLp f)) := by
    rw [translateLp_toLp (-ω) hf]
    symm
    simpa using
      (modulateLp_toLp x (f := translate (-ω) f) (hf := translate_memLp (-ω) hf))
  calc
    ambiguity (l2Fourier f hf) x ω
        = (Real.fourierChar (ω * x / 2) : ℂ) *
            inner ℂ (modulateLp ω (translateLp x (FourierTransform.fourier (hf.toLp f))))
              (FourierTransform.fourier (hf.toLp f)) := by
                simpa [ambiguity, l2Fourier] using
                  (crossAmbiguity_eq_inner' (f := l2Fourier f hf) (g := l2Fourier f hf) hfF hfF x ω)
    _ = (Real.fourierChar (ω * x / 2) : ℂ) *
          inner ℂ (FourierTransform.fourier (translateLp (-ω) (modulateLp x (hf.toLp f))))
            (FourierTransform.fourier (hf.toLp f)) := by
              congr 1
              rw [himage]
    _ = (Real.fourierChar (ω * x / 2) : ℂ) *
          inner ℂ (translateLp (-ω) (modulateLp x (hf.toLp f))) (hf.toLp f) := by
            rw [MeasureTheory.Lp.inner_fourier_eq]
    _ = (Real.fourierChar (ω * x / 2) : ℂ) *
          inner ℂ
            ((translate_memLp (-ω) (modulate_memLp x hf)).toLp
              (translate (-ω) (modulate x f)))
            (hf.toLp f) := by
              rw [hslot]
    _ = (Real.fourierChar (ω * x / 2) : ℂ) *
          ((Real.fourierChar (-(ω * x)) : ℂ) *
            inner ℂ
              ((modulate_memLp x (translate_memLp (-ω) hf)).toLp (modulate x (translate (-ω) f)))
              (hf.toLp f)) := by
                rw [hcomm_inner]
    _ = (Real.fourierChar (-(ω * x / 2)) : ℂ) *
          inner ℂ
            ((modulate_memLp x (translate_memLp (-ω) hf)).toLp (modulate x (translate (-ω) f)))
            (hf.toLp f) := by
              rw [← mul_assoc, hphase]
    _ = ambiguity f (-ω) x := by
          rw [hfinal]
          have harg : -(x * ω) / 2 = -(ω * x / 2) := by ring_nf
          simpa [ambiguity, harg] using
            (crossAmbiguity_eq_inner' (f := f) (g := f) hf hf (-ω) x).symm

theorem crossAmbiguity_continuous (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Continuous (fun p : ℝ × ℝ ↦ crossAmbiguity f g p.1 p.2) := by
  let F : MeasureTheory.Lp (α := ℝ) ℂ 2 volume := hf.toLp f
  let G : MeasureTheory.Lp (α := ℝ) ℂ 2 volume := hg.toLp g
  let τ : ℝ → C(ℝ, ℝ) := fun x ↦ ⟨fun t ↦ t - x, by continuity⟩
  have hτ : Continuous τ := by
    refine ContinuousMap.continuous_of_continuous_uncurry τ ?_
    simpa [τ, Function.uncurry] using (by
      continuity : Continuous fun p : ℝ × ℝ ↦ p.2 - p.1)
  have htransG : Continuous fun x : ℝ ↦ translateLp x G := by
    have hmp : ∀ x : ℝ, MeasurePreserving (τ x) volume volume := by
      intro x
      simpa [τ] using (MeasureTheory.measurePreserving_sub_right volume x)
    simpa [translateLp, τ] using
      (Continuous.compMeasurePreservingLp (μ := volume) (ν := volume) (E := ℂ)
        (p := (2 : ENNReal)) (hf := continuous_const) (hg := hτ) (hgm := hmp)
        (by norm_num : (2 : ENNReal) ≠ ⊤))
  have hmodBoth :
      Continuous (fun p : ℝ × MeasureTheory.Lp (α := ℝ) ℂ 2 volume ↦
        modulateLp p.1 p.2) := by
    have htransBoth : Continuous
        (fun p : ℝ × MeasureTheory.Lp (α := ℝ) ℂ 2 volume ↦
          translateLp p.1 (FourierTransform.fourier p.2)) := by
      simpa [translateLp, τ] using
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
    simpa [hmodEq] using (FourierTransform.continuous_fourierInv.comp htransBoth)
  have hphase : Continuous (fun p : ℝ × ℝ ↦ (Real.fourierChar (p.2 * p.1 / 2) : ℂ)) := by
    exact (continuous_subtype_val.comp
      (by
        simpa [mul_comm] using
          (Real.continuous_fourierChar.comp
            (by fun_prop : Continuous fun p : ℝ × ℝ ↦ p.2 * p.1 / 2))))
  have hvec : Continuous
      (fun p : ℝ × ℝ ↦ modulateLp p.2 (translateLp p.1 G)) := by
    simpa [G] using hmodBoth.comp (continuous_snd.prodMk (htransG.comp continuous_fst))
  have hinner : Continuous
      (fun p : ℝ × ℝ ↦ inner ℂ (modulateLp p.2 (translateLp p.1 G)) F) := by
    simpa [F, G] using
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

theorem crossAmbiguity_aestronglyMeasurable (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    AEStronglyMeasurable (fun p : ℝ × ℝ ↦ crossAmbiguity f g p.1 p.2) (volume.prod volume) := by
  exact (crossAmbiguity_continuous (f := f) (g := g) hf hg).aestronglyMeasurable

theorem crossAmbiguity_measurable (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Measurable (fun p : ℝ × ℝ ↦ crossAmbiguity f g p.1 p.2) := by
  exact (crossAmbiguity_continuous (f := f) (g := g) hf hg).measurable

theorem ambiguity_continuous (hf : MemLp f 2 volume) :
    Continuous (fun p : ℝ × ℝ ↦ ambiguity f p.1 p.2) := by
  simpa [ambiguity] using crossAmbiguity_continuous (f := f) (g := f) hf hf

theorem ambiguity_aestronglyMeasurable (hf : MemLp f 2 volume) :
    AEStronglyMeasurable (fun p : ℝ × ℝ ↦ ambiguity f p.1 p.2) (volume.prod volume) := by
  exact (ambiguity_continuous (f := f) hf).aestronglyMeasurable

theorem ambiguity_measurable (hf : MemLp f 2 volume) :
    Measurable (fun p : ℝ × ℝ ↦ ambiguity f p.1 p.2) := by
  exact (ambiguity_continuous (f := f) hf).measurable

theorem crossAmbiguity_indicator_indicator (a b : ℝ) (L : ℝ) (_hL : 0 < L) (x ω : ℝ)
    (_hx : |x - (a - b)| < L) :
    crossAmbiguity (Set.indicator (Set.Icc a (a + L)) fun _ ↦ (1 : ℂ))
      (Set.indicator (Set.Icc b (b + L)) fun _ ↦ (1 : ℂ)) x ω =
        (Real.fourierChar (-(ω * (a + b) / 2)) : ℂ) *
          crossAmbiguity (Set.indicator (Set.Icc 0 L) fun _ ↦ (1 : ℂ))
            (Set.indicator (Set.Icc 0 L) fun _ ↦ (1 : ℂ)) (x - (a - b)) ω := by
  let h0 : ℝ → ℂ := Set.indicator (Set.Icc 0 L) fun _ ↦ (1 : ℂ)
  have hmem0 : MemLp h0 2 volume := by
    have hsm : AEStronglyMeasurable h0 volume := by
      exact (Measurable.indicator (by fun_prop) measurableSet_Icc).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq_norm hsm]
    have hs : volume (Set.Icc 0 L) ≠ ⊤ := by
      simp [Real.volume_Icc]
    have hintOn : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc 0 L) volume := by
      exact integrableOn_const (s := Set.Icc 0 L) (C := (1 : ℝ)) hs
    have hint : Integrable ((Set.Icc 0 L).indicator (fun _ : ℝ => (1 : ℝ))) volume := by
      exact (integrable_indicator_iff measurableSet_Icc).2 hintOn
    have hnorm :
        (fun z : ℝ => ‖h0 z‖ * ‖h0 z‖) = (Set.Icc 0 L).indicator (fun _ : ℝ => (1 : ℝ)) := by
      funext z
      by_cases hz : z ∈ Set.Icc 0 L <;> simp [h0, Set.indicator, hz]
    simpa [sq, h0, hnorm] using hint
  have htranslate_a : translate a h0 = Set.indicator (Set.Icc a (a + L)) fun _ ↦ (1 : ℂ) := by
    funext t
    by_cases ht : t ∈ Set.Icc a (a + L)
    · have hmem : t - a ∈ Set.Icc 0 L := by
        rw [Set.mem_Icc] at ht ⊢
        constructor <;> linarith
      simp [h0, translate, ht, hmem]
    · have hnotmem : t - a ∉ Set.Icc 0 L := by
        intro hmem
        apply ht
        rw [Set.mem_Icc] at hmem ⊢
        constructor <;> linarith
      simp [h0, translate, ht, hnotmem]
  have htranslate_b : translate b h0 = Set.indicator (Set.Icc b (b + L)) fun _ ↦ (1 : ℂ) := by
    funext t
    by_cases ht : t ∈ Set.Icc b (b + L)
    · have hmem : t - b ∈ Set.Icc 0 L := by
        rw [Set.mem_Icc] at ht ⊢
        constructor <;> linarith
      simp [h0, translate, ht, hmem]
    · have hnotmem : t - b ∉ Set.Icc 0 L := by
        intro hmem
        apply ht
        rw [Set.mem_Icc] at hmem ⊢
        constructor <;> linarith
      simp [h0, translate, ht, hnotmem]
  rw [← htranslate_a, ← htranslate_b]
  simpa [h0] using
    (crossAmbiguity_translate_translate (f := h0) (g := h0)
      hmem0 hmem0 (a := a) (b := b)
      (x := x) (ω := ω))

theorem crossAmbiguity_indicator_indicator_mixed (a b L₁ L₂ : ℝ) (x ω : ℝ) :
    crossAmbiguity (Set.indicator (Set.Icc a (a + L₁)) fun _ ↦ (1 : ℂ))
      (Set.indicator (Set.Icc b (b + L₂)) fun _ ↦ (1 : ℂ)) x ω =
        (Real.fourierChar (-(ω * (a + b) / 2)) : ℂ) *
          crossAmbiguity (Set.indicator (Set.Icc 0 L₁) fun _ ↦ (1 : ℂ))
            (Set.indicator (Set.Icc 0 L₂) fun _ ↦ (1 : ℂ)) (x - (a - b)) ω := by
  let h0₁ : ℝ → ℂ := Set.indicator (Set.Icc 0 L₁) fun _ ↦ (1 : ℂ)
  let h0₂ : ℝ → ℂ := Set.indicator (Set.Icc 0 L₂) fun _ ↦ (1 : ℂ)
  have hmem0 : ∀ L : ℝ, MemLp (Set.indicator (Set.Icc 0 L) fun _ ↦ (1 : ℂ)) 2 volume := by
    intro L
    have hsm : AEStronglyMeasurable (Set.indicator (Set.Icc 0 L) fun _ ↦ (1 : ℂ)) volume := by
      exact (Measurable.indicator (by fun_prop) measurableSet_Icc).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq_norm hsm]
    have hs : volume (Set.Icc 0 L) ≠ ⊤ := by
      simp [Real.volume_Icc]
    have hintOn : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc 0 L) volume := by
      exact integrableOn_const (s := Set.Icc 0 L) (C := (1 : ℝ)) hs
    have hint : Integrable ((Set.Icc 0 L).indicator (fun _ : ℝ => (1 : ℝ))) volume := by
      exact (integrable_indicator_iff measurableSet_Icc).2 hintOn
    have hnorm :
        (fun z : ℝ => ‖Set.indicator (Set.Icc 0 L) (fun _ ↦ (1 : ℂ)) z‖ *
          ‖Set.indicator (Set.Icc 0 L) (fun _ ↦ (1 : ℂ)) z‖) =
            (Set.Icc 0 L).indicator (fun _ : ℝ => (1 : ℝ)) := by
      funext z
      by_cases hz : z ∈ Set.Icc 0 L <;> simp [Set.indicator, hz]
    simpa [sq, hnorm] using hint
  have htranslate : ∀ (c L : ℝ),
      translate c (Set.indicator (Set.Icc 0 L) fun _ ↦ (1 : ℂ)) =
        Set.indicator (Set.Icc c (c + L)) fun _ ↦ (1 : ℂ) := by
    intro c L
    funext t
    by_cases ht : t ∈ Set.Icc c (c + L)
    · have hmem : t - c ∈ Set.Icc 0 L := by
        rw [Set.mem_Icc] at ht ⊢
        constructor <;> linarith
      simp [translate, ht, hmem]
    · have hnotmem : t - c ∉ Set.Icc 0 L := by
        intro hmem
        apply ht
        rw [Set.mem_Icc] at hmem ⊢
        constructor <;> linarith
      simp [translate, ht, hnotmem]
  have htranslate_a : translate a h0₁ = Set.indicator (Set.Icc a (a + L₁)) fun _ ↦ (1 : ℂ) := by
    simpa [h0₁] using (htranslate a L₁)
  have htranslate_b : translate b h0₂ = Set.indicator (Set.Icc b (b + L₂)) fun _ ↦ (1 : ℂ) := by
    simpa [h0₂] using (htranslate b L₂)
  rw [← htranslate_a, ← htranslate_b]
  simpa [h0₁, h0₂] using
    (crossAmbiguity_translate_translate (f := h0₁) (g := h0₂)
      (hmem0 L₁) (hmem0 L₂) (a := a) (b := b)
      (x := x) (ω := ω))

private theorem ambiguity_indicator_Icc_eq_zero_aux
    (L : ℝ) (hL : 0 < L) (y ω : ℝ) (hy : L ≤ |y|) :
    ambiguity (Set.indicator (Set.Icc 0 L) fun _ ↦ (1 : ℂ)) y ω = 0 := by
  let h0 : ℝ → ℂ := Set.indicator (Set.Icc 0 L) fun _ ↦ (1 : ℂ)
  let S : Set ℝ :=
    Set.Icc (-y / 2) (L - y / 2) ∩ Set.Icc (y / 2) (L + y / 2)
  have hleft :
      ∀ t : ℝ, t + y / 2 ∈ Set.Icc 0 L ↔ t ∈ Set.Icc (-y / 2) (L - y / 2) := by
    intro t
    rw [Set.mem_Icc, Set.mem_Icc]
    constructor <;> intro ht <;> constructor <;> linarith
  have hright :
      ∀ t : ℝ, t - y / 2 ∈ Set.Icc 0 L ↔ t ∈ Set.Icc (y / 2) (L + y / 2) := by
    intro t
    rw [Set.mem_Icc, Set.mem_Icc]
    constructor <;> intro ht <;> constructor <;> linarith
  have hintegrand :
      (fun t ↦ h0 (t + y / 2) * star (h0 (t - y / 2)) * (Real.fourierChar (-(ω * t)) : ℂ)) =
        S.indicator (fun t ↦ (Real.fourierChar (-(ω * t)) : ℂ)) := by
    funext t
    by_cases hSin : t ∈ S
    · rcases hSin with ⟨htl, htr⟩
      have hSin' : t ∈ S := ⟨htl, htr⟩
      have htl' : t + y / 2 ∈ Set.Icc 0 L := (hleft t).mpr htl
      have htr' : t - y / 2 ∈ Set.Icc 0 L := (hright t).mpr htr
      simp [h0, S, hSin', htl', htr']
    · by_cases htl : t + y / 2 ∈ Set.Icc 0 L
      · by_cases htr : t - y / 2 ∈ Set.Icc 0 L
        · exfalso
          apply hSin
          exact ⟨(hleft t).mp htl, (hright t).mp htr⟩
        · simp [h0, S, hSin, htl, htr]
      · simp [h0, S, hSin, htl]
  have hOverlap : S = Set.Icc (|y| / 2) (L - |y| / 2) := by
    ext x
    constructor
    · rintro ⟨⟨hx11, hx12⟩, ⟨hx21, hx22⟩⟩
      by_cases hypos : 0 ≤ y
      · have habs : |y| = y := abs_of_nonneg hypos
        rw [Set.mem_Icc, habs]
        exact ⟨hx21, hx12⟩
      · have hyneg : y ≤ 0 := le_of_not_ge hypos
        have habs : |y| = -y := abs_of_nonpos hyneg
        rw [Set.mem_Icc, habs]
        constructor
        · exact hx11
        · linarith
    · intro hx
      by_cases hypos : 0 ≤ y
      · have habs : |y| = y := abs_of_nonneg hypos
        rw [Set.mem_Icc, habs] at hx
        rcases hx with ⟨hx1, hx2⟩
        have h1 : -y / 2 ≤ x := by linarith
        have h2 : x ≤ L - y / 2 := hx2
        have h3 : y / 2 ≤ x := hx1
        have h4 : x ≤ L + y / 2 := by linarith
        exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      · have hyneg : y ≤ 0 := le_of_not_ge hypos
        have habs : |y| = -y := abs_of_nonpos hyneg
        rw [Set.mem_Icc, habs] at hx
        rcases hx with ⟨hx1, hx2⟩
        have h1 : -y / 2 ≤ x := hx1
        have h2 : x ≤ L - y / 2 := by linarith
        have h3 : y / 2 ≤ x := by linarith
        have h4 : x ≤ L + y / 2 := by linarith
        exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  have hmeasure : volume S = 0 := by
    rw [hOverlap, Real.volume_Icc, ENNReal.ofReal_eq_zero]
    linarith
  calc
    ambiguity h0 y ω = ∫ t, S.indicator (fun t ↦ (Real.fourierChar (-(ω * t)) : ℂ)) t := by
      rw [ambiguity, crossAmbiguity]
      simp only [hintegrand]
    _ = ∫ t in S, (Real.fourierChar (-(ω * t)) : ℂ) := by
      rw [integral_indicator]
      exact measurableSet_Icc.inter measurableSet_Icc
    _ = 0 := by
      exact setIntegral_measure_zero _ hmeasure

theorem crossAmbiguity_indicator_indicator_eq_zero
    (a b : ℝ) (L : ℝ) (hL : 0 < L) (x ω : ℝ)
    (hx : L ≤ |x - (a - b)|) :
    crossAmbiguity (Set.indicator (Set.Icc a (a + L)) fun _ ↦ (1 : ℂ))
      (Set.indicator (Set.Icc b (b + L)) fun _ ↦ (1 : ℂ)) x ω = 0 := by
  let h0 : ℝ → ℂ := Set.indicator (Set.Icc 0 L) fun _ ↦ (1 : ℂ)
  have hmem0 : MemLp h0 2 volume := by
    have hsm : AEStronglyMeasurable h0 volume := by
      exact (Measurable.indicator (by fun_prop) measurableSet_Icc).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq_norm hsm]
    have hs : volume (Set.Icc 0 L) ≠ ⊤ := by
      simp [Real.volume_Icc]
    have hintOn : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc 0 L) volume := by
      exact integrableOn_const (s := Set.Icc 0 L) (C := (1 : ℝ)) hs
    have hint : Integrable ((Set.Icc 0 L).indicator (fun _ : ℝ => (1 : ℝ))) volume := by
      exact (integrable_indicator_iff measurableSet_Icc).2 hintOn
    have hnorm :
        (fun z : ℝ => ‖h0 z‖ * ‖h0 z‖) = (Set.Icc 0 L).indicator (fun _ : ℝ => (1 : ℝ)) := by
      funext z
      by_cases hz : z ∈ Set.Icc 0 L <;> simp [h0, Set.indicator, hz]
    simpa [sq, h0, hnorm] using hint
  have htranslate_a : translate a h0 = Set.indicator (Set.Icc a (a + L)) fun _ ↦ (1 : ℂ) := by
    funext t
    by_cases ht : t ∈ Set.Icc a (a + L)
    · have hmem : t - a ∈ Set.Icc 0 L := by
        rw [Set.mem_Icc] at ht ⊢
        constructor <;> linarith
      simp [h0, translate, ht, hmem]
    · have hnotmem : t - a ∉ Set.Icc 0 L := by
        intro hmem
        apply ht
        rw [Set.mem_Icc] at hmem ⊢
        constructor <;> linarith
      simp [h0, translate, ht, hnotmem]
  have htranslate_b : translate b h0 = Set.indicator (Set.Icc b (b + L)) fun _ ↦ (1 : ℂ) := by
    funext t
    by_cases ht : t ∈ Set.Icc b (b + L)
    · have hmem : t - b ∈ Set.Icc 0 L := by
        rw [Set.mem_Icc] at ht ⊢
        constructor <;> linarith
      simp [h0, translate, ht, hmem]
    · have hnotmem : t - b ∉ Set.Icc 0 L := by
        intro hmem
        apply ht
        rw [Set.mem_Icc] at hmem ⊢
        constructor <;> linarith
      simp [h0, translate, ht, hnotmem]
  have hzero_center :
      crossAmbiguity h0 h0 (x - (a - b)) ω = 0 := by
    simpa [ambiguity, h0] using
      (ambiguity_indicator_Icc_eq_zero_aux (L := L) hL (y := x - (a - b)) (ω := ω) hx)
  rw [← htranslate_a, ← htranslate_b]
  rw [crossAmbiguity_translate_translate (f := h0) (g := h0)
    hmem0 hmem0 (a := a) (b := b) (x := x) (ω := ω)]
  simp [hzero_center]

theorem ambiguity_indicator_Icc (L : ℝ) (_hL : 0 < L) (y ω : ℝ) (hy : |y| < L) :
    ambiguity (Set.indicator (Set.Icc 0 L) fun _ ↦ (1 : ℂ)) y ω =
      (Real.fourierChar (-(ω * L / 2)) : ℂ) * sincPiComplex (ω * (L - |y|)) * (L - |y|) := by
  let h0 : ℝ → ℂ := Set.indicator (Set.Icc 0 L) fun _ ↦ (1 : ℂ)
  let S : Set ℝ :=
    Set.Icc (-y / 2) (L - y / 2) ∩ Set.Icc (y / 2) (L + y / 2)
  let T : ℝ := L - |y|
  have hT : 0 < T := by
    dsimp [T]
    linarith
  have hleft :
      ∀ t : ℝ, t + y / 2 ∈ Set.Icc 0 L ↔ t ∈ Set.Icc (-y / 2) (L - y / 2) := by
    intro t
    rw [Set.mem_Icc, Set.mem_Icc]
    constructor <;> intro ht <;> constructor <;> linarith
  have hright :
      ∀ t : ℝ, t - y / 2 ∈ Set.Icc 0 L ↔ t ∈ Set.Icc (y / 2) (L + y / 2) := by
    intro t
    rw [Set.mem_Icc, Set.mem_Icc]
    constructor <;> intro ht <;> constructor <;> linarith
  have hintegrand :
      (fun t ↦ h0 (t + y / 2) * star (h0 (t - y / 2)) * (Real.fourierChar (-(ω * t)) : ℂ)) =
        S.indicator (fun t ↦ (Real.fourierChar (-(ω * t)) : ℂ)) := by
    funext t
    by_cases hSin : t ∈ S
    · rcases hSin with ⟨htl, htr⟩
      have hSin' : t ∈ S := ⟨htl, htr⟩
      have htl' : t + y / 2 ∈ Set.Icc 0 L := (hleft t).mpr htl
      have htr' : t - y / 2 ∈ Set.Icc 0 L := (hright t).mpr htr
      simp [h0, S, hSin', htl', htr']
    · by_cases htl : t + y / 2 ∈ Set.Icc 0 L
      · by_cases htr : t - y / 2 ∈ Set.Icc 0 L
        · exfalso
          apply hSin
          exact ⟨(hleft t).mp htl, (hright t).mp htr⟩
        · simp [h0, S, hSin, htl, htr]
      · simp [h0, S, hSin, htl]
  have hOverlap : S = Set.Icc (|y| / 2) (L - |y| / 2) := by
    ext x
    constructor
    · rintro ⟨⟨hx11, hx12⟩, ⟨hx21, hx22⟩⟩
      by_cases hypos : 0 ≤ y
      · have habs : |y| = y := abs_of_nonneg hypos
        rw [Set.mem_Icc, habs]
        exact ⟨hx21, hx12⟩
      · have hyneg : y ≤ 0 := le_of_not_ge hypos
        have habs : |y| = -y := abs_of_nonpos hyneg
        rw [Set.mem_Icc, habs]
        constructor
        · exact hx11
        · linarith
    · intro hx
      by_cases hypos : 0 ≤ y
      · have habs : |y| = y := abs_of_nonneg hypos
        rw [Set.mem_Icc, habs] at hx
        rcases hx with ⟨hx1, hx2⟩
        have h1 : -y / 2 ≤ x := by linarith
        have h2 : x ≤ L - y / 2 := hx2
        have h3 : y / 2 ≤ x := hx1
        have h4 : x ≤ L + y / 2 := by linarith
        exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      · have hyneg : y ≤ 0 := le_of_not_ge hypos
        have habs : |y| = -y := abs_of_nonpos hyneg
        rw [Set.mem_Icc, habs] at hx
        rcases hx with ⟨hx1, hx2⟩
        have h1 : -y / 2 ≤ x := hx1
        have h2 : x ≤ L - y / 2 := by linarith
        have h3 : y / 2 ≤ x := by linarith
        have h4 : x ≤ L + y / 2 := by linarith
        exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  have hle : |y| / 2 ≤ L - |y| / 2 := by
    linarith
  have hshift :
      ∫ t in Set.Icc (|y| / 2) (L - |y| / 2), (Real.fourierChar (-(ω * t)) : ℂ) =
        (Real.fourierChar (-(ω * (|y| / 2))) : ℂ) *
          ∫ t in 0..T, (Real.fourierChar (-(ω * t)) : ℂ) := by
    have hinterval :
        ∫ t in Set.Icc (|y| / 2) (L - |y| / 2), (Real.fourierChar (-(ω * t)) : ℂ) =
          ∫ t in (|y| / 2)..(L - |y| / 2), (Real.fourierChar (-(ω * t)) : ℂ) := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
    have hcomp := intervalIntegral.integral_comp_add_right
      (f := fun t : ℝ ↦ (Real.fourierChar (-(ω * t)) : ℂ)) (a := (0 : ℝ)) (b := T) (|y| / 2)
    have hcomp' :
        ∫ t in (|y| / 2)..(L - |y| / 2), (Real.fourierChar (-(ω * t)) : ℂ) =
          ∫ t in 0..T, (Real.fourierChar (-(ω * (t + |y| / 2))) : ℂ) := by
      have htmp :
          ∫ t in (|y| / 2)..(T + |y| / 2), (Real.fourierChar (-(ω * t)) : ℂ) =
            ∫ t in 0..T, (Real.fourierChar (-(ω * (t + |y| / 2))) : ℂ) := by
        simpa using hcomp.symm
      have hend : T + |y| / 2 = L - |y| / 2 := by
        dsimp [T]
        ring_nf
      simpa [hend] using htmp
    have hphase : ∀ t : ℝ,
        (Real.fourierChar (-(ω * (t + |y| / 2))) : ℂ) =
          (Real.fourierChar (-(ω * (|y| / 2))) : ℂ) * (Real.fourierChar (-(ω * t)) : ℂ) := by
      intro t
      have hmul := Real.fourierChar.map_add_eq_mul' (-(ω * (|y| / 2))) (-(ω * t))
      simpa [mul_add, add_comm, add_left_comm, add_assoc, mul_assoc, mul_left_comm, mul_comm] using
        congrArg (fun z : Circle ↦ (z : ℂ)) hmul
    have hconst :
        ∫ t in 0..T, (Real.fourierChar (-(ω * (t + |y| / 2))) : ℂ) =
          (Real.fourierChar (-(ω * (|y| / 2))) : ℂ) *
            ∫ t in 0..T, (Real.fourierChar (-(ω * t)) : ℂ) := by
      calc
        ∫ t in 0..T, (Real.fourierChar (-(ω * (t + |y| / 2))) : ℂ)
            = ∫ t in 0..T, (Real.fourierChar (-(ω * (|y| / 2))) : ℂ) *
                (Real.fourierChar (-(ω * t)) : ℂ) := by
                  congr with t
                  exact hphase t
        _ = (Real.fourierChar (-(ω * (|y| / 2))) : ℂ) * ∫ t in 0..T,
              (Real.fourierChar (-(ω * t)) : ℂ) := by
                exact intervalIntegral.integral_const_mul
                  (r := (Real.fourierChar (-(ω * (|y| / 2))) : ℂ))
                  (f := fun t : ℝ ↦ (Real.fourierChar (-(ω * t)) : ℂ))
    exact hinterval.trans (hcomp'.trans hconst)
  have hphase_total :
      (Real.fourierChar (-(ω * (|y| / 2))) : ℂ) *
          (Real.fourierChar (-(ω * T / 2)) : ℂ) =
        (Real.fourierChar (-(ω * L / 2)) : ℂ) := by
    have hmul := Real.fourierChar.map_add_eq_mul' (-(ω * (|y| / 2))) (-(ω * T / 2))
    have harg : -(ω * (|y| / 2)) + -(ω * T / 2) = -(ω * L / 2) := by
      dsimp [T]
      ring_nf
    simpa [harg, mul_assoc, mul_comm, mul_left_comm] using
      (congrArg (fun z : Circle ↦ (z : ℂ)) hmul).symm
  calc
    ambiguity h0 y ω = ∫ t in S, (Real.fourierChar (-(ω * t)) : ℂ) := by
      rw [ambiguity, crossAmbiguity]
      rw [hintegrand, integral_indicator]
      exact measurableSet_Icc.inter measurableSet_Icc
    _ = ∫ t in Set.Icc (|y| / 2) (L - |y| / 2), (Real.fourierChar (-(ω * t)) : ℂ) := by
      rw [hOverlap]
    _ = (Real.fourierChar (-(ω * (|y| / 2))) : ℂ) * ∫ t in 0..T,
          (Real.fourierChar (-(ω * t)) : ℂ) := hshift
    _ = (Real.fourierChar (-(ω * (|y| / 2))) : ℂ) *
          ((Real.fourierChar (-(ω * T / 2)) : ℂ) * sincPiComplex (ω * T) * T) := by
          rw [integral_cexp_symmetric T ω hT]
    _ = (Real.fourierChar (-(ω * (|y| / 2))) : ℂ) *
          (Real.fourierChar (-(ω * T / 2)) : ℂ) * sincPiComplex (ω * T) * T := by
        ring_nf
    _ = (Real.fourierChar (-(ω * L / 2)) : ℂ) * sincPiComplex (ω * T) * T := by
          rw [hphase_total]
    _ = (Real.fourierChar (-(ω * L / 2)) : ℂ) * sincPiComplex (ω * (L - |y|)) * (L - |y|) := by
          simp [T]

theorem ambiguity_indicator_Icc_eq_zero (L : ℝ) (hL : 0 < L) (y ω : ℝ) (hy : L ≤ |y|) :
    ambiguity (Set.indicator (Set.Icc 0 L) fun _ ↦ (1 : ℂ)) y ω = 0 := by
  simpa using ambiguity_indicator_Icc_eq_zero_aux (L := L) hL (y := y) (ω := ω) hy

theorem ambiguity_indicator_zeros_discrete (L : ℝ) (hL : 0 < L) (y : ℝ) (hy : |y| < L) :
    {ω : ℝ | ambiguity (Set.indicator (Set.Icc 0 L) fun _ ↦ (1 : ℂ)) y ω = 0} =
      {ω : ℝ | sincPiComplex (ω * (L - |y|)) = 0} := by
  ext ω
  have hphase_ne : (Real.fourierChar (-(ω * L / 2)) : ℂ) ≠ 0 := by
    simp [Real.fourierChar_apply]
  have hlen_pos : 0 < L - |y| := by
    linarith
  have hlen_ne : (L - |y| : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hlen_pos)
  simp only [Set.mem_setOf_eq]
  rw [ambiguity_indicator_Icc (L := L) hL (y := y) (ω := ω) hy]
  constructor
  · intro hzero
    have hzero' :
        ((Real.fourierChar (-(ω * L / 2)) : ℂ) * sincPiComplex (ω * (L - |y|))) *
          (L - |y| : ℂ) = 0 := by
      simpa [mul_assoc] using hzero
    have hsinc_prod :
        (Real.fourierChar (-(ω * L / 2)) : ℂ) * sincPiComplex (ω * (L - |y|)) = 0 :=
      Or.resolve_right (mul_eq_zero.mp hzero') hlen_ne
    exact Or.resolve_left (mul_eq_zero.mp hsinc_prod) hphase_ne
  · intro hsinc
    simp [hsinc]

theorem indicator_Icc_aestronglyMeasurable (a b : ℝ) :
    AEStronglyMeasurable (Set.indicator (Set.Icc a b) fun _ ↦ (1 : ℂ)) volume := by
  exact (Measurable.indicator (by fun_prop) measurableSet_Icc).aestronglyMeasurable

theorem indicator_Icc_memLp (a b : ℝ) :
    MemLp (Set.indicator (Set.Icc a b) fun _ ↦ (1 : ℂ)) 2 volume := by
  have hsm : AEStronglyMeasurable (Set.indicator (Set.Icc a b) fun _ ↦ (1 : ℂ)) volume := by
    exact (Measurable.indicator (by fun_prop) measurableSet_Icc).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hsm]
  have hs : volume (Set.Icc a b) ≠ ⊤ := by
    simp [Real.volume_Icc]
  have hintOn : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) volume := by
    exact integrableOn_const (s := Set.Icc a b) (C := (1 : ℝ)) hs
  have hint : Integrable ((Set.Icc a b).indicator (fun _ : ℝ => (1 : ℝ))) volume := by
    exact (integrable_indicator_iff measurableSet_Icc).2 hintOn
  have hnorm :
      (fun x : ℝ => ‖(Set.Icc a b).indicator (fun _ : ℝ => (1 : ℂ)) x‖ *
        ‖(Set.Icc a b).indicator (fun _ : ℝ => (1 : ℂ)) x‖) =
        (Set.Icc a b).indicator (fun _ : ℝ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ Set.Icc a b
    · simp [Set.indicator, hx]
    · simp [Set.indicator, hx]
  simpa [sq, hnorm] using hint

theorem crossAmbiguity_indicator_indicator_mixed_eq_zero
    (L₁ L₂ y ω : ℝ) (hy : max L₁ L₂ ≤ |y|) :
    crossAmbiguity (Set.indicator (Set.Icc 0 L₁) fun _ ↦ (1 : ℂ))
      (Set.indicator (Set.Icc 0 L₂) fun _ ↦ (1 : ℂ)) y ω = 0 := by
  let h0₁ : ℝ → ℂ := Set.indicator (Set.Icc 0 L₁) fun _ ↦ (1 : ℂ)
  let h0₂ : ℝ → ℂ := Set.indicator (Set.Icc 0 L₂) fun _ ↦ (1 : ℂ)
  let S : Set ℝ :=
    Set.Icc (-y / 2) (L₁ - y / 2) ∩ Set.Icc (y / 2) (L₂ + y / 2)
  have hleft :
      ∀ t : ℝ, t + y / 2 ∈ Set.Icc 0 L₁ ↔ t ∈ Set.Icc (-y / 2) (L₁ - y / 2) := by
    intro t
    rw [Set.mem_Icc, Set.mem_Icc]
    constructor <;> intro ht <;> constructor <;> linarith
  have hright :
      ∀ t : ℝ, t - y / 2 ∈ Set.Icc 0 L₂ ↔ t ∈ Set.Icc (y / 2) (L₂ + y / 2) := by
    intro t
    rw [Set.mem_Icc, Set.mem_Icc]
    constructor <;> intro ht <;> constructor <;> linarith
  have hintegrand :
      (fun t ↦ h0₁ (t + y / 2) * star (h0₂ (t - y / 2)) *
        (Real.fourierChar (-(ω * t)) : ℂ)) =
        S.indicator (fun t ↦ (Real.fourierChar (-(ω * t)) : ℂ)) := by
    funext t
    by_cases hS : t ∈ S
    · rcases hS with ⟨htl, htr⟩
      have hS' : t ∈ S := ⟨htl, htr⟩
      have htl' : t + y / 2 ∈ Set.Icc 0 L₁ := (hleft t).2 htl
      have htr' : t - y / 2 ∈ Set.Icc 0 L₂ := (hright t).2 htr
      simp [h0₁, h0₂, S, hS', htl', htr']
    · by_cases htl : t + y / 2 ∈ Set.Icc 0 L₁
      · by_cases htr : t - y / 2 ∈ Set.Icc 0 L₂
        · exfalso
          apply hS
          exact ⟨(hleft t).1 htl, (hright t).1 htr⟩
        · simp [h0₁, h0₂, S, hS, htl, htr]
      · simp [h0₁, h0₂, S, hS, htl]
  have hmeasure : volume S = 0 := by
    by_cases hy0 : 0 ≤ y
    · have hyabs : |y| = y := abs_of_nonneg hy0
      have hyL1 : L₁ ≤ y := by
        have hmax : max L₁ L₂ ≤ y := by simpa [hyabs] using hy
        exact le_trans (le_max_left _ _) hmax
      have hsubset : S ⊆ ({y / 2} : Set ℝ) := by
        intro t ht
        rcases ht with ⟨htl, htr⟩
        rw [Set.mem_Icc] at htl htr
        have hle : t ≤ y / 2 := by linarith [htl.2, hyL1]
        have hge : y / 2 ≤ t := by linarith [htr.1]
        have ht' : t = y / 2 := le_antisymm hle hge
        simp [ht']
      exact measure_mono_null hsubset (by simp)
    · have hyneg : y ≤ 0 := le_of_not_ge hy0
      have hyabs : |y| = -y := abs_of_nonpos hyneg
      have hyL2 : L₂ ≤ -y := by
        have hmax : max L₁ L₂ ≤ -y := by simpa [hyabs] using hy
        exact le_trans (le_max_right _ _) hmax
      have hsubset : S ⊆ ({-y / 2} : Set ℝ) := by
        intro t ht
        rcases ht with ⟨htl, htr⟩
        rw [Set.mem_Icc] at htl htr
        have hge : -y / 2 ≤ t := by linarith [htl.1]
        have hle : t ≤ -y / 2 := by linarith [htr.2, hyL2]
        have ht' : t = -y / 2 := le_antisymm hle hge
        simp [ht']
      exact measure_mono_null hsubset (by simp)
  calc
    crossAmbiguity h0₁ h0₂ y ω =
        ∫ t, S.indicator (fun t ↦ (Real.fourierChar (-(ω * t)) : ℂ)) t := by
      rw [crossAmbiguity, hintegrand]
    _ = ∫ t in S, (Real.fourierChar (-(ω * t)) : ℂ) := by
      rw [integral_indicator]
      exact measurableSet_Icc.inter measurableSet_Icc
    _ = 0 := by
      exact setIntegral_measure_zero _ hmeasure

theorem overlap_interval (y L : ℝ) :
    Set.Icc (-y / 2) (L - y / 2) ∩ Set.Icc (y / 2) (L + y / 2) =
      Set.Icc (|y| / 2) (L - |y| / 2) := by
  ext x
  constructor
  · rintro ⟨⟨hx11, hx12⟩, ⟨hx21, hx22⟩⟩
    by_cases hypos : 0 ≤ y
    · have habs : |y| = y := abs_of_nonneg hypos
      rw [Set.mem_Icc, habs]
      exact ⟨hx21, hx12⟩
    · have hyneg : y ≤ 0 := le_of_not_ge hypos
      have habs : |y| = -y := abs_of_nonpos hyneg
      rw [Set.mem_Icc, habs]
      constructor
      · exact hx11
      · linarith
  · intro hx
    by_cases hypos : 0 ≤ y
    · have habs : |y| = y := abs_of_nonneg hypos
      rw [Set.mem_Icc, habs] at hx
      rcases hx with ⟨hx1, hx2⟩
      have h1 : -y / 2 ≤ x := by linarith
      have h2 : x ≤ L - y / 2 := hx2
      have h3 : y / 2 ≤ x := hx1
      have h4 : x ≤ L + y / 2 := by linarith
      exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    · have hyneg : y ≤ 0 := le_of_not_ge hypos
      have habs : |y| = -y := abs_of_nonpos hyneg
      rw [Set.mem_Icc, habs] at hx
      rcases hx with ⟨hx1, hx2⟩
      have h1 : -y / 2 ≤ x := hx1
      have h2 : x ≤ L - y / 2 := by linarith
      have h3 : y / 2 ≤ x := by linarith
      have h4 : x ≤ L + y / 2 := by linarith
      exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

theorem overlap_volume (y L : ℝ) :
    volume (Set.Icc (|y| / 2) (L - |y| / 2)) =
      ENNReal.ofReal (L - |y|) := by
  rw [Real.volume_Icc]
  congr 1
  ring_nf

end

end AmbiguityZeros.ToMathlib
