import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

namespace AmbiguityZeros.ToMathlib

noncomputable section

open MeasureTheory

variable {p : ENNReal} {f g u v : ℝ → ℂ}

def translate (x : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t ↦ f (t - x)

def modulate (ω : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t ↦ (Real.fourierChar (ω * t) : ℂ) * f t

/- Translation on Schwartz space, matching `translate` on underlying functions. -/
private def translateSchwartz (x : ℝ) : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.compSubConstCLM ℂ x

@[simp] private theorem translateSchwartz_apply (x : ℝ) (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    translateSchwartz x f t = f (t - x) := rfl

private theorem coe_translateSchwartz (x : ℝ) (f : SchwartzMap ℝ ℂ) :
    (translateSchwartz x f : ℝ → ℂ) = translate x f := by
  funext t
  rfl

/- Complex conjugation on Schwartz space, viewed as a real-linear map. -/
private def conjSchwartz : SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) (F := ℂ) (G := ℂ) Complex.conjCLE

@[simp] private theorem conjSchwartz_apply (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    conjSchwartz f t = star (f t) := by
  simp [conjSchwartz, Complex.conjCLE_apply]

theorem translate_zero (f : ℝ → ℂ) : translate 0 f = f := by
  funext t
  simp [translate]

theorem translate_translate (x y : ℝ) (f : ℝ → ℂ) :
    translate x (translate y f) = translate (x + y) f := by
  funext t
  exact congrArg f (by ring)

theorem translate_neg (x : ℝ) (f : ℝ → ℂ) :
    translate (-x) (translate x f) = f := by
  funext t
  exact congrArg f (by ring)

theorem modulate_zero (f : ℝ → ℂ) : modulate 0 f = f := by
  funext t
  simp [modulate]

private theorem norm_fourierChar_aux (x : ℝ) : ‖(Real.fourierChar x : ℂ)‖ = 1 := by
  simpa [Real.fourierChar_apply, mul_comm, mul_left_comm, mul_assoc] using
    Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)

def l2Fourier (f : ℝ → ℂ) (hf : MemLp f 2 volume) : ℝ → ℂ :=
  (FourierTransform.fourier (hf.toLp f) : MeasureTheory.Lp (α := ℝ) ℂ 2)

theorem l2Fourier_memLp (f : ℝ → ℂ) (hf : MemLp f 2 volume) :
    MemLp (l2Fourier f hf) 2 volume := by
  simpa [l2Fourier] using (MeasureTheory.Lp.memLp (FourierTransform.fourier (hf.toLp f) :
    MeasureTheory.Lp (α := ℝ) ℂ 2))

theorem l2Fourier_congr_ae (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hfg : f =ᵐ[volume] g) :
    l2Fourier f hf =ᵐ[volume] l2Fourier g hg := by
  have hLp : hf.toLp f = hg.toLp g := MemLp.toLp_congr hf hg hfg
  change (↑(FourierTransform.fourier (hf.toLp f)) : ℝ → ℂ) =ᵐ[volume]
    (↑(FourierTransform.fourier (hg.toLp g)) : ℝ → ℂ)
  rw [hLp]

theorem l2Fourier_const_mul_ae (c : ℂ) (hf : MemLp f 2 volume) :
    l2Fourier (fun t ↦ c * f t) (hf.const_mul c) =ᵐ[volume]
      fun t ↦ c * l2Fourier f hf t := by
  have hLp :
      (hf.const_mul c).toLp (fun t ↦ c * f t) = c • hf.toLp f := by
    simpa [Pi.smul_def, smul_eq_mul] using (MemLp.toLp_const_smul c hf)
  have hF :
      FourierTransform.fourier ((hf.const_mul c).toLp (fun t ↦ c * f t)) =
        c • FourierTransform.fourier (hf.toLp f) := by
    rw [hLp, FourierTransform.fourier_smul]
  change (↑(FourierTransform.fourier ((hf.const_mul c).toLp (fun t ↦ c * f t))) :
      ℝ → ℂ) =ᵐ[volume]
    fun t ↦ c * (↑(FourierTransform.fourier (hf.toLp f)) : ℝ → ℂ) t
  rw [hF]
  simpa [Pi.smul_def, smul_eq_mul] using
    (MeasureTheory.Lp.coeFn_smul c (FourierTransform.fourier (hf.toLp f) :
      MeasureTheory.Lp (α := ℝ) ℂ 2))

theorem not_exists_smul_l2Fourier_of_not_exists_smul
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hli : ¬ ∃ c : ℂ, v =ᵐ[volume] fun t ↦ c * u t) :
    ¬ ∃ c : ℂ,
      l2Fourier v hv =ᵐ[volume] fun t ↦ c * l2Fourier u hu t := by
  rintro ⟨c, hc⟩
  have hcu :=
    l2Fourier_const_mul_ae (f := u) c hu
  have hLpF :
      FourierTransform.fourier (hv.toLp v) =
        FourierTransform.fourier ((hu.const_mul c).toLp (fun t ↦ c * u t)) := by
    apply Lp.ext
    exact hc.trans hcu.symm
  have hLp :
      hv.toLp v = (hu.const_mul c).toLp (fun t ↦ c * u t) := by
    have h := congrArg FourierTransform.fourierInv hLpF
    simpa using h
  have hLpcoe :
      (↑(hv.toLp v) : ℝ → ℂ) =ᵐ[volume]
        (↑((hu.const_mul c).toLp (fun t ↦ c * u t)) : ℝ → ℂ) := by
    rw [hLp]
  exact hli ⟨c, hv.coeFn_toLp.symm.trans (hLpcoe.trans (hu.const_mul c).coeFn_toLp)⟩

theorem modulate_modulate (ω₁ ω₂ : ℝ) (f : ℝ → ℂ) :
    modulate ω₁ (modulate ω₂ f) = modulate (ω₁ + ω₂) f := by
  funext t
  rw [modulate, modulate, modulate]
  rw [Real.fourierChar_apply, Real.fourierChar_apply, Real.fourierChar_apply]
  simp [Complex.exp_add, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc]

theorem translate_modulate_comm (x ω : ℝ) (f : ℝ → ℂ) :
    translate x (modulate ω f) =
      fun t ↦ (Real.fourierChar (-(ω * x)) : ℂ) * modulate ω (translate x f) t := by
  funext t
  rw [translate, modulate, modulate, translate]
  rw [Real.fourierChar_apply, Real.fourierChar_apply, Real.fourierChar_apply]
  simp [Complex.exp_add, mul_add, add_mul, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]

theorem translate_modulate_comm_apply (x ω : ℝ) (f : ℝ → ℂ) (t : ℝ) :
    translate x (modulate ω f) t =
      (Real.fourierChar (-(ω * x)) : ℂ) * modulate ω (translate x f) t := by
  rw [translate, modulate, modulate, translate]
  rw [Real.fourierChar_apply, Real.fourierChar_apply, Real.fourierChar_apply]
  simp [Complex.exp_add, mul_add, add_mul, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]

theorem translate_measurable (x : ℝ) (hf : Measurable f) :
    Measurable (translate x f) := by
  simpa [translate] using hf.comp (measurable_id.sub measurable_const)

theorem translate_aestronglyMeasurable (x : ℝ) (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (translate x f) volume := by
  simpa [translate, sub_eq_add_neg] using
    hf.comp_measurePreserving (MeasureTheory.measurePreserving_add_right volume (-x))

theorem modulate_measurable (ω : ℝ) (hf : Measurable f) :
    Measurable (modulate ω f) := by
  have hchar : Measurable fun t : ℝ => (Real.fourierChar (ω * t) : ℂ) := by
    fun_prop
  simpa [modulate] using hchar.mul hf

theorem modulate_aestronglyMeasurable (ω : ℝ) (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (modulate ω f) volume := by
  have hchar : AEStronglyMeasurable (fun t : ℝ => (Real.fourierChar (ω * t) : ℂ)) volume := by
    exact
      (by fun_prop : Measurable fun t : ℝ => (Real.fourierChar (ω * t) : ℂ)).aestronglyMeasurable
  simpa [modulate] using hchar.mul hf

theorem conj_measurable (hf : Measurable f) :
    Measurable (fun t ↦ star (f t)) := by
  exact ContinuousStar.continuous_star.measurable.comp hf

theorem conj_aestronglyMeasurable (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (fun t ↦ star (f t)) volume := by
  simpa using hf.star

theorem translate_eLpNorm (x : ℝ) (hf : AEStronglyMeasurable f volume) :
    eLpNorm (translate x f) p volume = eLpNorm f p volume := by
  simpa [translate, sub_eq_add_neg] using
    eLpNorm_comp_measurePreserving hf (MeasureTheory.measurePreserving_add_right volume (-x))

theorem modulate_eLpNorm (ω : ℝ) (_hf : AEStronglyMeasurable f volume) :
    eLpNorm (modulate ω f) p volume = eLpNorm f p volume := by
  have hnorm : ∀ t : ℝ, ‖(Real.fourierChar (ω * t) : ℂ)‖ = 1 := by
    intro t
    simpa [Real.fourierChar_apply, mul_comm, mul_left_comm, mul_assoc] using
      Complex.norm_exp_ofReal_mul_I (2 * Real.pi * (ω * t))
  apply le_antisymm
  · have h₁ : ∀ᵐ t ∂volume, ‖modulate ω f t‖ ≤ (1 : ℝ) * ‖f t‖ := by
      refine Filter.Eventually.of_forall ?_
      intro t
      simp [modulate, hnorm t, mul_comm]
    have hle₁ : eLpNorm (modulate ω f) p volume ≤ eLpNorm f p volume := by
      have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (f := modulate ω f) (g := f) (c := 1) h₁ p
      simpa using h
    simpa [one_mul] using hle₁
  · have h₂ : ∀ᵐ t ∂volume, ‖f t‖ ≤ (1 : ℝ) * ‖modulate ω f t‖ := by
      refine Filter.Eventually.of_forall ?_
      intro t
      simp [modulate, hnorm t, mul_comm]
    have hle₂ : eLpNorm f p volume ≤ eLpNorm (modulate ω f) p volume := by
      have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (f := f) (g := modulate ω f) (c := 1) h₂ p
      simpa using h
    simpa [one_mul] using hle₂

theorem translate_memLp (x : ℝ) (hf : MemLp f p volume) :
    MemLp (translate x f) p volume := by
  simpa [translate, sub_eq_add_neg] using
    hf.comp_measurePreserving (MeasureTheory.measurePreserving_add_right volume (-x))

theorem modulate_memLp (ω : ℝ) (hf : MemLp f p volume) :
    MemLp (modulate ω f) p volume := by
  constructor
  · exact modulate_aestronglyMeasurable ω hf.1
  · simpa [modulate_eLpNorm ω hf.1] using hf.2

theorem conj_memLp (hf : MemLp f p volume) :
    MemLp (fun t ↦ star (f t)) p volume := by
  simpa using hf.star

theorem translate_integrable (x : ℝ) (hf : Integrable f volume) :
    Integrable (translate x f) volume := by
  have hmem : MemLp f 1 volume := (memLp_one_iff_integrable).mpr hf
  have hmem' : MemLp (translate x f) 1 volume := translate_memLp x hmem
  exact (memLp_one_iff_integrable).mp hmem'

theorem modulate_integrable (ω : ℝ) (hf : Integrable f volume) :
    Integrable (modulate ω f) volume := by
  have hmem : MemLp f 1 volume := (memLp_one_iff_integrable).mpr hf
  have hmem' : MemLp (modulate ω f) 1 volume := modulate_memLp ω hmem
  exact (memLp_one_iff_integrable).mp hmem'

theorem fourierIntegral_translate (x : ℝ) (_hf : Integrable f volume) :
    FourierTransform.fourier (translate x f) = modulate (-x) (FourierTransform.fourier f) := by
  have hL : (innerₗ ℝ) = LinearMap.mul ℝ ℝ := by
    ext
    simp [innerₗ_apply_apply]
  have h := (VectorFourier.fourierIntegral_comp_add_right (e := Real.fourierChar) (μ := volume)
      (L := LinearMap.mul ℝ ℝ) (f := f) (v₀ := -x))
  rw [FourierTransform.fourier]
  ext w
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) (translate x f) w =
    modulate (-x) (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) f) w
  simpa [translate, modulate, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc, Circle.smul_def,
    hL] using congrFun h w

theorem fourierIntegral_modulate (ω : ℝ) (_hf : Integrable f volume) :
    FourierTransform.fourier (modulate ω f) = translate ω (FourierTransform.fourier f) := by
  ext t
  rw [translate, Real.fourier_real_eq, Real.fourier_real_eq]
  refine integral_congr_ae ?_
  filter_upwards with v
  rw [modulate, Circle.smul_def]
  calc
    (Real.fourierChar (-(v * t)) : ℂ) * ((Real.fourierChar (ω * v) : ℂ) * f v)
        = ((Real.fourierChar (-(v * t)) : ℂ) * (Real.fourierChar (ω * v) : ℂ)) * f v := by
          ring
    _ = (Real.fourierChar (-(v * (t - ω))) : ℂ) * f v := by
          congr 1
          rw [Real.fourierChar_apply, Real.fourierChar_apply, Real.fourierChar_apply]
          rw [← Complex.exp_add]
          congr 1
          rw [← add_mul]
          congr 1
          push_cast
          ring

theorem modulate_translate_memLp (g : ℝ → ℂ) (ω x : ℝ) (hg : MemLp g p volume) :
    MemLp (modulate ω (translate x g)) p volume := by
  exact modulate_memLp ω (translate_memLp x hg)

theorem modulate_translate_aestronglyMeasurable (g : ℝ → ℂ) (ω x : ℝ)
    (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (modulate ω (translate x g)) volume := by
  exact modulate_aestronglyMeasurable ω (translate_aestronglyMeasurable x hg)

theorem modulate_translate_measurable (g : ℝ → ℂ) (ω x : ℝ) (hg : Measurable g) :
    Measurable (modulate ω (translate x g)) := by
  exact modulate_measurable ω (translate_measurable x hg)

theorem integrable_conj_mul_modulate_translate
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (x ω : ℝ) :
    Integrable (fun t ↦ star (f t) * (modulate ω (translate x g)) t) volume := by
  have h : MemLp (fun t ↦ star (f t) * (modulate ω (translate x g)) t) 1 volume := by
    simpa [mul_comm] using (modulate_translate_memLp g ω x hg).mul hf.star
  exact (memLp_one_iff_integrable).mp h

theorem integral_conj_mul_modulate_translate
    (_hf : MemLp f 2 volume) (_hg : MemLp g 2 volume) (x ω : ℝ) :
    ∫ t, star (f t) * (modulate ω (translate x g)) t =
      ∫ t, star (f t) * (Real.fourierChar (ω * t) : ℂ) * g (t - x) := by
  simp [modulate, translate, mul_left_comm, mul_comm]

theorem integrable_mul_of_memLp (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun t ↦ f t * g t) volume := by
  have h : MemLp (fun t ↦ f t * g t) 1 volume := by
    simpa [mul_comm] using hg.mul hf
  exact (memLp_one_iff_integrable).mp h

theorem norm_fourierChar (x : ℝ) : ‖(Real.fourierChar x : ℂ)‖ = 1 := by
  simpa [Real.fourierChar_apply, mul_comm, mul_left_comm, mul_assoc] using
    Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)

/-- Translation on `L²` as a linear isometry equivalence. -/
def translateLp (x : ℝ) :
    MeasureTheory.Lp (α := ℝ) ℂ 2 volume →ₗᵢ[ℂ] MeasureTheory.Lp (α := ℝ) ℂ 2 volume :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ (E := ℂ) (p := 2) (μ := volume) (μb := volume)
    (fun t : ℝ => t - x) (MeasureTheory.measurePreserving_sub_right volume x)

theorem translateLp_toLp (x : ℝ) (hf : MemLp f 2 volume) :
    translateLp x (hf.toLp f) = (translate_memLp x hf).toLp (translate x f) := by
  rfl

private theorem fourierChar_memLp_top (ω : ℝ) :
    MemLp (fun t : ℝ ↦ (Real.fourierChar (ω * t) : ℂ)) (⊤ : ENNReal) volume := by
  have hcont : Continuous fun t : ℝ ↦ (Real.fourierChar (ω * t) : ℂ) := by
    continuity
  refine memLp_top_of_bound hcont.aestronglyMeasurable 1 ?_
  filter_upwards with t
  exact le_of_eq (norm_fourierChar (ω * t))

/-- The fixed `L∞` Fourier character used for modulation on `L²`. -/
def fourierCharLp (ω : ℝ) : MeasureTheory.Lp (α := ℝ) ℂ (⊤ : ENNReal) volume :=
  (fourierChar_memLp_top ω).toLp fun t : ℝ ↦ (Real.fourierChar (ω * t) : ℂ)

theorem fourierCharLp_coeFn (ω : ℝ) :
    (fourierCharLp ω : ℝ → ℂ) =ᵐ[volume] fun t : ℝ ↦ (Real.fourierChar (ω * t) : ℂ) :=
  (fourierChar_memLp_top ω).coeFn_toLp

/-- Pointwise modulation on `L²`, using the canonical `Lp` representative. -/
def modulateLp (ω : ℝ) (g : MeasureTheory.Lp (α := ℝ) ℂ 2 volume) :
    MeasureTheory.Lp (α := ℝ) ℂ 2 volume :=
  ((MeasureTheory.Lp.memLp g).mul' (fourierChar_memLp_top ω)).toLp
    (fun t ↦ (Real.fourierChar (ω * t) : ℂ) * g t)

private theorem modulateLp_coeFn (ω : ℝ)
    (g : MeasureTheory.Lp (α := ℝ) ℂ 2 volume) :
    modulateLp ω g =ᵐ[volume] fun t ↦ (Real.fourierChar (ω * t) : ℂ) * g t := by
  simpa [modulateLp] using
    (MeasureTheory.MemLp.coeFn_toLp
      ((MeasureTheory.Lp.memLp g).mul' (fourierChar_memLp_top ω)))

private theorem modulateLp_add (ω : ℝ)
    (g h : MeasureTheory.Lp (α := ℝ) ℂ 2 volume) :
    modulateLp ω (g + h) = modulateLp ω g + modulateLp ω h := by
  apply MeasureTheory.Lp.ext
  filter_upwards [modulateLp_coeFn (ω := ω) (g := g + h),
    modulateLp_coeFn (ω := ω) (g := g),
    modulateLp_coeFn (ω := ω) (g := h),
    MeasureTheory.Lp.coeFn_add (modulateLp ω g) (modulateLp ω h),
    MeasureTheory.Lp.coeFn_add g h] with t hgh hg hh hsummod hsum
  have h1 :
      modulateLp ω (g + h) t =
        (g t + h t) * (Real.fourierChar (ω * t) : ℂ) := by
    rw [hsum] at hgh
    calc
      modulateLp ω (g + h) t = (Real.fourierChar (ω * t) : ℂ) * (g t + h t) := by
        simpa [Pi.add_apply] using hgh
      _ = (g t + h t) * (Real.fourierChar (ω * t) : ℂ) := by
        ring
  have h2 :
      (modulateLp ω g + modulateLp ω h) t =
        (g t + h t) * (Real.fourierChar (ω * t) : ℂ) := by
    calc
      (modulateLp ω g + modulateLp ω h) t =
          (Real.fourierChar (ω * t) : ℂ) * g t +
            (Real.fourierChar (ω * t) : ℂ) * h t := by
        simpa [hg, hh, Pi.add_apply, mul_add] using hsummod
      _ = (g t + h t) * (Real.fourierChar (ω * t) : ℂ) := by
        ring
  exact h1.trans h2.symm

private theorem modulateLp_smul (ω : ℝ) (c : ℂ)
    (g : MeasureTheory.Lp (α := ℝ) ℂ 2 volume) :
    modulateLp ω (c • g) = c • modulateLp ω g := by
  apply MeasureTheory.Lp.ext
  filter_upwards [modulateLp_coeFn (ω := ω) (g := c • g),
    modulateLp_coeFn (ω := ω) (g := g),
    MeasureTheory.Lp.coeFn_smul c (modulateLp ω g),
    MeasureTheory.Lp.coeFn_smul c g] with t hcg hg hsmulmod hsmulg
  have h1 :
      modulateLp ω (c • g) t = c * (g t * (Real.fourierChar (ω * t) : ℂ)) := by
    simpa [hsmulg, mul_comm, mul_left_comm, mul_assoc] using hcg
  have h2 :
      (c • modulateLp ω g) t = c * (g t * (Real.fourierChar (ω * t) : ℂ)) := by
    simpa [hg, mul_comm, mul_left_comm, mul_assoc] using hsmulmod
  exact h1.trans h2.symm

private theorem modulateLp_norm (ω : ℝ)
    (g : MeasureTheory.Lp (α := ℝ) ℂ 2 volume) : ‖modulateLp ω g‖ = ‖g‖ := by
  rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def, eLpNorm_congr_ae
      (modulateLp_coeFn (ω := ω) (g := g))]
  exact congrArg ENNReal.toReal
    (modulate_eLpNorm (f := (g : ℝ → ℂ)) (p := (2 : ENNReal)) ω
      (MeasureTheory.Lp.aestronglyMeasurable g))

private def modulateLpCLM (ω : ℝ) :
    MeasureTheory.Lp (α := ℝ) ℂ 2 volume →L[ℂ] MeasureTheory.Lp (α := ℝ) ℂ 2 volume :=
  LinearMap.mkContinuous
    { toFun := modulateLp ω
      map_add' := modulateLp_add (ω := ω)
      map_smul' := modulateLp_smul (ω := ω) }
    1 (by
      intro g
      simp [modulateLp_norm (ω := ω) g, one_mul])

theorem modulateLp_toLp (ω : ℝ) (hf : MemLp f 2 volume) :
    modulateLp ω (hf.toLp f) = (modulate_memLp ω hf).toLp (modulate ω f) := by
  refine MemLp.toLp_congr
    ((MeasureTheory.Lp.memLp (hf.toLp f)).mul' (fourierChar_memLp_top ω))
    (modulate_memLp ω hf) ?_
  filter_upwards [hf.coeFn_toLp] with t ht
  simp [modulate, ht]

/-- Bridge-ready Fourier intertwining on Schwartz functions: translation becomes modulation. -/
theorem fourier_compSubConstCLM_eq_modulate
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    FourierTransform.fourier (f.compSubConstCLM ℂ x) =
      modulate (-x) (FourierTransform.fourier f) := by
  simpa [SchwartzMap.compSubConstCLM_apply, modulate, translate, SchwartzMap.fourier_coe]
    using (fourierIntegral_translate (f := f) x f.integrable)

/-- Bridge-ready Fourier intertwining on Schwartz functions: modulation becomes translation. -/
theorem fourier_modulate_eq_translate
    (f : SchwartzMap ℝ ℂ) (ω : ℝ) :
    FourierTransform.fourier (fun t ↦ (Real.fourierChar (ω * t) : ℂ) * f t) =
      translate ω (FourierTransform.fourier f) := by
  simpa [modulate, translate, SchwartzMap.fourier_coe] using
    (fourierIntegral_modulate (f := f) ω f.integrable)

private theorem contDiff_fourierChar_mul (n : WithTop ℕ∞) (ω : ℝ) :
    ContDiff ℝ n (fun t : ℝ ↦ (Real.fourierChar (ω * t) : ℂ)) := by
  have harg :
      ContDiff ℝ n (fun t : ℝ ↦ (((2 * Real.pi * (ω * t) : ℝ) : ℂ) * Complex.I)) := by
    exact (Complex.ofRealCLM.contDiff.comp
      (by fun_prop : ContDiff ℝ n fun t : ℝ ↦ 2 * Real.pi * (ω * t))).mul contDiff_const
  simpa [Real.fourierChar_apply] using Complex.contDiff_exp.comp harg

private theorem iteratedDeriv_fourierChar (n : ℕ) :
    iteratedDeriv n (fun x : ℝ ↦ (Real.fourierChar x : ℂ)) =
      fun x ↦ (2 * Real.pi * Complex.I) ^ n * (Real.fourierChar x : ℂ) := by
  let e : ℝ → ℂ := fun x ↦ (Real.fourierChar x : ℂ)
  change iteratedDeriv n e = fun x ↦ (2 * Real.pi * Complex.I) ^ n * e x
  induction n with
  | zero =>
      funext x
      simp
  | succ n ih =>
      funext x
      let c : ℂ := 2 * Real.pi * Complex.I
      calc
        iteratedDeriv (n + 1) e x = iteratedDeriv n (fun x ↦ c * e x) x := by
                rw [iteratedDeriv_succ']
                rw [show deriv e =
                    fun x ↦ c * e x by
                      funext x
                      simpa [e, c, mul_assoc, mul_left_comm, mul_comm] using
                        Real.deriv_fourierChar x]
        _ = c * iteratedDeriv n e x := by
              exact iteratedDeriv_const_mul_field (n := n) (x := x) (c := c) (f := e)
        _ = c ^ (n + 1) * e x := by
              rw [ih]
              change c * (c ^ n * e x) = c ^ (n + 1) * e x
              ring

private theorem fourierChar_mul_hasTemperateGrowth (ω : ℝ) :
    (fun t : ℝ ↦ (Real.fourierChar (ω * t) : ℂ)).HasTemperateGrowth := by
  refine ⟨?_, ?_⟩
  · simpa using (contDiff_fourierChar_mul (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) ω)
  · intro n
    refine ⟨0, ‖((ω : ℂ) ^ n)‖ * ‖(2 * Real.pi * Complex.I) ^ n‖, ?_⟩
    intro x
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hbase : ContDiff ℝ (n : WithTop ℕ∞) (fun y : ℝ ↦ (Real.fourierChar y : ℂ)) := by
      simpa using (contDiff_fourierChar_mul (n := (n : WithTop ℕ∞)) 1)
    have hcomp' :
        iteratedDeriv n (fun t : ℝ ↦ (Real.fourierChar (ω * t) : ℂ)) x =
          ω ^ n • iteratedDeriv n (fun y : ℝ ↦ (Real.fourierChar y : ℂ)) (ω * x) := by
      exact
        congrFun
          (iteratedDeriv_comp_const_smul
            (f := fun y : ℝ ↦ (Real.fourierChar y : ℂ))
            (n := n) (h := hbase) ω) x
    have hcomp :
        iteratedDeriv n (fun t : ℝ ↦ (Real.fourierChar (ω * t) : ℂ)) x =
          ((ω : ℂ) ^ n) * iteratedDeriv n (fun y : ℝ ↦ (Real.fourierChar y : ℂ)) (ω * x) := by
      rw [hcomp']
      simp [Complex.ofReal_pow]
    rw [hcomp]
    rw [show iteratedDeriv n (fun y : ℝ ↦ (Real.fourierChar y : ℂ)) (ω * x) =
        (2 * Real.pi * Complex.I) ^ n * (Real.fourierChar (ω * x) : ℂ) by
          simpa using congrFun (iteratedDeriv_fourierChar n) (ω * x)]
    calc
      ‖(ω : ℂ) ^ n * ((2 * Real.pi * Complex.I) ^ n * (Real.fourierChar (ω * x) : ℂ))‖
          = ‖(ω : ℂ) ^ n‖ * ‖(2 * Real.pi * Complex.I) ^ n * (Real.fourierChar (ω * x) : ℂ)‖ := by
              rw [norm_mul]
      _ = ‖((ω : ℂ) ^ n)‖ *
            (‖(2 * Real.pi * Complex.I) ^ n‖ * ‖(Real.fourierChar (ω * x) : ℂ)‖) := by
              rw [norm_mul]
      _ = ‖((ω : ℂ) ^ n)‖ * ‖(2 * Real.pi * Complex.I) ^ n‖ := by
              simp
      _ ≤ (‖((ω : ℂ) ^ n)‖ * ‖(2 * Real.pi * Complex.I) ^ n‖) * (1 + ‖x‖) ^ 0 := by
              simp

/-- Modulation on Schwartz space, matching `modulate` on underlying functions. -/
def modulateSchwartz (ω : ℝ) : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun t : ℝ ↦ (Real.fourierChar (ω * t) : ℂ))

@[simp] theorem modulateSchwartz_apply (ω : ℝ) (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    modulateSchwartz ω f t = (Real.fourierChar (ω * t) : ℂ) * f t := by
  simpa [modulateSchwartz] using
    (SchwartzMap.smulLeftCLM_apply_apply
      (F := ℂ)
      (g := fun s : ℝ ↦ (Real.fourierChar (ω * s) : ℂ))
      (hg := fourierChar_mul_hasTemperateGrowth ω)
      f t)

theorem coe_modulateSchwartz (ω : ℝ) (f : SchwartzMap ℝ ℂ) :
    (modulateSchwartz ω f : ℝ → ℂ) = modulate ω f := by
  funext t
  simp [modulate]

/-- L² Fourier commutes with translation up to modulation, stated on `Lp` representatives. -/
theorem l2Fourier_translate_lp (x : ℝ) (hf : MemLp f 2 volume) :
    FourierTransform.fourier (translateLp x (hf.toLp f)) =
      modulateLp (-x) (FourierTransform.fourier (hf.toLp f)) := by
  set P : MeasureTheory.Lp (α := ℝ) ℂ 2 volume → Prop :=
    fun g ↦ FourierTransform.fourier (translateLp x g) =
      modulateLp (-x) (FourierTransform.fourier g)
  refine DenseRange.induction_on (p := P)
    (SchwartzMap.denseRange_toLpCLM (p := (2 : ENNReal)) ENNReal.ofNat_ne_top) (hf.toLp f) ?_ ?_
  · apply isClosed_eq
    · exact FourierTransform.continuous_fourier.comp (translateLp x).continuous
    · exact (modulateLpCLM (-x)).continuous.comp FourierTransform.continuous_fourier
  intro s
  have htranslate :
      FourierTransform.fourier (translateLp x (s.toLp 2 volume)) =
        (FourierTransform.fourier (s.compSubConstCLM ℂ x)).toLp 2 volume := by
    calc
      FourierTransform.fourier (translateLp x (s.toLp 2 volume))
          = FourierTransform.fourier ((s.compSubConstCLM ℂ x).toLp 2 volume) := by
              exact congrArg FourierTransform.fourier <|
                by simpa [translate, SchwartzMap.compSubConstCLM_apply] using
                  (translateLp_toLp (f := s) x (s.memLp 2 volume))
      _ = (FourierTransform.fourier (s.compSubConstCLM ℂ x)).toLp 2 volume := by
              exact SchwartzMap.toLp_fourier_eq (f := s.compSubConstCLM ℂ x)
  have hFourier :
      (FourierTransform.fourier (s.compSubConstCLM ℂ x)).toLp 2 volume =
        (modulate_memLp (-x) ((FourierTransform.fourier s).memLp 2 volume)).toLp
          (modulate (-x) (FourierTransform.fourier s)) := by
    exact MemLp.toLp_congr
      ((FourierTransform.fourier (s.compSubConstCLM ℂ x)).memLp 2 volume)
      (modulate_memLp (-x) ((FourierTransform.fourier s).memLp 2 volume))
      (Filter.Eventually.of_forall
        (congrFun (fourier_compSubConstCLM_eq_modulate (f := s) x)))
  have hmodulate :
      modulateLp (-x) (FourierTransform.fourier (s.toLp 2 volume)) =
        (modulate_memLp (-x) ((FourierTransform.fourier s).memLp 2 volume)).toLp
          (modulate (-x) (FourierTransform.fourier s)) := by
    calc
      modulateLp (-x) (FourierTransform.fourier (s.toLp 2 volume))
          = modulateLp (-x) ((FourierTransform.fourier s).toLp 2 volume) := by
            congr 1
            rw [SchwartzMap.toLp_fourier_eq (f := s)]
      _ = (modulate_memLp (-x) ((FourierTransform.fourier s).memLp 2 volume)).toLp
            (modulate (-x) (FourierTransform.fourier s)) := by
            exact modulateLp_toLp (-x) (f := FourierTransform.fourier s)
              (hf := (FourierTransform.fourier s).memLp 2 volume)
  exact htranslate.trans (hFourier.trans hmodulate.symm)

/-- L² Fourier commutes with modulation up to translation, stated on `Lp` representatives. -/
theorem l2Fourier_modulate_lp (ω : ℝ) (hf : MemLp f 2 volume) :
    FourierTransform.fourier (modulateLp ω (hf.toLp f)) =
      translateLp ω (FourierTransform.fourier (hf.toLp f)) := by
  let P : MeasureTheory.Lp (α := ℝ) ℂ 2 volume → Prop :=
    fun g ↦ FourierTransform.fourier (modulateLp ω g) =
      translateLp ω (FourierTransform.fourier g)
  refine DenseRange.induction_on (p := P)
    (SchwartzMap.denseRange_toLpCLM (p := (2 : ENNReal)) ENNReal.ofNat_ne_top) (hf.toLp f) ?_ ?_
  · apply isClosed_eq
    · exact FourierTransform.continuous_fourier.comp (modulateLpCLM ω).continuous
    · exact (translateLp ω).continuous.comp FourierTransform.continuous_fourier
  intro s
  have htemp : (fun t : ℝ ↦ (Real.fourierChar (ω * t) : ℂ)).HasTemperateGrowth :=
    fourierChar_mul_hasTemperateGrowth ω
  let smod : SchwartzMap ℝ ℂ :=
    SchwartzMap.smulLeftCLM ℂ (fun t : ℝ ↦ (Real.fourierChar (ω * t) : ℂ)) s
  have hsmod_toLp :
      (modulate_memLp ω (s.memLp 2 volume)).toLp (modulate ω s) = smod.toLp 2 volume := by
    exact MemLp.toLp_congr
      (modulate_memLp ω (s.memLp 2 volume))
      (smod.memLp 2 volume)
      (Filter.Eventually.of_forall fun t ↦ by
        simp [smod, modulate, SchwartzMap.smulLeftCLM_apply htemp])
  have hmod :
      FourierTransform.fourier (modulateLp ω (s.toLp 2 volume)) =
        FourierTransform.fourier (smod.toLp 2 volume) := by
    calc
      FourierTransform.fourier (modulateLp ω (s.toLp 2 volume))
          = FourierTransform.fourier
              ((modulate_memLp ω (s.memLp 2 volume)).toLp (modulate ω s)) := by
              congr 1
              exact modulateLp_toLp ω (f := s) (hf := s.memLp 2 volume)
      _ = FourierTransform.fourier (smod.toLp 2 volume) := by
              exact congrArg FourierTransform.fourier hsmod_toLp
  have hfourier_smod :
      FourierTransform.fourier smod = translate ω (FourierTransform.fourier s) := by
    have hsmod_fun : (smod : ℝ → ℂ) = fun t ↦ (Real.fourierChar (ω * t) : ℂ) * s t := by
      funext t
      simp [smod, SchwartzMap.smulLeftCLM_apply htemp]
    calc
      FourierTransform.fourier smod =
          FourierTransform.fourier
            (fun t ↦ (Real.fourierChar (ω * t) : ℂ) * s t) := by
        simpa using congrArg FourierTransform.fourier hsmod_fun
      _ = translate ω (FourierTransform.fourier s) := fourier_modulate_eq_translate (f := s) ω
  have hsmod :
      FourierTransform.fourier (smod.toLp 2 volume) =
        (translate_memLp ω ((FourierTransform.fourier s).memLp 2 volume)).toLp
          (translate ω (FourierTransform.fourier s)) := by
    calc
      FourierTransform.fourier (smod.toLp 2 volume)
          = (FourierTransform.fourier smod).toLp 2 volume := by
              exact SchwartzMap.toLp_fourier_eq (f := smod)
      _ = (translate_memLp ω ((FourierTransform.fourier s).memLp 2 volume)).toLp
            (translate ω (FourierTransform.fourier s)) := by
              exact MemLp.toLp_congr
                ((FourierTransform.fourier smod).memLp 2 volume)
                (translate_memLp ω ((FourierTransform.fourier s).memLp 2 volume))
                (Filter.Eventually.of_forall (congrFun hfourier_smod))
  have htranslate :
      translateLp ω (FourierTransform.fourier (s.toLp 2 volume)) =
        (translate_memLp ω ((FourierTransform.fourier s).memLp 2 volume)).toLp
          (translate ω (FourierTransform.fourier s)) := by
    calc
      translateLp ω (FourierTransform.fourier (s.toLp 2 volume))
          = translateLp ω ((FourierTransform.fourier s).toLp 2 volume) := by
              congr 1
              rw [SchwartzMap.toLp_fourier_eq (f := s)]
      _ = (translate_memLp ω ((FourierTransform.fourier s).memLp 2 volume)).toLp
            (translate ω (FourierTransform.fourier s)) := by
              exact translateLp_toLp (f := FourierTransform.fourier s) ω
                (hf := (FourierTransform.fourier s).memLp 2 volume)
  exact hmod.trans (hsmod.trans htranslate.symm)

private theorem toLp_memLp_eq_self (g : MeasureTheory.Lp (α := ℝ) ℂ 2 volume) :
    ((MeasureTheory.Lp.memLp g).toLp (g : ℝ → ℂ)) = g := by
  apply MeasureTheory.Lp.ext
  exact (MeasureTheory.Lp.memLp g).coeFn_toLp

theorem continuous_translateLp_apply :
    Continuous
      (fun q : ℝ × MeasureTheory.Lp (α := ℝ) ℂ 2 volume ↦ translateLp q.1 q.2) := by
  let τ : ℝ → C(ℝ, ℝ) := fun x ↦ ⟨fun t ↦ t - x, by continuity⟩
  have hτ : Continuous τ := by
    refine ContinuousMap.continuous_of_continuous_uncurry τ ?_
    simpa [τ, Function.uncurry] using (by continuity : Continuous fun p : ℝ × ℝ ↦ p.2 - p.1)
  have hmp : ∀ x, MeasurePreserving (τ x) volume volume := by
    intro x
    simpa [τ] using (MeasureTheory.measurePreserving_sub_right volume x)
  simpa [translateLp, τ] using
    (continuous_snd.compMeasurePreservingLp
      (μ := volume) (ν := volume) (E := ℂ) (p := (2 : ENNReal))
      (g := fun q : ℝ × MeasureTheory.Lp (α := ℝ) ℂ 2 volume ↦ τ q.1)
      (hτ.comp continuous_fst) (fun q ↦ hmp q.1) ENNReal.ofNat_ne_top)

theorem continuous_translateLp (g : MeasureTheory.Lp (α := ℝ) ℂ 2 volume) :
    Continuous fun x : ℝ ↦ translateLp x g := by
  simpa using
    (continuous_translateLp_apply.comp
      ((continuous_id : Continuous fun x : ℝ ↦ x).prodMk continuous_const))

theorem fourier_modulateLp_eq_translateLp (ω : ℝ)
    (g : MeasureTheory.Lp (α := ℝ) ℂ 2 volume) :
    FourierTransform.fourier (modulateLp ω g) = translateLp ω (FourierTransform.fourier g) := by
  simpa [toLp_memLp_eq_self g] using
    (l2Fourier_modulate_lp (f := (g : ℝ → ℂ)) (ω := ω) (hf := MeasureTheory.Lp.memLp g))

theorem modulateLp_eq_fourierInv_translateLp_fourier (ω : ℝ)
    (g : MeasureTheory.Lp (α := ℝ) ℂ 2 volume) :
    modulateLp ω g = FourierTransform.fourierInv (translateLp ω (FourierTransform.fourier g)) := by
  simpa using
    congrArg FourierTransform.fourierInv (fourier_modulateLp_eq_translateLp (ω := ω) g)

theorem continuous_modulateLp_apply :
    Continuous
      (fun q : ℝ × MeasureTheory.Lp (α := ℝ) ℂ 2 volume ↦ modulateLp q.1 q.2) := by
  have htranslate :
      Continuous
        (fun q : ℝ × MeasureTheory.Lp (α := ℝ) ℂ 2 volume ↦
          translateLp q.1 (FourierTransform.fourier q.2)) := by
    simpa using
      (continuous_translateLp_apply.comp
        (continuous_fst.prodMk (FourierTransform.continuous_fourier.comp continuous_snd)))
  simpa [modulateLp_eq_fourierInv_translateLp_fourier] using
    (FourierTransform.continuous_fourierInv.comp htranslate)

theorem continuous_modulateLp (g : MeasureTheory.Lp (α := ℝ) ℂ 2 volume) :
    Continuous fun ω : ℝ ↦ modulateLp ω g := by
  simpa using
    (continuous_modulateLp_apply.comp
      ((continuous_id : Continuous fun ω : ℝ ↦ ω).prodMk continuous_const))

end

end AmbiguityZeros.ToMathlib
