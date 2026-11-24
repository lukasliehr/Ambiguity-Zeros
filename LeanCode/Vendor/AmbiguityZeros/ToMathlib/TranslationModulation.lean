module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

@[expose] public section

namespace AmbiguityZeros.ToMathlib

noncomputable section

open MeasureTheory

variable {p : ENNReal} {f g u v : ℝ → ℂ}

def translate (x : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t ↦ f (t - x)

def modulate (ω : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t ↦ (Real.fourierChar (ω * t) : ℂ) * f t

/- Translation on Schwartz space, matching `translate` on underlying functions. -/
/- Complex conjugation on Schwartz space, viewed as a real-linear map. -/
theorem translate_aestronglyMeasurable (x : ℝ) (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (translate x f) volume := by
  exact hf.comp_measurePreserving (MeasureTheory.measurePreserving_sub_right volume x)

theorem modulate_aestronglyMeasurable (ω : ℝ) (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (modulate ω f) volume := by
  have hchar : AEStronglyMeasurable (fun t : ℝ => (Real.fourierChar (ω * t) : ℂ)) volume := by
    exact
      (by fun_prop : Measurable fun t : ℝ => (Real.fourierChar (ω * t) : ℂ)).aestronglyMeasurable
  exact hchar.mul hf

theorem translate_eLpNorm (x : ℝ) (hf : AEStronglyMeasurable f volume) :
    eLpNorm (translate x f) p volume = eLpNorm f p volume := by
  exact eLpNorm_comp_measurePreserving hf (MeasureTheory.measurePreserving_sub_right volume x)

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
      have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (f := modulate ω f) (g := f) (c := 1)
        (modulate_aestronglyMeasurable ω _hf) h₁ p
      simpa using h
    simpa [one_mul] using hle₁
  · have h₂ : ∀ᵐ t ∂volume, ‖f t‖ ≤ (1 : ℝ) * ‖modulate ω f t‖ := by
      refine Filter.Eventually.of_forall ?_
      intro t
      simp [modulate, hnorm t, mul_comm]
    have hle₂ : eLpNorm f p volume ≤ eLpNorm (modulate ω f) p volume := by
      have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (f := f) (g := modulate ω f) (c := 1)
        _hf h₂ p
      simpa using h
    simpa [one_mul] using hle₂

theorem translate_memLp (x : ℝ) (hf : MemLp f p volume) :
    MemLp (translate x f) p volume := by
  exact hf.comp_measurePreserving (MeasureTheory.measurePreserving_sub_right volume x)

theorem modulate_memLp (ω : ℝ) (hf : MemLp f p volume) :
    MemLp (modulate ω f) p volume := by
  rw [memLp_iff, modulate_eLpNorm ω hf.aestronglyMeasurable]
  exact hf.eLpNorm_lt_top

theorem conj_memLp (hf : MemLp f p volume) :
    MemLp (fun t ↦ star (f t)) p volume := by
  exact hf.star

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
  have htr : translate x f = f ∘ fun v => v + -x := by
    funext t
    simp [translate, sub_eq_add_neg]
  simpa [htr, modulate, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc, Circle.smul_def,
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

theorem integrable_mul_of_memLp (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun t ↦ f t * g t) volume := by
  have h : MemLp (fun t ↦ f t * g t) 1 volume := by
    exact hf.fun_mul hg
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

theorem fourierChar_memLp_top (ω : ℝ) :
    MemLp (fun t : ℝ ↦ (Real.fourierChar (ω * t) : ℂ)) (⊤ : ENNReal) volume := by
  have hcont : Continuous fun t : ℝ ↦ (Real.fourierChar (ω * t) : ℂ) := by
    continuity
  refine memLp_top_of_bound hcont.aestronglyMeasurable 1 ?_
  filter_upwards with t
  exact le_of_eq (norm_fourierChar (ω * t))

/-- Pointwise modulation on `L²`, using the canonical `Lp` representative. -/
def modulateLp (ω : ℝ) (g : MeasureTheory.Lp (α := ℝ) ℂ 2 volume) :
    MeasureTheory.Lp (α := ℝ) ℂ 2 volume :=
  ((fourierChar_memLp_top ω).fun_mul (MeasureTheory.Lp.memLp g)).toLp
    (fun t ↦ (Real.fourierChar (ω * t) : ℂ) * g t)

private theorem modulateLp_coeFn (ω : ℝ)
    (g : MeasureTheory.Lp (α := ℝ) ℂ 2 volume) :
    modulateLp ω g =ᵐ[volume] fun t ↦ (Real.fourierChar (ω * t) : ℂ) * g t := by
  simpa [modulateLp] using
    (MeasureTheory.MemLp.coeFn_toLp
      ((fourierChar_memLp_top ω).fun_mul (MeasureTheory.Lp.memLp g)))

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
    ((fourierChar_memLp_top ω).fun_mul (MeasureTheory.Lp.memLp (hf.toLp f)))
    (modulate_memLp ω hf) ?_
  filter_upwards [hf.coeFn_toLp] with t ht
  simp [modulate, ht]

/-- Bridge-ready Fourier intertwining on Schwartz functions: translation becomes modulation. -/
theorem fourier_compSubConstCLM_eq_modulate
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    FourierTransform.fourier (f.compSubConstCLM ℂ x) =
      modulate (-x) (FourierTransform.fourier f) := by
  have hcoe : (⇑(f.compSubConstCLM ℂ x) : ℝ → ℂ) = translate x f := by
    funext t
    simp [SchwartzMap.compSubConstCLM_apply, translate]
  simpa [hcoe, SchwartzMap.fourier_coe]
    using (fourierIntegral_translate (f := f) x f.integrable)

/-- Bridge-ready Fourier intertwining on Schwartz functions: modulation becomes translation. -/
theorem fourier_modulate_eq_translate
    (f : SchwartzMap ℝ ℂ) (ω : ℝ) :
    FourierTransform.fourier (fun t ↦ (Real.fourierChar (ω * t) : ℂ) * f t) =
      translate ω (FourierTransform.fourier f) := by
  exact fourierIntegral_modulate (f := f) ω f.integrable

private theorem contDiff_fourierChar_mul (n : WithTop ℕ∞) (ω : ℝ) :
    ContDiff ℝ n (fun t : ℝ ↦ (Real.fourierChar (ω * t) : ℂ)) := by
  have harg :
      ContDiff ℝ n (fun t : ℝ ↦ (((2 * Real.pi * (ω * t) : ℝ) : ℂ) * Complex.I)) := by
    exact (Complex.ofRealCLM.contDiff.comp
      (by fun_prop : ContDiff ℝ n fun t : ℝ ↦ 2 * Real.pi * (ω * t))).mul contDiff_const
  simpa [Real.fourierChar_apply, Function.comp_def] using Complex.contDiff_exp.comp harg

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
        exact (SchwartzMap.fourier_coe smod).trans (congrArg FourierTransform.fourier hsmod_fun)
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

end

end AmbiguityZeros.ToMathlib
