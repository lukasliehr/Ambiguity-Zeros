module

public import LeanCode.Analysis.FourierAgreement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

public section

/-! The Fourier transform of the spectrogram, via Plancherel on its slices. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace AmbiguityHoles.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private def phase (a : ℝ) : ℂ := Real.fourierChar a

private theorem phase_add (a b : ℝ) : phase (a + b) = phase a * phase b := by
  exact congrArg (fun z : Circle ↦ (z : ℂ)) (Real.fourierChar.map_add_eq_mul a b)

@[simp] private theorem norm_phase (a : ℝ) : ‖phase a‖ = 1 :=
  Circle.norm_coe _

@[simp] private theorem star_phase (a : ℝ) : star (phase a) = phase (-a) := by
  unfold phase
  rw [Real.fourierChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj _).symm

@[fun_prop] private theorem continuous_phase : Continuous phase := by
  unfold phase
  fun_prop

private theorem translate_memLp' {s : E → ℂ} {p : ENNReal} (h : MemLp s p volume) (x : E) :
    MemLp (fun t ↦ s (t - x)) p volume :=
  h.comp_measurePreserving (measurePreserving_sub_right volume x)

private theorem conj_memLp' {s : E → ℂ} {p : ENNReal} (h : MemLp s p volume) :
    MemLp (fun t ↦ star (s t)) p volume :=
  h.star

private theorem fourier_shift (s : E → ℂ) (x η : E) :
    𝓕 (fun t ↦ s (t + x)) η = phase (inner ℝ x η) * 𝓕 s η := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
    (volume : Measure E) (innerₗ E) s x) η
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ E) (fun t ↦ s (t + x)) η =
    phase (inner ℝ x η) * VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ E) s η
  simpa [phase, Function.comp_def, innerₗ_apply_apply, Circle.smul_def] using h

private def slice (w f : E → ℂ) (y : E) : E → ℂ := fun t ↦ f t * star (w (t - y))

private theorem slice_integrable {w f : E → ℂ} (hw : MemLp w 2 volume)
    (hf : MemLp f 2 volume) (y : E) : Integrable (slice w f y) := by
  exact hf.integrable_mul (conj_memLp' (translate_memLp' hw y))

private theorem stft_eq_fourier_slice (w f : E → ℂ) (y η : E) :
    stft w f y η = 𝓕 (slice w f y) η := by
  simp [stft, Real.fourier_eq, slice, Circle.smul_def, real_inner_comm η,
    mul_comm, mul_assoc]

private theorem integrable_skew_mul {R : Type*} [NormedRing R] {f g : E → R}
    (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun p : E × E ↦ f p.1 * g (p.1 - p.2)) (volume.prod volume) := by
  have hs : MeasurePreserving (fun p : E × E ↦ (p.1, p.1 - p.2))
      (volume.prod volume) (volume.prod volume) := by
    have h := ((MeasurePreserving.id (volume : Measure E)).prod
      ((volume : Measure E).measurePreserving_neg)).comp
        (measurePreserving_prod_sub (volume : Measure E) volume)
    simpa [Function.comp_def] using h
  exact hs.integrable_comp_of_integrable (hf.mul_prod hg)

private theorem slice_memLp_ae {w f : E → ℂ} (hw : MemLp w 2 volume)
    (hf : MemLp f 2 volume) : ∀ᵐ y : E ∂volume, MemLp (slice w f y) 2 volume := by
  have hf2 : Integrable (fun t ↦ ‖f t‖ ^ 2) volume := hf.integrable_norm_pow (by decide)
  have hw2 : Integrable (fun t ↦ ‖w t‖ ^ 2) volume := hw.integrable_norm_pow (by decide)
  filter_upwards [(integrable_skew_mul hf2 hw2).prod_left_ae] with y hy
  have hm := (slice_integrable hw hf y).aestronglyMeasurable
  rw [← memLp_norm_iff hm]
  apply (memLp_two_iff_integrable_sq hm.norm).2
  simpa [slice, norm_mul, mul_pow] using hy


private def corr (f : E → ℂ) (x : E) (t : E) : ℂ :=
  f (t + (1 / 2 : ℝ) • x) * star (f (t - (1 / 2 : ℝ) • x))

private theorem corr_integrable {f : E → ℂ} (hf : MemLp f 2 volume) (x : E) :
    Integrable (corr f x) := by
  have h := (translate_memLp' hf (-((1 / 2 : ℝ) • x))).integrable_mul
    (conj_memLp' (translate_memLp' hf ((1 / 2 : ℝ) • x)))
  refine h.congr (Filter.Eventually.of_forall fun t ↦ ?_)
  simp only [corr, Pi.mul_apply, sub_neg_eq_add]

private theorem star_corr_integrable {f : E → ℂ} (hf : MemLp f 2 volume) (x : E) :
    Integrable (fun t ↦ star (corr f x t)) := by
  have h := corr_integrable hf x
  exact h.mono h.aestronglyMeasurable.star (ae_of_all _ fun t ↦ by simp)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem skew_inner (t y ω : E) :
    -(inner ℝ ω y) = -(inner ℝ ω t) + inner ℝ ω (t - y) := by
  rw [inner_sub_right]
  ring

private theorem integral_corr_slice_product {w f : E → ℂ} (hw : MemLp w 2 volume)
    (hf : MemLp f 2 volume) (x ω : E) :
    (∫ y, phase (-(inner ℝ ω y)) * ∫ t, corr (slice w f y) x t) =
      ambiguity f x ω * star (ambiguity w x ω) := by
  let A : E → ℂ := fun t ↦ corr f x t * phase (-(inner ℝ ω t))
  let B : E → ℂ := fun t ↦ star (corr w x t) * phase (inner ℝ ω t)
  have hA : Integrable A := by
    exact (corr_integrable hf x).mul_bdd (c := 1) (by fun_prop) (ae_of_all _ fun _ ↦ by simp)
  have hB : Integrable B := by
    exact (star_corr_integrable hw x).mul_bdd (c := 1) (by fun_prop) (ae_of_all _ fun _ ↦ by simp)
  have hpoint (t y : E) :
      phase (-(inner ℝ ω y)) * corr (slice w f y) x t = A t * B (t - y) := by
    rw [skew_inner t y ω, phase_add]
    have hplus : t + (1 / 2 : ℝ) • x - y = t - y + (1 / 2 : ℝ) • x := by abel
    have hminus : t - (1 / 2 : ℝ) • x - y = t - y - (1 / 2 : ℝ) • x := by abel
    simp only [corr, slice, star_mul, star_star, A, B, hplus, hminus]
    ring
  have hBint (t : E) : ∫ y, B (t - y) = ∫ y, B y := by
    simpa only [Function.comp_apply, sub_eq_add_neg] using
      (integral_neg_eq_self (μ := (volume : Measure E)) (f := fun y ↦ B (t + y))).trans
        (by simpa only [add_comm] using
          (integral_add_right_eq_self (μ := (volume : Measure E)) B t))
  calc
    _ = ∫ y, ∫ t, A t * B (t - y) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
      exact (integral_const_mul (μ := (volume : Measure E)) (phase (-(inner ℝ ω y)))
        (corr (slice w f y) x)).symm.trans
          (integral_congr_ae (Filter.Eventually.of_forall fun t ↦ hpoint t y))
    _ = ∫ t, ∫ y, A t * B (t - y) := by
      exact integral_integral_swap (integrable_skew_mul hA hB).swap
    _ = ∫ t, A t * (∫ y, B y) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
      exact (integral_const_mul (μ := (volume : Measure E)) (A t) (fun y ↦ B (t - y))).trans
        (congrArg (fun z ↦ A t * z) (hBint t))
    _ = (∫ t, A t) * ∫ y, B y := integral_mul_const _ _
    _ = _ := by
      have hBconj : (∫ y, B y) = star (ambiguity w x ω) := by
        refine Eq.trans ?_ (integral_conj (f := fun t ↦ corr w x t * phase (-(inner ℝ ω t))))
        apply integral_congr_ae
        filter_upwards with y
        change B y = star (corr w x y * phase (-(inner ℝ ω y)))
        simp only [B, star_mul, star_phase, neg_neg, mul_comm]
      rw [hBconj]
      rfl

private theorem integral_corr_eq_spectral {s : E → ℂ} (h1 : Integrable s)
    (h2 : MemLp s 2 volume) (x : E) :
    (∫ t, corr s x t) = ∫ η, phase (inner ℝ x η) * (‖𝓕 s η‖ ^ 2 : ℝ) := by
  let a : E := (1 / 2 : ℝ) • x
  let splus : E → ℂ := fun t ↦ s (t + a)
  let sminus : E → ℂ := fun t ↦ s (t - a)
  have hp := measurePreserving_add_right (volume : Measure E) a
  have hm := measurePreserving_sub_right (volume : Measure E) a
  have hp₁ : Integrable splus := hp.integrable_comp_of_integrable h1
  have hm₁ : Integrable sminus := hm.integrable_comp_of_integrable h1
  have hp₂ : MemLp splus 2 volume := h2.comp_measurePreserving hp
  have hm₂ : MemLp sminus 2 volume := h2.comp_measurePreserving hm
  calc
    _ = inner ℂ (hm₂.toLp sminus) (hp₂.toLp splus) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hm₂.coeFn_toLp, hp₂.coeFn_toLp] with t htminus htplus
      rw [RCLike.inner_apply, htminus, htplus]
      rfl
    _ = inner ℂ (𝓕 (hm₂.toLp sminus)) (𝓕 (hp₂.toLp splus)) :=
      (Lp.inner_fourier_eq (f := hm₂.toLp sminus) (g := hp₂.toLp splus)).symm
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [fourier_toLp_ae hm₁ hm₂, fourier_toLp_ae hp₁ hp₂] with η hηminus hηplus
      rw [RCLike.inner_apply, hηminus, hηplus]
      have hminus : sminus = fun t ↦ s (t + -a) := by simp [sminus, sub_eq_add_neg]
      have hplus : splus = fun t ↦ s (t + a) := rfl
      rw [hminus, hplus, fourier_shift, fourier_shift]
      simp only [starRingEnd_apply, star_mul, star_phase, inner_neg_left, neg_neg]
      calc
        _ = phase (inner ℝ a η + inner ℝ a η) *
            ((𝓕 s η) * star (𝓕 s η)) := by rw [phase_add]; ring
        _ = _ := by
          rw [← inner_add_left, show a + a = x by dsimp [a]; rw [← add_smul]; norm_num]
          simpa only [starRingEnd_apply, Complex.ofReal_pow] using
            congrArg (fun z ↦ phase (inner ℝ x η) * z) (Complex.mul_conj' (𝓕 s η))

/-- Equal spectrogram magnitudes determine the product of each ambiguity with
the conjugate window ambiguity. -/
theorem ambiguity_product_eq_of_stft_norm_eq {w f g : E → ℂ} (hw : MemLp w 2 volume)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (heq : ∀ y η, ‖stft w f y η‖ = ‖stft w g y η‖) (x ω : E) :
    ambiguity f x ω * star (ambiguity w x ω) =
      ambiguity g x ω * star (ambiguity w x ω) := by
  rw [← integral_corr_slice_product hw hf, ← integral_corr_slice_product hw hg]
  apply integral_congr_ae
  filter_upwards [slice_memLp_ae hw hf, slice_memLp_ae hw hg] with y hyf hyg
  rw [integral_corr_eq_spectral (slice_integrable hw hf y) hyf x,
    integral_corr_eq_spectral (slice_integrable hw hg y) hyg x]
  simp_rw [← stft_eq_fourier_slice, heq y]

end AmbiguityHoles.Analysis
