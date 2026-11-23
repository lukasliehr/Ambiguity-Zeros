module

public import LeanCode.Analysis.FourierUniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

public section

/-! Compact-support uncertainty for finite-dimensional real inner product spaces. -/

noncomputable section

open MeasureTheory Filter Complex
open scoped FourierTransform RealInnerProductSpace Topology

namespace AmbiguityHoles.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem frequently_zero_of_vanishing_on_real_interval (F : ℂ → ℂ)
    (a b : ℝ) (hab : a < b) (h : ∀ x : ℝ, x ∈ Set.Ioo a b → F (x : ℂ) = 0) :
    ∃ᶠ z in nhdsWithin ((((a + b) / 2 : ℝ) : ℂ))
      ({(((a + b) / 2 : ℝ) : ℂ)}ᶜ), F z = 0 := by
  rw [Filter.frequently_iff]
  intro U hU
  rcases Metric.mem_nhdsWithin_iff.mp hU with ⟨ε, εpos, hU⟩
  let r : ℝ := min (ε / 2) ((b - a) / 4)
  have hr0 : 0 < r := by
    dsimp [r]
    have h1 : 0 < ε / 2 := by linarith
    have h2 : 0 < (b - a) / 4 := by nlinarith
    exact lt_min h1 h2
  have hrle : r ≤ (b - a) / 4 := by
    dsimp [r]
    exact min_le_right _ _
  have hrlt : r < (b - a) / 2 := by
    have hq : (b - a) / 4 < (b - a) / 2 := by
      nlinarith [hab]
    exact lt_of_le_of_lt hrle hq
  let x : ℝ := (a + b) / 2 + r
  have hxIoo : x ∈ Set.Ioo a b := by
    dsimp [x]
    constructor <;> nlinarith
  have hxball : ((x : ℂ)) ∈ Metric.ball (((a + b) / 2 : ℂ)) ε := by
    rw [Metric.mem_ball]
    dsimp [x]
    have hrε : r < ε := by
      have hrleε : r ≤ ε / 2 := by
        dsimp [r]
        exact min_le_left _ _
      linarith
    simpa only [ofReal_add, ofReal_div, ofReal_ofNat, dist_self_add_left, norm_real,
      Real.norm_eq_abs, abs_of_pos hr0] using hrε
  have hxne : ((x : ℂ)) ≠ (((a + b) / 2 : ℂ)) := by
    intro hx
    have hxreal : (a + b) / 2 + r = (a + b) / 2 := by
      have hRe := congrArg Complex.re hx
      simpa [x] using hRe
    linarith
  have hxU : ((x : ℂ)) ∈ U := hU (by simpa using ⟨hxball, hxne⟩)
  exact ⟨(x : ℂ), hxU, h x hxIoo⟩

private theorem entire_eq_zero_of_vanishing_on_real_interval (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F Set.univ) (a b : ℝ) (hab : a < b)
    (h : ∀ x : ℝ, x ∈ Set.Ioo a b → F (x : ℂ) = 0) :
    F = 0 := by
  have hfreq := frequently_zero_of_vanishing_on_real_interval F a b hab h
  have hEqOn : Set.EqOn F 0 Set.univ :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero hF
      (by simpa using (isPreconnected_univ : IsPreconnected (Set.univ : Set ℂ)))
      (by simp) hfreq
  funext z
  exact hEqOn (by simp)

private theorem analyticOnNhd_exp_integral {f : E → ℂ} (hf : Integrable f)
    {a : E → ℂ} (ha : Continuous a) {C : ℝ}
    (hbound : ∀ᵐ t ∂volume, C < ‖a t‖ → f t = 0) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ ∫ t, Complex.exp (z * a t) * f t) Set.univ := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  intro z _
  let F (w : ℂ) (t : E) := Complex.exp (w * a t) * f t
  let F' (w : ℂ) (t : E) := (Complex.exp (w * a t) * a t) * f t
  let M := Real.exp ((‖z‖ + 1) * C)
  have hExp {w : ℂ} {t : E} (hw : ‖w‖ ≤ ‖z‖ + 1) (ht : ‖a t‖ ≤ C) :
      ‖Complex.exp (w * a t)‖ ≤ M := by
    rw [Complex.norm_exp, Real.exp_le_exp]
    calc
      (w * a t).re ≤ ‖w * a t‖ := Complex.re_le_norm _
      _ = ‖w‖ * ‖a t‖ := norm_mul _ _
      _ ≤ (‖z‖ + 1) * C := by gcongr
  have hmeas (w : ℂ) : AEStronglyMeasurable (F w) volume := by fun_prop
  have hInt : Integrable (F z) := by
    refine (hf.norm.const_mul M).mono' (hmeas z) ?_
    filter_upwards [hbound] with t ht
    by_cases h : ‖a t‖ ≤ C
    · rw [show ‖F z t‖ = ‖Complex.exp (z * a t)‖ * ‖f t‖ by simp [F]]
      exact mul_le_mul_of_nonneg_right (hExp (by linarith) h) (norm_nonneg _)
    · simp [F, ht (lt_of_not_ge h)]
  have hDerivMeas : AEStronglyMeasurable (F' z) volume := by fun_prop
  have hDerivBound : ∀ᵐ t ∂volume, ∀ w ∈ Metric.ball z 1,
      ‖F' w t‖ ≤ (M * C) * ‖f t‖ := by
    filter_upwards [hbound] with t ht w hw
    by_cases h : ‖a t‖ ≤ C
    · have hw' : ‖w‖ ≤ ‖z‖ + 1 := calc
        ‖w‖ = ‖z + (w - z)‖ := by congr 1; abel
        _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + 1 := by exact le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hw)
      rw [show ‖F' w t‖ = ‖Complex.exp (w * a t)‖ * ‖a t‖ * ‖f t‖ by simp [F']]
      gcongr
      exact hExp hw' h
    · simp [F', ht (lt_of_not_ge h)]
  have hDiff : ∀ᵐ t ∂volume, ∀ w ∈ Metric.ball z 1, HasDerivAt (fun w ↦ F w t) (F' w t) w :=
    ae_of_all _ fun t w _ ↦ by
      simpa [F, F'] using (((hasDerivAt_id w).mul_const (a t)).cexp.mul_const (f t))
  exact ((hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z zero_lt_one) (Eventually.of_forall hmeas) hInt hDerivMeas
    hDerivBound (hf.norm.const_mul (M * C)) hDiff).2).differentiableAt.differentiableWithinAt

private theorem fourier_eq_zero_of_aeBoundedSupport_of_eqOn_open
    {f : E → ℂ} (hf : Integrable f) {R : ℝ}
    (hs : ∀ᵐ t ∂volume, R < ‖t‖ → f t = 0)
    {U : Set E} (hU : IsOpen U) {p : E} (hp : p ∈ U) (hzero : Set.EqOn (𝓕 f) 0 U) :
    𝓕 f = 0 := by
  funext q
  let c (v t : E) : ℂ := (↑(-2 * Real.pi * ⟪t, v⟫) : ℂ) * I
  let g (t : E) := Complex.exp (c p t) * f t
  let H (z : ℂ) := ∫ t, Complex.exp (z * c (q - p) t) * g t
  have hc (v : E) : Continuous (c v) := by dsimp [c]; fun_prop
  have hg : Integrable g := by
    apply hf.norm.mono' (by dsimp [g]; fun_prop)
    exact ae_of_all _ fun t ↦ by simp [g, c, Complex.norm_exp]
  have hH : AnalyticOnNhd ℂ H Set.univ := by
    let C := (2 * Real.pi) * max R 0 * ‖q - p‖
    apply analyticOnNhd_exp_integral hg (hc (q - p)) (C := C)
    filter_upwards [hs] with t ht h
    have hR : R < ‖t‖ := by
      by_contra! hle
      apply not_lt_of_ge _ h
      calc
        ‖c (q - p) t‖ = (2 * Real.pi) * |⟪t, q - p⟫| := by
          simp [c, abs_of_pos Real.pi_pos]
        _ ≤ (2 * Real.pi) * (‖t‖ * ‖q - p‖) := by
          gcongr
          exact abs_real_inner_le_norm _ _
        _ ≤ C := by
          have hn : ‖t‖ ≤ max R 0 := hle.trans (le_max_left _ _)
          dsimp [C]
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hn (norm_nonneg (q - p)))
            (show (0 : ℝ) ≤ 2 * Real.pi from mul_nonneg (by norm_num) Real.pi_pos.le)
    simp [g, ht hR]
  have hreal (r : ℝ) : H (r : ℂ) = 𝓕 f (p + r • (q - p)) := by
    rw [Real.fourier_eq']
    apply integral_congr_ae
    exact ae_of_all _ fun t ↦ by
      simp only [g, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
      congr 2
      simp only [c, inner_add_right, real_inner_smul_right, ofReal_mul, ofReal_add, ofReal_neg,
        ofReal_ofNat]
      ring
  have hnear : ∀ᶠ r : ℝ in 𝓝 0, p + r • (q - p) ∈ U := by
    have hcont : Continuous (fun r : ℝ ↦ p + r • (q - p)) := by fun_prop
    exact hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simpa using hp))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hHzero : H = 0 := by
    apply entire_eq_zero_of_vanishing_on_real_interval
      H hH (-ε) ε (by linarith)
    intro r hr
    rw [hreal]
    apply hzero
    apply hεsub
    simpa [Metric.mem_ball, Real.dist_eq, abs_lt] using hr
  simpa using (hreal 1).symm.trans (congrFun hHzero 1)

/-- An integrable function and its Fourier transform cannot both have bounded essential
support on a nontrivial finite-dimensional real inner product space. -/
theorem ae_eq_zero_of_aeBoundedSupport_fourier [Nontrivial E]
    (f : E → ℂ) (hf : Integrable f)
    (hs : ∃ R : ℝ, ∀ᵐ t ∂volume, R < ‖t‖ → f t = 0)
    (hFs : ∃ R : ℝ, ∀ᵐ t ∂volume, R < ‖t‖ → 𝓕 f t = 0) :
    f =ᵐ[volume] 0 := by
  obtain ⟨R, hR⟩ := hs
  obtain ⟨S, hS⟩ := hFs
  let U : Set E := {t | S < ‖t‖}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  obtain ⟨p, hp⟩ := NormedSpace.exists_lt_norm ℝ E S
  have hzero : Set.EqOn (𝓕 f) 0 U := by
    apply Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).mpr hS) hU
    · exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hf).continuousOn
    · exact continuous_zero.continuousOn
  exact integrable_fourier_eq_zero_ae f hf
    (fourier_eq_zero_of_aeBoundedSupport_of_eqOn_open hf hR hU hp hzero)

end AmbiguityHoles.Analysis
