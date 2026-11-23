module

public import LeanCode.Local.TrainsGeometry
public import LeanCode.Local.SeparationAlgebra
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace AmbiguityHoles.Local
open Analysis

private theorem centered_integral (w ω : ℝ) :
    (∫ t in -(w / 2)..w / 2, (Real.fourierChar (-(ω * t)) : ℂ)) =
      (w * Real.sinc (Real.pi * ω * w) : ℝ) := by
  by_cases hω : ω = 0
  · simp [hω]
    change (w : ℂ) * 1 = (w : ℂ)
    exact mul_one _
  let c := -(2 * Real.pi * ω)
  have hc : c ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hω)
  have hchar (t : ℝ) : (Real.fourierChar (-(ω * t)) : ℂ) =
      Complex.exp (((c * t : ℝ) : ℂ) * Complex.I) := by
    rw [Real.fourierChar_apply]
    congr 2
    dsimp [c]
    ring
  simp_rw [hchar]
  rw [intervalIntegral.integral_comp_mul_left (f := fun t : ℝ ↦ Complex.exp ((t : ℂ) * Complex.I)) hc,
    mul_neg, integral_exp_mul_I_eq_sinc]
  have harg : c * (w / 2) = -(Real.pi * ω * w) := by dsimp [c]; ring
  have hs : Real.sinc (c * (w / 2)) = Real.sinc (Real.pi * ω * w) := by
    rw [harg, Real.sinc_neg]
  rw [hs]
  change ((c⁻¹ : ℝ) : ℂ) *
    (2 * ((c * (w / 2) : ℝ) : ℂ) * (Real.sinc (Real.pi * ω * w) : ℂ)) = _
  push_cast
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  field_simp [hc']

private theorem interval_kernel (L x ω : ℝ) :
    (∫ t : ℝ,
      (Icc (0 : ℝ) L).indicator (fun _ ↦ (1 : ℂ)) (t + (1/2 : ℝ)*x) *
      star ((Icc (0 : ℝ) L).indicator (fun _ ↦ (1 : ℂ)) (t - (1/2 : ℝ)*x)) *
      (Real.fourierChar (-(ω*t)) : ℂ)) =
    halfPhase (Real.pi * ω * L) * (intervalAmplitude L x ω : ℂ) := by
  have hmem (t : ℝ) :
      t + (1/2 : ℝ)*x ∈ Icc 0 L ∧ t - (1/2 : ℝ)*x ∈ Icc 0 L ↔
        t ∈ Icc (|x|/2) (L - |x|/2) := by
    rcases le_total 0 x with hx | hx
    · simp only [abs_of_nonneg hx, mem_Icc]
      constructor <;> intro h
      · exact ⟨by linarith [h.2.1], by linarith [h.1.2]⟩
      · exact ⟨⟨by linarith [h.1], by linarith [h.2]⟩,
          ⟨by linarith [h.1], by linarith [h.2]⟩⟩
    · simp only [abs_of_nonpos hx, mem_Icc]
      constructor <;> intro h
      · exact ⟨by linarith [h.1.1], by linarith [h.2.2]⟩
      · exact ⟨⟨by linarith [h.1], by linarith [h.2]⟩,
          ⟨by linarith [h.1], by linarith [h.2]⟩⟩
  have hfun :
      (fun t : ℝ ↦
        (Icc (0 : ℝ) L).indicator (fun _ ↦ (1 : ℂ)) (t + (1/2 : ℝ)*x) *
        star ((Icc (0 : ℝ) L).indicator (fun _ ↦ (1 : ℂ)) (t - (1/2 : ℝ)*x)) *
        (Real.fourierChar (-(ω*t)) : ℂ)) =
      (Icc (|x|/2) (L - |x|/2)).indicator (fun t ↦ (Real.fourierChar (-(ω*t)) : ℂ)) := by
    funext t
    by_cases hp : t + (1/2 : ℝ)*x ∈ Icc 0 L <;>
      by_cases hq : t - (1/2 : ℝ)*x ∈ Icc 0 L <;>
      simp only [indicator, hp, hq, ← hmem t, and_self, and_false, false_and,
        if_true, if_false, star_one, star_zero, zero_mul, mul_zero, one_mul]
  rw [hfun, integral_indicator measurableSet_Icc]
  by_cases hx : L ≤ |x|
  · rw [intervalAmplitude_eq_zero hx, Complex.ofReal_zero, mul_zero,
      integral_Icc_eq_integral_Ioc, Ioc_eq_empty (by linarith), Measure.restrict_empty]
    simp
  have hpos : 0 ≤ L - |x| := by linarith
  let w := L - |x|
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have hleft : -(w/2) + L/2 = |x|/2 := by dsimp [w]; ring
  have hright : w/2 + L/2 = L - |x|/2 := by dsimp [w]; ring
  have htranslate :
      (∫ t in |x|/2..L - |x|/2, (Real.fourierChar (-(ω*t)) : ℂ)) =
      ∫ t in -(w/2)..w/2, (Real.fourierChar (-(ω*(t + L/2))) : ℂ) := by
    simpa only [hleft, hright] using
      (intervalIntegral.integral_comp_add_right
        (f := fun t : ℝ ↦ (Real.fourierChar (-(ω*t)) : ℂ))
        (a := -(w/2)) (b := w/2) (L/2)).symm
  rw [htranslate]
  have hshift (t : ℝ) :
      (Real.fourierChar (-(ω * (t + L/2))) : ℂ) =
      halfPhase (Real.pi * ω * L) * (Real.fourierChar (-(ω*t)) : ℂ) := by
    rw [show -(ω * (t + L/2)) = -(ω * (L/2)) + -(ω*t) by ring, Real.fourierChar.map_add_eq_mul, Circle.coe_mul]
    congr 1
    rw [Real.fourierChar_apply, halfPhase]
    congr 1
    push_cast
    ring
  simp_rw [hshift]
  calc
    _ = halfPhase (Real.pi * ω * L) *
        (∫ t in -(w / 2)..w / 2, (Real.fourierChar (-(ω * t)) : ℂ)) :=
      intervalIntegral.integral_const_mul (μ := (volume : Measure ℝ)) _ _
    _ = _ := by rw [centered_integral w ω]; simp [intervalAmplitude, max_eq_right hpos, w]

theorem cubePulse_ambiguity {d : ℕ} (L : ℝ) (x ω : Coord d) :
    ambiguity (cubePulse L) x ω =
      ∏ i, halfPhase (Real.pi * ω i * L) * (intervalAmplitude L (x i) (ω i) : ℂ) := by
  rw [ambiguity, crossAmbiguity]
  let f (i : Fin d) (t : ℝ) : ℂ :=
    (Icc (0 : ℝ) L).indicator (fun _ ↦ (1 : ℂ)) (t + (1/2 : ℝ)*x i) *
      star ((Icc (0 : ℝ) L).indicator (fun _ ↦ (1 : ℂ)) (t - (1/2 : ℝ)*x i)) *
      (Real.fourierChar (-(ω i*t)) : ℂ)
  have hpulse (t : Coord d) :
      cubePulse L t = ∏ i, (Icc (0 : ℝ) L).indicator (fun _ ↦ (1 : ℂ)) (t i) := by
    classical
    by_cases ht : ∀ i, t i ∈ Icc (0 : ℝ) L
    · have ht' : t ∈ unitCube L := ht
      simp [cubePulse, ht', ht]
    · push Not at ht
      obtain ⟨i, hi⟩ := ht
      have ht' : t ∉ unitCube L := fun h ↦ hi (h i)
      rw [cubePulse, indicator_of_notMem ht', Finset.prod_eq_zero (Finset.mem_univ i)]
      exact indicator_of_notMem hi _
  have hchar (t : Coord d) :
      (Real.fourierChar (-(inner ℝ ω t)) : ℂ) =
        ∏ i, (Real.fourierChar (-(ω i*t i)) : ℂ) := by
    rw [PiLp.inner_apply, ← Finset.sum_neg_distrib]
    simp only [Real.fourierChar_apply, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul,
      Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    rw [show inner ℝ (ω i) (t i) = ω i * t i by
      change t i * ω i = ω i * t i
      exact mul_comm _ _]
  have hfun (t : Coord d) :
      cubePulse L (t + (1/2 : ℝ) • x) * star (cubePulse L (t - (1/2 : ℝ) • x)) *
        (Real.fourierChar (-(inner ℝ ω t)) : ℂ) = ∏ i, f i (t i) := by
    rw [hpulse, hpulse, hchar, star_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    rfl
  simp_rw [hfun]
  let e := MeasurableEquiv.toLp 2 (Fin d → ℝ)
  have he := PiLp.volume_preserving_toLp (ι := Fin d)
  rw [← he.integral_comp e.measurableEmbedding]
  change (∫ t : Fin d → ℝ, ∏ i, f i (t i)) = _
  exact (integral_fintype_prod_volume_eq_prod (E := fun _ : Fin d ↦ ℝ) f).trans
    (Finset.prod_congr rfl fun i _ ↦ interval_kernel L (x i) (ω i))

/-- At any frequency, a sufficiently short cube pulse has nonzero ambiguity
at zero delay. -/
theorem exists_small_cubePulse_ambiguity_ne_zero {d : ℕ}
    (ω : Coord d) {r : ℝ} (hr : 0 < r) :
    ∃ L : ℝ, 0 < L ∧ L < r ∧ ambiguity (cubePulse L) 0 ω ≠ 0 := by
  let L := min (r / 2) (1 / (‖ω‖ + 1))
  have hL : 0 < L := lt_min (by linarith) (by positivity)
  refine ⟨L, hL, (min_le_left _ _).trans_lt (by linarith), ?_⟩
  rw [cubePulse_ambiguity]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply mul_ne_zero (halfPhase_ne_zero _)
  apply Complex.ofReal_ne_zero.mpr
  have hw : |ω i| ≤ ‖ω‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le ω i
  have hs : |ω i| * L < 1 := by
    calc
      |ω i| * L ≤ ‖ω‖ * (1 / (‖ω‖ + 1)) :=
        mul_le_mul hw (min_le_right _ _) hL.le (norm_nonneg _)
      _ < 1 := by
        rw [mul_one_div]
        exact (div_lt_one (by positivity)).2 (by linarith)
  simpa [intervalAmplitude, max_eq_right hL.le] using sinc_mul_ne_zero hL hs

end AmbiguityHoles.Local
