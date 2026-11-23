module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

@[expose] public section

namespace AmbiguityHoles.Local

/-- The real amplitude after removing the phase of the interval ambiguity. -/
noncomputable def intervalAmplitude (L x ω : ℝ) : ℝ :=
  let w := max 0 (L - |x|)
  w * Real.sinc (Real.pi * ω * w)

noncomputable def intervalDifference (L h x ω : ℝ) : ℝ :=
  intervalAmplitude L x ω -
    2 * Real.cos (Real.pi * ω * h) * intervalAmplitude L (x-h) ω +
    intervalAmplitude L (x-2*h) ω

private theorem amplitude_recurrence (a w h : ℝ) :
    (w+h) * Real.sinc (a*(w+h)) - 2*Real.cos (a*h) * (w * Real.sinc (a*w)) +
      (w-h)*Real.sinc (a*(w-h)) = 0 := by
  by_cases ha : a = 0
  · simp [ha]
    ring
  have conv (v : ℝ) : v * Real.sinc (a*v) = Real.sin (a*v) / a := by
    by_cases hv : v = 0
    · simp [hv]
    rw [Real.sinc_of_ne_zero (mul_ne_zero ha hv)]
    field_simp
  rw [conv, conv, conv, mul_add, mul_sub, Real.sin_add, Real.sin_sub]
  ring

theorem intervalAmplitude_eq_zero {L x ω : ℝ} (hx : L ≤ |x|) :
    intervalAmplitude L x ω = 0 := by
  simp [intervalAmplitude, max_eq_left (sub_nonpos.mpr hx)]

theorem intervalDifference_eq_zero {L h x ω : ℝ} (hh : 0 < h)
    (hx : x ∉ Set.Icc (-L) (-L+2*h) ∪ Set.Icc 0 (2*h) ∪ Set.Icc L (L+2*h)) :
    intervalDifference L h x ω = 0 := by
  simp only [Set.mem_union, Set.mem_Icc, not_or] at hx
  by_cases hl : x < -L
  · unfold intervalDifference
    rw [intervalAmplitude_eq_zero (le_trans (by linarith) (neg_le_abs x)),
      intervalAmplitude_eq_zero (le_trans (by linarith) (neg_le_abs (x-h))),
      intervalAmplitude_eq_zero (le_trans (by linarith) (neg_le_abs (x-2*h)))]
    ring
  by_cases hr : L+2*h < x
  · unfold intervalDifference
    rw [intervalAmplitude_eq_zero (le_trans (by linarith) (le_abs_self x)),
      intervalAmplitude_eq_zero (le_trans (by linarith) (le_abs_self (x-h))),
      intervalAmplitude_eq_zero (le_trans (by linarith) (le_abs_self (x-2*h)))]
    ring
  by_cases hn : x < 0
  · have hb : -L+2*h < x := lt_of_not_ge fun h' => hx.1.1 ⟨le_of_not_gt hl, h'⟩
    unfold intervalDifference intervalAmplitude
    rw [abs_of_neg hn, abs_of_neg (show x-h < 0 by linarith),
      abs_of_neg (show x-2*h < 0 by linarith)]
    rw [max_eq_right (show 0 ≤ L - -x by linarith),
      max_eq_right (show 0 ≤ L - -(x-h) by linarith),
      max_eq_right (show 0 ≤ L - -(x-2*h) by linarith)]
    have H := amplitude_recurrence (Real.pi*ω) (L - -(x-h)) h
    rw [show L - -(x-h) + h = L - -x by ring,
      show L - -(x-h) - h = L - -(x-2*h) by ring] at H
    exact H
  · have hb : 2*h < x := lt_of_not_ge fun h' => hx.1.2 ⟨le_of_not_gt hn, h'⟩
    have ht : x < L := lt_of_not_ge fun h' => hx.2 ⟨h', le_of_not_gt hr⟩
    unfold intervalDifference intervalAmplitude
    rw [abs_of_nonneg (le_of_not_gt hn), abs_of_pos (show 0 < x-h by linarith),
      abs_of_pos (show 0 < x-2*h by linarith)]
    rw [max_eq_right (show 0 ≤ L-x by linarith),
      max_eq_right (show 0 ≤ L-(x-h) by linarith),
      max_eq_right (show 0 ≤ L-(x-2*h) by linarith)]
    have H := amplitude_recurrence (Real.pi*ω) (L - (x-h)) (-h)
    rw [show L - (x-h) + -h = L-x by ring,
      show L - (x-h) - -h = L-(x-2*h) by ring,
      show Real.pi*ω * -h = -(Real.pi*ω*h) by ring, Real.cos_neg] at H
    exact H

theorem intervalDifference_at_tip {L h ω : ℝ} (hh : 0 < h) (hL : h ≤ L) :
    intervalDifference L h (L+h) ω = h * Real.sinc (Real.pi*ω*h) := by
  unfold intervalDifference
  rw [intervalAmplitude_eq_zero (le_trans (by linarith) (le_abs_self (L+h))),
    intervalAmplitude_eq_zero (le_trans (by linarith) (le_abs_self (L+h-h)))]
  simp only [mul_zero, sub_zero, zero_add, intervalAmplitude]
  rw [abs_of_nonneg (show 0 ≤ L+h-2*h by linarith),
    show L-(L+h-2*h) = h by ring, max_eq_right hh.le]

theorem sinc_mul_ne_zero {h ω : ℝ} (hh : 0 < h) (hs : |ω| * h < 1) :
    h * Real.sinc (Real.pi*ω*h) ≠ 0 := by
  apply mul_ne_zero hh.ne'
  by_cases he : Real.pi*ω*h = 0
  · simp [he]
  rw [Real.sinc_of_ne_zero he]
  apply div_ne_zero _ he
  have hp : |Real.pi*ω*h| < Real.pi := by
    rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hh, mul_assoc]
    simpa using mul_lt_mul_of_pos_left hs Real.pi_pos
  exact fun hz => he ((Real.sin_eq_zero_iff_of_lt_of_lt (abs_lt.mp hp).1
    (abs_lt.mp hp).2).mp hz)

theorem intervalAmplitude_exists_ne_zero {L : ℝ} (hL : 0 < L) (ω : ℝ) :
    ∃ β ∈ Set.Icc (-L) L, intervalAmplitude L β ω ≠ 0 := by
  let h := min L (1 / (|ω| + 1))
  have hh : 0 < h := lt_min hL (one_div_pos.mpr (by positivity))
  have hle : h ≤ L := min_le_left _ _
  have hω : |ω| * h < 1 := by
    calc
      |ω| * h ≤ |ω| * (1 / (|ω| + 1)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (abs_nonneg _)
      _ < 1 := by
        rw [mul_one_div]
        exact (div_lt_one (by positivity)).2 (by linarith)
  refine ⟨L-h, ⟨by linarith, by linarith⟩, ?_⟩
  unfold intervalAmplitude
  rw [abs_of_nonneg (sub_nonneg.mpr hle), show L-(L-h) = h by ring, max_eq_right hh.le]
  exact sinc_mul_ne_zero hh hω

end AmbiguityHoles.Local
