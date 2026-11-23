module

public import LeanCode.Local.SeparationKernel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

@[expose] public section

namespace AmbiguityHoles.Local

open scoped BigOperators
noncomputable section

def differenceCoefficient (k : Fin 3) (r : ℂ) : ℂ :=
  if k = 0 then 1 else if k = 1 then -(1+r) else r

def halfPhase (t : ℝ) : ℂ := Complex.exp (-(t : ℂ) * Complex.I)

theorem halfPhase_add (t u : ℝ) : halfPhase (t+u) = halfPhase t * halfPhase u := by
  unfold halfPhase
  rw [Complex.ofReal_add, ← Complex.exp_add]
  congr 1
  ring

theorem halfPhase_ne_zero (t : ℝ) : halfPhase t ≠ 0 := Complex.exp_ne_zero _

theorem difference_sum (L h x ω : ℝ) :
    ∑ k : Fin 3, halfPhase (Real.pi*ω*((k.val : ℝ)*h)) *
        differenceCoefficient k (halfPhase (-(2*Real.pi*ω*h))) *
        (intervalAmplitude L (x-(k.val : ℝ)*h) ω : ℂ) =
      (intervalDifference L h x ω : ℂ) := by
  let a := Real.pi*ω*h
  have P : halfPhase a * halfPhase (-(2*a)) = halfPhase (-a) := by
    rw [← halfPhase_add]
    congr 1
    ring
  have Q : halfPhase (2*a) * halfPhase (-(2*a)) = 1 := by
    rw [← halfPhase_add, add_neg_cancel]
    simp [halfPhase]
  have C : halfPhase a + halfPhase (-a) = 2 * (Real.cos a : ℂ) := by
    unfold halfPhase
    rw [← Complex.ofReal_neg, Complex.exp_ofReal_mul_I, Complex.ofReal_neg, neg_neg,
      Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
    ring
  have hd0 (r : ℂ) : differenceCoefficient 0 r = 1 := by simp [differenceCoefficient]
  have hd1 (r : ℂ) : differenceCoefficient 1 r = -(1+r) := by
    rw [differenceCoefficient, if_neg (by decide), if_pos rfl]
  have hd2 (r : ℂ) : differenceCoefficient 2 r = r := by
    rw [differenceCoefficient, if_neg (by decide), if_neg (by decide)]
  rw [Fin.sum_univ_three, hd0, hd1, hd2]
  simp only [show ((0 : Fin 3).val : ℝ) = 0 by norm_num,
    show ((1 : Fin 3).val : ℝ) = 1 by norm_num,
    show ((2 : Fin 3).val : ℝ) = 2 by rfl,
    zero_mul, mul_zero, one_mul, mul_one, sub_zero,
    show halfPhase 0 = 1 by simp [halfPhase]]
  have H : Real.pi * ω * (2*h) = 2*a := by dsimp [a]; ring
  have J : 2*Real.pi*ω*h = 2*a := by dsimp [a]; ring
  rw [H, J]
  change (intervalAmplitude L x ω : ℂ) +
      halfPhase a * -(1 + halfPhase (-(2*a))) * _ +
      (halfPhase (2*a) * halfPhase (-(2*a))) * _ = _
  rw [show halfPhase a * -(1 + halfPhase (-(2*a))) = -(halfPhase a + halfPhase (-a)) by
    rw [mul_neg, mul_add, mul_one, P], C, Q]
  simp only [intervalDifference, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  change _ = _ - 2 * (Real.cos a : ℂ) * _ + _
  ring

theorem difference_product {d : ℕ} (L : ℝ) (h x ω : Fin d → ℝ) :
    ∑ k : Fin d → Fin 3, ∏ j, (halfPhase (Real.pi*ω j*((k j).val*h j)) *
        differenceCoefficient (k j) (halfPhase (-(2*Real.pi*ω j*h j))) *
        (intervalAmplitude L (x j-(k j).val*h j) (ω j) : ℂ)) =
      ∏ j, (intervalDifference L (h j) (x j) (ω j) : ℂ) := by
  let F (j : Fin d) (k : Fin 3) :=
    halfPhase (Real.pi*ω j*(k.val*h j)) *
      differenceCoefficient k (halfPhase (-(2*Real.pi*ω j*h j))) *
      (intervalAmplitude L (x j-k.val*h j) (ω j) : ℂ)
  change (∑ k : Fin d → Fin 3, ∏ j, F j (k j)) = _
  rw [← Fintype.prod_sum F]
  exact Finset.prod_congr rfl fun j _ ↦ difference_sum _ _ _ _

end
end AmbiguityHoles.Local
