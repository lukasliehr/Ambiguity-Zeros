module

public import LeanCode.Local.TrainsGeometry
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section

noncomputable section
open Set Polynomial
namespace AmbiguityHoles.Local

def integerSite {d : ℕ} (n : Fin d → ℤ) : Coord d :=
  WithLp.toLp 2 (fun i ↦ (n i : ℝ))

def latticeSite {d : ℕ} (θ : Coord d) :
    ((Fin d → ℤ) ⊕ (Fin d → ℤ)) → Coord d :=
  Sum.elim integerSite (fun n ↦ integerSite n + θ)

@[simp] theorem integerSite_apply {d : ℕ} (n : Fin d → ℤ) (i : Fin d) :
    integerSite n i = (n i : ℝ) := rfl

@[simp] theorem latticeSite_inl {d : ℕ} (θ : Coord d) (n : Fin d → ℤ) :
    latticeSite θ (.inl n) = integerSite n := rfl

@[simp] theorem latticeSite_inr {d : ℕ} (θ : Coord d) (n : Fin d → ℤ) :
    latticeSite θ (.inr n) = integerSite n + θ := rfl

theorem exists_shift (d : ℕ) :
    ∃ θ : Coord d, (∀ i, 0 < θ i ∧ θ i < 1/2) ∧
      ∀ n : Fin d → ℤ, Real.fourierChar (-(inner ℝ θ (integerSite n))) = 1 → n = 0 := by
  have hnot : ¬ Set.Ioo (1/4 : ℝ) (1/2) ⊆ {x : ℝ | IsAlgebraic ℚ x} := by
    intro h
    exact (not_le.mpr (by norm_num : (1/4 : ℝ) < 1/2))
      (Cardinal.Real.Ioo_countable_iff.mp ((Algebraic.countable ℚ ℝ).mono h))
  obtain ⟨t, ht, htr⟩ := not_subset.mp hnot
  have ht0 : 0 < t := by linarith [ht.1]
  refine ⟨WithLp.toLp 2 (fun i : Fin d ↦ t ^ (i.val + 1)), ?_, ?_⟩
  · intro i
    change 0 < t ^ (i.val + 1) ∧ t ^ (i.val + 1) < 1 / 2
    refine ⟨by positivity, lt_of_le_of_lt ?_ ht.2⟩
    rw [pow_succ]
    exact mul_le_of_le_one_left ht0.le (pow_le_one₀ ht0.le (by linarith [ht.2]))
  · intro n hn
    rw [Real.fourierChar_apply', Circle.exp_eq_one] at hn
    obtain ⟨m, hm⟩ := hn
    change 2 * Real.pi * -(∑ i : Fin d, (n i : ℝ) * t ^ (i.val + 1)) =
      (m : ℝ) * (2 * Real.pi) at hm
    have hm' : -(∑ i : Fin d, t ^ (i.val + 1) * (n i : ℝ)) = m := by
      apply (mul_right_inj' (show 2 * Real.pi ≠ 0 by positivity)).mp
      simpa only [mul_comm (2 * Real.pi), mul_comm ((n _) : ℝ)] using hm
    let p : ℚ[X] := Polynomial.C (m : ℚ) +
      ∑ i : Fin d, Polynomial.monomial (i.val + 1) (n i : ℚ)
    have hp : Polynomial.aeval t p = 0 := by
      simp only [p, map_add, map_sum, Polynomial.aeval_C, Polynomial.aeval_monomial,
        map_intCast]
      rw [← hm']
      simp_rw [mul_comm (↑(n _) : ℝ)]
      ring
    have hp0 : p = 0 := by
      by_contra h
      exact htr ⟨p, h, hp⟩
    ext i
    have hcoeff := congrArg (fun q : ℚ[X] ↦ q.coeff (i.val + 1)) hp0
    simp only [p, Polynomial.coeff_add, Polynomial.coeff_C, Nat.succ_ne_zero,
      if_false, zero_add, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial,
      Polynomial.coeff_zero] at hcoeff
    rw [Finset.sum_eq_single i] at hcoeff
    · simpa using hcoeff
    · intro j _ hj
      exact if_neg (by intro he; exact hj (Fin.ext (by omega)))
    · simp

end AmbiguityHoles.Local
