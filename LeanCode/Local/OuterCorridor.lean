module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

@[expose] public section

open Set MeasureTheory

namespace AmbiguityHoles.Local

/-- A finite collection of short forbidden intervals on the unit circle leaves simultaneous
room for a point and any prescribed translate of it. -/
theorem exists_circle_placement {ι : Type*} [Fintype ι]
    (c : ι → UnitAddCircle) (r : ℝ)
    (hr : 2 * (Fintype.card ι : ℝ) * (2 * r) < 1) (hr₀ : 0 ≤ r)
    (q : UnitAddCircle) :
    ∃ a : UnitAddCircle, ∀ i, r < dist a (c i) ∧ r < dist (a + q) (c i) := by
  let B (v : UnitAddCircle) := ⋃ i, Metric.closedBall (c i - v) r
  have hB (v : UnitAddCircle) :
      volume (B v) ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * (2 * r)) := by
    refine (measure_iUnion_le _).trans ?_
    rw [tsum_fintype]
    calc
      ∑ i, volume (Metric.closedBall (c i - v) r) ≤
          ∑ _i : ι, ENNReal.ofReal (2 * r) := by
        exact Finset.sum_le_sum fun i _ => by
          rw [AddCircle.volume_closedBall]
          exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
      _ = _ := by
        simp [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul]
  have hsmall : volume (B 0 ∪ B q) < 1 := by
    refine (measure_union_le _ _).trans_lt ?_
    refine (add_le_add (hB _) (hB _)).trans_lt ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr (by linarith)
  have hne : (B 0 ∪ B q)ᶜ.Nonempty := by
    rw [nonempty_compl]
    intro h
    rw [h, UnitAddCircle.measure_univ] at hsmall
    exact (lt_irrefl _ hsmall)
  obtain ⟨a, ha⟩ := hne
  refine ⟨a, fun i => ⟨?_, ?_⟩⟩
  · have h : a ∉ Metric.closedBall (c i - 0) r :=
      fun hh => ha (Or.inl (mem_iUnion.mpr ⟨i, hh⟩))
    simpa [Metric.mem_closedBall, not_le] using h
  · have h : a ∉ Metric.closedBall (c i - q) r :=
      fun hh => ha (Or.inr (mem_iUnion.mpr ⟨i, hh⟩))
    rw [Metric.mem_closedBall, ← dist_add_right a (c i - q) q, sub_add_cancel, not_le] at h
    exact h

/-- Each unit-length right-closed interval contains a lift of the simultaneous placement. -/
theorem exists_real_circle_placement {ι : Type*} [Fintype ι]
    (c : ι → UnitAddCircle) (r : ℝ)
    (hr : 2 * (Fintype.card ι : ℝ) * (2 * r) < 1) (hr₀ : 0 ≤ r)
    (q M : ℝ) :
    ∃ a : ℝ, M < a ∧ a ≤ M + 1 ∧
      ∀ i, r < dist (a : UnitAddCircle) (c i) ∧
        r < dist ((a + q : ℝ) : UnitAddCircle) (c i) := by
  obtain ⟨a, ha⟩ := exists_circle_placement c r hr hr₀ (q : UnitAddCircle)
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
  let n : ℤ := ⌊M - x⌋ + 1
  have hn₁ : M - x < (n : ℝ) := by
    dsimp [n]
    push_cast
    exact Int.lt_floor_add_one (M - x)
  have hn₂ : (n : ℝ) ≤ M - x + 1 := by
    dsimp [n]
    push_cast
    exact add_le_add_left (Int.floor_le (M - x)) 1
  have hz : ((n : ℝ) : UnitAddCircle) = 0 := by
    rw [← zsmul_one, AddCircle.coe_zsmul, AddCircle.coe_period, zsmul_zero]
  refine ⟨x + n, by linarith, by linarith, ?_⟩
  intro i
  simpa only [AddCircle.coe_add, hz, add_zero] using ha i

/-- The quotient distance is at most the distance between any two real lifts. -/
theorem unitAddCircle_dist_le (a b : ℝ) :
    dist (a : UnitAddCircle) (b : UnitAddCircle) ≤ |a - b| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub, ← Real.norm_eq_abs]
  exact QuotientAddGroup.norm_mk_le_norm

end AmbiguityHoles.Local
