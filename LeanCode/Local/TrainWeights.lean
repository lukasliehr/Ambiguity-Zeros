module

public import LeanCode.Local.Fourier
public import LeanCode.Local.Lattice
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

noncomputable section

open Set Filter

namespace AmbiguityHoles.Local

private theorem exists_summable_lattice_weight (d : ℕ) :
    ∃ k : ℕ, Summable (fun n : Lattice d ↦ (1 + ‖latticePoint n‖)⁻¹ ^ k) := by
  let b := Pi.basisFun ℝ (Fin d)
  let L : Submodule ℤ (Coordinates d) := Submodule.span ℤ (range b)
  letI : DiscreteTopology L := inferInstanceAs (DiscreteTopology (Submodule.span ℤ (range b)))
  let j (n : Lattice d) : L :=
    ⟨latticePoint n, (b.mem_span_iff_repr_mem ℤ _).2 (fun i ↦ ⟨n i, rfl⟩)⟩
  have hj : Function.Injective j := by
    intro n m h
    funext i
    exact Int.cast_injective (α := ℝ) (congrArg (fun z : L ↦ z.1 i) h)
  let k := Module.finrank ℤ L + 1
  refine ⟨k, ?_⟩
  have hsum := (ZLattice.summable_norm_pow_inv L k (Nat.lt_succ_self _)).comp_injective hj
  apply hsum.of_norm_bounded_eventually
  have hfinite : ({0} : Set (Lattice d)).Finite := finite_singleton 0
  filter_upwards [hfinite.compl_mem_cofinite] with n hn
  have hn0 : n ≠ 0 := by simpa using hn
  have hpos : 0 < ‖latticePoint n‖ := by
    apply norm_pos_iff.mpr
    intro hz
    apply hn0 (hj (Subtype.ext ?_))
    change latticePoint n = latticePoint 0
    rw [hz]
    funext i
    simp [latticePoint]
  change ‖(1 + ‖latticePoint n‖)⁻¹ ^ k‖ ≤ ‖latticePoint n‖⁻¹ ^ k
  rw [Real.norm_of_nonneg (by positivity)]
  gcongr
  linarith

set_option maxHeartbeats 400000 in
/-- Polynomially decaying reference weights give square-summable trains and
allow every rapid coefficient family to be divided by the reference weights. -/
theorem exists_train_weight {d : ℕ} (θ : Coord d)
    (hθ : ∀ i, 0 < θ i ∧ θ i < 1/2) :
    ∃ w : CosetIndex d → ℂ, (∀ i, w i ≠ 0) ∧
      Summable (fun i ↦ ‖w i‖ ^ 2) ∧
      ∀ c, RapidCoefficients (frequency (WithLp.ofLp θ)) c →
        Summable (fun i ↦ ‖c i / star (w i)‖ ^ 2) := by
  obtain ⟨k, hsum⟩ := exists_summable_lattice_weight d
  let v (n : Lattice d) : ℝ := (1 + ‖latticePoint n‖)⁻¹ ^ k
  have hv (n : Lattice d) : 0 < v n := by dsimp [v]; positivity
  have hv₁ (n : Lattice d) : v n ≤ 1 := by
    dsimp [v]
    exact pow_le_one₀ (by positivity)
      (inv_le_one_of_one_le₀ (le_add_of_nonneg_right (norm_nonneg _)))
  let w : CosetIndex d → ℂ := Sum.elim (fun n ↦ (v n : ℂ)) (fun n ↦ (v n : ℂ))
  have hnorm (n : Lattice d) : ‖(v n : ℂ)‖ = v n := by
    rw [Complex.norm_real, Real.norm_of_nonneg (hv n).le]
  have hsq : Summable (fun n ↦ ‖(v n : ℂ)‖ ^ 2) := by
    simp_rw [hnorm]
    exact hsum.of_nonneg_of_le (fun _ ↦ sq_nonneg _) (fun n ↦ by
      nlinarith [hv n, hv₁ n, mul_nonneg (hv n).le (sub_nonneg.mpr (hv₁ n))])
  refine ⟨w, ?_, Summable.sum (fun i ↦ ‖w i‖ ^ 2) hsq hsq, ?_⟩
  · intro i
    cases i <;> exact Complex.ofReal_ne_zero.mpr (hv _).ne'
  intro c hc
  let θ' : Coordinates d := WithLp.ofLp θ
  have hθnorm : ‖θ'‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    change ‖θ i‖ ≤ 1
    rw [Real.norm_of_nonneg (hθ i).1.le]
    exact (hθ i).2.le.trans (by norm_num)
  have hdiv (z : ℂ) (n : Lattice d) :
      ‖z / star (v n : ℂ)‖ = ‖z‖ * (1 + ‖latticePoint n‖) ^ k := by
    rw [norm_div, norm_star, hnorm, show v n = ((1 + ‖latticePoint n‖) ^ k)⁻¹ by
      simp [v, inv_pow], div_inv_eq_mul]
  have hsum' := (hc k).mul_left ((2 : ℝ) ^ k)
  have hℓ₁ : Summable (fun i ↦ ‖c i / star (w i)‖) := by
    refine hsum'.of_nonneg_of_le (fun _ ↦ norm_nonneg _) ?_
    intro i
    cases i with
    | inl n =>
      change ‖c (.inl n) / star (v n : ℂ)‖ ≤
        2 ^ k * (‖c (.inl n)‖ * (1 + ‖latticePoint n‖) ^ k)
      rw [hdiv]
      exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
    | inr n =>
      change ‖c (.inr n) / star (v n : ℂ)‖ ≤
        2 ^ k * (‖c (.inr n)‖ * (1 + ‖latticePoint n + θ'‖) ^ k)
      rw [hdiv, mul_left_comm, ← mul_pow]
      gcongr
      have hle : ‖latticePoint n‖ ≤ ‖latticePoint n + θ'‖ + ‖θ'‖ := by
        simpa only [add_sub_cancel_right] using norm_sub_le (latticePoint n + θ') θ'
      linarith [norm_nonneg (latticePoint n + θ')]
  let A : ℝ := ∑' i, ‖c i / star (w i)‖
  refine (hℓ₁.mul_right A).of_nonneg_of_le (fun _ ↦ sq_nonneg _) ?_
  intro i
  rw [pow_two]
  exact mul_le_mul_of_nonneg_left
    (hℓ₁.le_tsum i (fun _ _ ↦ norm_nonneg _)) (norm_nonneg _)

end AmbiguityHoles.Local
