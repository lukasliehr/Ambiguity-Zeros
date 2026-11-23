module

public import LeanCode.Local.RealizationCore
public import LeanCode.Local.GapSupply
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section

noncomputable section
open Set MeasureTheory
namespace AmbiguityHoles.Local

private theorem int_shift_separated {θ : ℝ} (h₀ : 0 < θ) (h₁ : θ < 1/2) (z : ℤ) :
    θ ≤ |(z : ℝ)+θ| := by
  by_cases hz : 0 ≤ z
  · have hz' : 0 ≤ (z : ℝ) := by exact_mod_cast hz
    exact (by linarith : θ ≤ (z : ℝ)+θ).trans (le_abs_self _)
  · have hz' : (z : ℝ) ≤ -1 := by exact_mod_cast (show z ≤ -1 by omega)
    exact (by linarith : θ ≤ -((z : ℝ)+θ)).trans (neg_le_abs _)

private theorem separated_latticeSite {d : ℕ} (θ : Coord (d+1))
    (hθ : ∀ j, 0 < θ j ∧ θ j < 1/2) :
    ∀ i j, i ≠ j → ∃ k, θ 0 ≤ |latticeSite θ i k-latticeSite θ j k| := by
  have hsame (m n : Fin (d+1) → ℤ) (hmn : m ≠ n) :
      ∃ k, θ 0 ≤ |(m k : ℝ)-(n k : ℝ)| := by
    have hk : ∃ k, m k ≠ n k := by
      by_contra! h
      exact hmn (funext h)
    obtain ⟨k,hk⟩ := hk
    have H := Int.one_le_abs (sub_ne_zero.mpr hk)
    have H' : (1 : ℝ) ≤ |(m k : ℝ)-(n k : ℝ)| := by exact_mod_cast H
    exact ⟨k,(by linarith [(hθ 0).2] : θ 0 ≤ 1).trans H'⟩
  intro i j hij
  cases i with
  | inl m =>
    cases j with
    | inl n => exact hsame m n (fun h ↦ hij (congrArg Sum.inl h))
    | inr n =>
      refine ⟨0, ?_⟩
      simp only [latticeSite_inl, latticeSite_inr, integerSite_apply, PiLp.add_apply]
      rw [abs_sub_comm, add_sub_right_comm, ← Int.cast_sub]
      exact int_shift_separated (hθ 0).1 (hθ 0).2 (n 0-m 0)
  | inr m =>
    cases j with
    | inl n =>
      refine ⟨0, ?_⟩
      simp only [latticeSite_inl, latticeSite_inr, integerSite_apply, PiLp.add_apply]
      rw [add_sub_right_comm, ← Int.cast_sub]
      exact int_shift_separated (hθ 0).1 (hθ 0).2 (m 0-n 0)
    | inr n =>
      simpa only [latticeSite_inr, PiLp.add_apply, add_sub_add_right_eq_sub, integerSite_apply] using
        hsame m n (fun h ↦ hij (congrArg Sum.inr h))

/-- Every regular open pattern in a fixed neighborhood of a nonzero delay can be
realized together with its central reflection as the open zero set of an ambiguity function. -/
theorem localRealization (d : ℕ) (hd : 0 < d) :
    ∃ e : Coord d, e ≠ 0 ∧ ∃ N : Set (Coord d × Coord d),
      IsOpen N ∧ (e,0) ∈ N ∧ ∀ U : Set (Coord d × Coord d), IsOpen U →
        interior (closure U) = U → U ⊆ N →
        ∃ f : Coord d → ℂ, MemLp f 2 volume ∧
          Analysis.openZeros f = U ∪ ((fun z ↦ -z) '' U) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  obtain ⟨θ,hθ,hres⟩ := exists_shift (n+1)
  let σ := θ 0
  let s := σ/4
  let L := σ/100
  let ρ := σ/1000
  have hσ := (hθ 0).1
  have hσ' := (hθ 0).2
  have G : TrainGeometry (latticeSite θ) σ s L ρ :=
    ⟨by dsimp [ρ,σ]; positivity,
      by dsimp [L,ρ,σ]; linarith,
      by dsimp [s,L,ρ,σ]; linarith,
      by dsimp [s,L,ρ,σ]; linarith,
      separated_latticeSite θ hθ⟩
  have hr : 32*(2*L+5*ρ) < 1 := by dsimp [L,ρ,σ]; linarith
  have hρ : ρ < 1/2 := by dsimp [ρ,σ]; linarith
  obtain ⟨w,hw,hgap⟩ := exists_gapSupply θ hθ hres G.rho_pos.le hρ
  exact localRealization_of_supply θ G hr w hw hgap

end AmbiguityHoles.Local
