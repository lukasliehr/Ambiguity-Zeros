module

public import LeanCode.Analysis.Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

noncomputable section
open Set
namespace AmbiguityHoles.Local

abbrev Coord (d : ℕ) := EuclideanSpace ℝ (Fin d)

def coordBox {d : ℕ} (r : ℝ) (x : Coord d) : Prop :=
  ∀ i, |x i| ≤ r

def unitCube {d : ℕ} (L : ℝ) : Set (Coord d) :=
  {x | ∀ i, x i ∈ Icc (0 : ℝ) L}

def cubePulse {d : ℕ} (L : ℝ) : Coord d → ℂ :=
  (unitCube L).indicator fun _ ↦ 1

def firstAxis (d : ℕ) : Coord d :=
  WithLp.toLp 2 fun i ↦ if i.val = 0 then 1 else 0

structure TrainGeometry {d : ℕ} {ι : Type*} (site : ι → Coord d)
    (σ s L ρ : ℝ) : Prop where
  rho_pos : 0 < ρ
  width : 4 * ρ < L
  near : 3 * L + 7 * ρ < s
  far : 2 * s + 2 * L + 4 * ρ < σ
  sep : ∀ i j, i ≠ j → ∃ k, σ ≤ |site i k - site j k|

theorem pulse_overlap {d : ℕ} {L : ℝ} {p q x t : Coord d}
    (hp : t + (1 / 2 : ℝ) • x - p ∈ unitCube L)
    (hq : t - (1 / 2 : ℝ) • x - q ∈ unitCube L) :
    coordBox L (x - (p - q)) := by
  intro i
  have hp' := hp i
  have hq' := hq i
  simp only [mem_Icc, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul] at hp' hq' ⊢
  exact abs_le.mpr ⟨by linarith [hp'.1, hq'.2], by linarith [hp'.2, hq'.1]⟩

section
variable {d : ℕ} {ι : Type*} {site : ι → Coord (d + 1)} {σ s L ρ : ℝ}

private theorem axis_apply (i : Fin (d + 1)) :
    firstAxis (d + 1) i = if i.val = 0 then 1 else 0 := rfl

theorem train_no_overlap_same (G : TrainGeometry site σ s L ρ)
    {x a b : Coord (d + 1)} {i j : ι} {e : ℝ} (he : e = 1 ∨ e = -1)
    (hx : coordBox ρ (x - (e * s) • firstAxis (d + 1)))
    (hab : coordBox (2 * (L + 3 * ρ)) (a - b)) :
    ¬ coordBox L (x - ((site i + a) - (site j + b))) := by
  intro h
  by_cases hij : i = j
  · subst j
    have u := abs_le.mp (hx 0)
    have v := abs_le.mp (hab 0)
    have w := abs_le.mp (h 0)
    simp [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, axis_apply] at u v w
    rcases he with rfl | rfl <;> norm_num at u <;>
      linarith [u.1, u.2, v.1, v.2, w.1, w.2, G.near]
  · obtain ⟨k, hk⟩ := G.sep i j hij
    have u := abs_le.mp (hx k)
    have v := abs_le.mp (hab k)
    have w := abs_le.mp (h k)
    have hs : 0 < s := by linarith [G.near, G.rho_pos, G.width]
    have hh : |site i k - site j k| ≤ s + 3 * L + 7 * ρ := by
      apply abs_le.mpr
      simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        axis_apply] at u v w
      rcases he with rfl | rfl <;> split_ifs at u <;> norm_num at u <;>
        constructor <;> linarith [u.1, u.2, v.1, v.2, w.1, w.2]
    linarith [G.far, G.near, G.width, G.rho_pos]

theorem train_overlap_mixed (G : TrainGeometry site σ s L ρ)
    {x a : Coord (d + 1)} {i j : ι} {e : ℝ} (he : e = 1 ∨ e = -1)
    (hx : coordBox ρ (x - (e * s) • firstAxis (d + 1)))
    (ha : coordBox (L + 3 * ρ) (a - s • firstAxis (d + 1)))
    (h : coordBox L (x - (site i - (site j + a)))) :
    i = j ∧ e = -1 := by
  have hs : 0 < s := by linarith [G.near, G.rho_pos, G.width]
  have hij : i = j := by
    by_contra hn
    obtain ⟨k, hk⟩ := G.sep i j hn
    have u := abs_le.mp (hx k)
    have v := abs_le.mp (ha k)
    have w := abs_le.mp (h k)
    have hh : |site i k - site j k| ≤ 2 * s + 2 * L + 4 * ρ := by
      apply abs_le.mpr
      simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        axis_apply] at u v w
      rcases he with rfl | rfl <;> split_ifs at u v <;> norm_num at u v <;>
        constructor <;> linarith [u.1, u.2, v.1, v.2, w.1, w.2]
    linarith [G.far]
  refine ⟨hij, ?_⟩
  rcases he with rfl | rfl
  · subst j
    have u := abs_le.mp (hx 0)
    have v := abs_le.mp (ha 0)
    have w := abs_le.mp (h 0)
    simp [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, axis_apply] at u v w
    linarith [u.1, v.1, w.2, G.near, G.width, G.rho_pos]
  · rfl

end

end AmbiguityHoles.Local
