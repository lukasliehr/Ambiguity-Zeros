module

public import LeanCode.Local.TrainsGeometry
public import LeanCode.Analysis.Basic
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

@[expose] public section

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace AmbiguityHoles.Local
open Analysis

variable {d : ℕ} {ι : Type*}

theorem isCompact_unitCube (L : ℝ) : IsCompact (unitCube L : Set (Coord d)) := by
  let e := PiLp.homeomorph 2 (fun _ : Fin d ↦ ℝ)
  apply (e.isCompact_preimage (s := {x : Fin d → ℝ | ∀ i, x i ∈ Icc (0 : ℝ) L})).mpr
  exact isCompact_pi_infinite fun _ ↦ isCompact_Icc

theorem measurable_unitCube (L : ℝ) : MeasurableSet (unitCube L : Set (Coord d)) :=
  (isCompact_unitCube L).isClosed.measurableSet

theorem measurable_cubePulse (L : ℝ) : Measurable (cubePulse L : Coord d → ℂ) :=
  measurable_const.indicator (measurable_unitCube L)

theorem cubePulse_memLp (L : ℝ) (p : ℝ≥0∞) : MemLp (cubePulse L : Coord d → ℂ) p volume :=
  memLp_indicator_const p (measurable_unitCube L).nullMeasurableSet 1
    (Or.inr (isCompact_unitCube L).measure_lt_top.ne)

def cubeTrain (L : ℝ) (site : ι → Coord d) (c : ι → ℂ) (t : Coord d) : ℂ :=
  ∑' i, c i * cubePulse L (t - site i)

theorem norm_cubePulse_le_one (L : ℝ) (t : Coord d) : ‖cubePulse L t‖ ≤ 1 := by
  by_cases ht : t ∈ unitCube L <;> simp [cubePulse, ht]

theorem cubeTrain_at {site : ι → Coord d} {L : ℝ}
    (h : ∀ i j, i ≠ j → ∃ k, L < |site i k - site j k|) (c : ι → ℂ)
    {t : Coord d} {i : ι} (ht : t - site i ∈ unitCube L) :
    cubeTrain L site c t = c i := by
  unfold cubeTrain
  rw [tsum_eq_single i]
  · simp [cubePulse, ht]
  · intro j hji
    have hj : t - site j ∉ unitCube L := by
      intro hj
      obtain ⟨k, hk⟩ := h j i hji
      have u := ht k
      have v := hj k
      simp only [mem_Icc, PiLp.sub_apply] at u v
      exact hk.not_ge (abs_le.mpr ⟨by linarith [u.1, v.2], by linarith [u.2, v.1]⟩)
    simp [cubePulse, hj]

theorem cubeTrain_off {site : ι → Coord d} {L : ℝ} (c : ι → ℂ)
    {t : Coord d} (ht : ∀ i, t - site i ∉ unitCube L) :
    cubeTrain L site c t = 0 := by
  simp [cubeTrain, cubePulse, ht]

theorem shifted_width_sep {site : ι → Coord d} {σ s L ρ : ℝ}
    (G : TrainGeometry site σ s L ρ) (a : Coord d) :
    ∀ i j, i ≠ j → ∃ k, L < |(site i + a) k - (site j + a) k| := by
  intro i j hij
  obtain ⟨k, hk⟩ := G.sep i j hij
  refine ⟨k, ?_⟩
  simp only [PiLp.add_apply, add_sub_add_right_eq_sub]
  linarith [G.far, G.near, G.width, G.rho_pos]

theorem translate_cubeTrain (L : ℝ) (site : ι → Coord d) (c : ι → ℂ) (a : Coord d) :
    translate a (cubeTrain L site c) = cubeTrain L (fun i ↦ site i + a) c := by
  ext t
  simp only [translate, cubeTrain]
  congr 1
  funext i
  rw [sub_sub, add_comm a]

end AmbiguityHoles.Local
