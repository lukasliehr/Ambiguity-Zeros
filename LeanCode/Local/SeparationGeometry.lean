module

public import LeanCode.Local.SeparationKernel
public import LeanCode.Local.TrainsGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology

namespace AmbiguityHoles.Local

def packetBox {d : ℕ} (y h : Coord d) : Set (Coord d) :=
  {x | ∀ j, |x j-y j| ≤ h j}

theorem isClosed_packetBox {d : ℕ} (y h : Coord d) : IsClosed (packetBox y h) := by
  rw [packetBox, Set.setOf_forall]
  exact isClosed_iInter fun j ↦ isClosed_le (((PiLp.continuous_apply _ _ j).sub
    continuous_const).abs) continuous_const

def projectedFrequencies {d : ℕ} (K : Set (Coord d × Coord d))
    (Q : Set (Coord d)) : Set (Coord d) := Prod.snd '' (K ∩ Prod.fst ⁻¹' Q)

theorem isCompact_projectedFrequencies {d : ℕ} {K : Set (Coord d × Coord d)}
    {Q : Set (Coord d)} (hK : IsCompact K) (hQ : IsClosed Q) :
    IsCompact (projectedFrequencies K Q) :=
  (hK.inter_right (hQ.preimage continuous_fst)).image continuous_snd

theorem projectedFrequencies_subset {d : ℕ} {K : Set (Coord d × Coord d)}
    {Q J : Set (Coord d)} (hK : ∀ z ∈ K, z.2 ∈ J) :
    projectedFrequencies K Q ⊆ J := by
  rintro _ ⟨z, hz, rfl⟩
  exact hK z hz.1

theorem mem_projectedFrequencies {d : ℕ} {K : Set (Coord d × Coord d)}
    {Q : Set (Coord d)} {x ω : Coord d} (hz : (x, ω) ∈ K) (hx : x ∈ Q) :
    ω ∈ projectedFrequencies K Q := ⟨(x,ω), ⟨hz,hx⟩, rfl⟩

theorem exists_packetBox {d : ℕ} {K : Set (Coord d × Coord d)} (hK : IsClosed K)
    {y η : Coord d} (hy : (y,η) ∉ K) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ h : Coord d, (∀ j, 0 < h j ∧ h j < ρ ∧ |η j| * h j < 1) ∧
      η ∉ projectedFrequencies K (packetBox y h) := by
  let S : Set (Fin d → ℝ) := {u | (WithLp.toLp 2 u, η) ∉ K}
  have hS : IsOpen S :=
    hK.isOpen_compl.preimage ((PiLp.continuous_toLp _ _).prodMk continuous_const)
  have hmem : WithLp.ofLp y ∈ S := hy
  have hN := hS.mem_nhds hmem
  rw [nhds_pi, Filter.mem_pi'] at hN
  obtain ⟨I, U, hU, hsub⟩ := hN
  have balls (j : Fin d) : ∃ r > 0, Metric.ball (y j) r ⊆ U j :=
    Metric.mem_nhds_iff.mp (hU j)
  choose r hr hrU using balls
  let h : Coord d := WithLp.toLp 2 fun j ↦ min (ρ/2) (min (r j/2) (1/(|η j|+1)))
  have hh (j : Fin d) : 0 < h j :=
    lt_min (by linarith) (lt_min (by linarith [hr j]) (one_div_pos.mpr (by positivity)))
  have h₁ (j : Fin d) : h j ≤ ρ/2 := min_le_left _ _
  have h₂ (j : Fin d) : h j ≤ r j/2 := (min_le_right _ _).trans (min_le_left _ _)
  have h₃ (j : Fin d) : h j ≤ 1/(|η j|+1) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨h, fun j ↦ ⟨hh j, by linarith [h₁ j], ?_⟩, ?_⟩
  · calc
      |η j| * h j ≤ |η j| * (1/(|η j|+1)) :=
        mul_le_mul_of_nonneg_left (h₃ j) (abs_nonneg _)
      _ < 1 := by rw [mul_one_div]; exact (div_lt_one (by positivity)).2 (by linarith)
  · rintro ⟨⟨u,ω⟩, ⟨huK, hu⟩, rfl⟩
    apply (hsub (a := WithLp.ofLp u) ?_) huK
    intro j _
    apply hrU j
    rw [Metric.mem_ball, Real.dist_eq]
    exact (hu j).trans_lt (by linarith [h₂ j, hr j])

theorem localized_coordinate {ρ L x y c h ω : ℝ}
    (hL : 3*ρ < L) (hh : 0 < h) (hhρ : h < ρ)
    (hx : |x-c| ≤ ρ) (hy : |y-c| ≤ ρ)
    (hn : intervalDifference L h (x-(y-L-h)) ω ≠ 0) :
    |x-y| ≤ h := by
  have hs := not_imp_not.mpr (intervalDifference_eq_zero (L := L) (h := h)
    (x := x-(y-L-h)) (ω := ω) hh) hn
  simp only [not_not, mem_union, mem_Icc] at hs
  obtain ⟨hx₁,hx₂⟩ := abs_le.mp hx
  obtain ⟨hy₁,hy₂⟩ := abs_le.mp hy
  rcases hs with (hleft | hmid) | hright
  · exfalso
    linarith [hleft.2]
  · exfalso
    linarith [hmid.2]
  · exact abs_le.mpr ⟨by linarith [hright.1], by linarith [hright.2]⟩

end AmbiguityHoles.Local
