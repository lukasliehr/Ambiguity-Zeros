module

public import LeanCode.Local.TrainsGeometry
public import LeanCode.Local.SeparationAlgebra
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open Set
namespace AmbiguityHoles.Local

def band {d : ℕ} (s ρ : ℝ) : Set (Coord d) :=
  {x | coordBox ρ (x - s • firstAxis d)}

theorem coordBox_neg {d : ℕ} {r : ℝ} {x : Coord d} (h : coordBox r x) :
    coordBox r (-x) := fun i ↦ by simpa using h i

theorem neg_mem_band {d : ℕ} {s ρ : ℝ} {x : Coord d} (hx : x ∈ band s ρ) :
    -x ∈ band (-s) ρ := by
  change coordBox ρ (-x - (-s) • firstAxis d)
  convert coordBox_neg hx using 1
  module

theorem half_phase_fourierChar {d : ℕ} (a ω : Coord d) :
    (Real.fourierChar (-(inner ℝ ω ((1/2 : ℝ) • a))) : ℂ) =
      halfPhase (Real.pi * inner ℝ ω a) := by
  rw [Real.fourierChar_apply, inner_smul_right, halfPhase]
  push_cast
  ring_nf

def trainRegion {d : ℕ} {ι : Type*} (site : ι → Coord d) (L : ℝ)
    (S : Set (Coord d)) : Set (Coord d) :=
  {t | ∃ a ∈ S, ∃ i, t - (site i + a) ∈ unitCube L}

end AmbiguityHoles.Local
