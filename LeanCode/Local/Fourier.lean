module

public import Mathlib.Analysis.Fourier.AddCircleMulti

@[expose] public section

open scoped BigOperators
open Set

namespace AmbiguityHoles.Local

noncomputable section

abbrev Coordinates (d : ℕ) := Fin d → ℝ
abbrev Lattice (d : ℕ) := Fin d → ℤ
abbrev CosetIndex (d : ℕ) := Lattice d ⊕ Lattice d

def latticePoint {d : ℕ} (n : Lattice d) : Coordinates d := fun i => n i

def frequency {d : ℕ} (θ : Coordinates d) : CosetIndex d → Coordinates d
  | .inl n => latticePoint n
  | .inr n => latticePoint n + θ

def character {d : ℕ} (ξ ω : Coordinates d) : ℂ :=
  Real.fourierChar (-∑ i, ξ i * ω i)

@[simp] theorem norm_character {d : ℕ} (ξ ω : Coordinates d) :
    ‖character ξ ω‖ = 1 :=
  Circle.norm_coe _

theorem character_add_left {d : ℕ} (ξ μ ω : Coordinates d) :
    character (ξ + μ) ω = character ξ ω * character μ ω := by
  unfold character
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, neg_add,
    Real.fourierChar.map_add_eq_mul, Circle.coe_mul]

theorem character_add_right {d : ℕ} (ξ ω η : Coordinates d) :
    character ξ (ω + η) = character ξ ω * character ξ η := by
  unfold character
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, neg_add,
    Real.fourierChar.map_add_eq_mul, Circle.coe_mul]

def RapidCoefficients {d : ℕ} {ι : Type*} (ξ : ι → Coordinates d) (c : ι → ℂ) : Prop :=
  ∀ k : ℕ, Summable (fun i => ‖c i‖ * (1 + ‖ξ i‖) ^ k)

theorem RapidCoefficients.summable_norm {d : ℕ} {ι : Type*}
    {ξ : ι → Coordinates d} {c : ι → ℂ} (hc : RapidCoefficients ξ c) :
    Summable (fun i => ‖c i‖) := by
  simpa using hc 0

def series {d : ℕ} {ι : Type*} (ξ : ι → Coordinates d) (c : ι → ℂ)
    (ω : Coordinates d) : ℂ :=
  ∑' i, c i * character (ξ i) ω

theorem summable_series {d : ℕ} {ι : Type*} {ξ : ι → Coordinates d} {c : ι → ℂ}
    (hc : Summable (fun i => ‖c i‖)) (ω : Coordinates d) :
    Summable (fun i => c i * character (ξ i) ω) :=
  Summable.of_norm (by simpa [norm_mul] using hc)

end
end AmbiguityHoles.Local
