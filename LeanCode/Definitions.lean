module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

@[expose] public section

noncomputable section
open MeasureTheory

namespace AmbiguityHoles

/-- Euclidean space ℝᵈ and the space L²(ℝᵈ; ℂ). -/
abbrev Rd (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev L2 (d : ℕ) := Lp ℂ 2 (volume : Measure (Rd d))
abbrev PhaseSpace (d : ℕ) := Rd d × Rd d

/-- The ambiguity function A(f)(x, ω). -/
def ambiguity {d : ℕ} (f : L2 d) (z : PhaseSpace d) : ℂ :=
  ∫ t, f (t + (1 / 2 : ℝ) • z.1) * star (f (t - (1 / 2 : ℝ) • z.1)) *
    Complex.exp (-2 * Real.pi * Complex.I * (inner ℝ z.2 t : ℝ))

/-- The open zero set 𝒵(f) = int{z : A(f)(z) = 0}. -/
def openZeros {d : ℕ} (f : L2 d) : Set (PhaseSpace d) :=
  interior {z | ambiguity f z = 0}

/-- The short-time Fourier transform V_w f(x, ω). -/
def stft {d : ℕ} (w f : L2 d) (z : PhaseSpace d) : ℂ :=
  ∫ t, f t * star (w (t - z.1)) *
    Complex.exp (-2 * Real.pi * Complex.I * (inner ℝ z.2 t : ℝ))

/-- STFT magnitudes determine every L² signal up to a constant phase. -/
def DoesPhaseRetrieval {d : ℕ} (w : L2 d) : Prop :=
  ∀ f g : L2 d,
    (∀ z, ‖stft w f z‖ = ‖stft w g z‖) →
    ∃ θ : ℝ, g = Complex.exp (θ * Complex.I) • f

/-- The Euclidean annulus O_{r,R}; the sum of squares avoids the max norm on pairs. -/
def annulus (d : ℕ) (r R : ℝ) : Set (PhaseSpace d) :=
  {z | r < Real.sqrt (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) ∧
       Real.sqrt (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) < R}

end AmbiguityHoles
