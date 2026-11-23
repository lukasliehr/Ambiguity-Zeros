module

public import Mathlib

@[expose] public section

/-!
The three main results of the paper.
This is the paper-facing statement file; proof bodies are intentionally omitted.
All three statements are proved in `Showcase_WithProofs.lean`.
`L2 d` is L²(ℝᵈ; ℂ), whose elements are identified up to equality almost everywhere.
`star` is complex conjugation, `•` is scalar multiplication, and `''` is set image.
-/

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

/-- Theorem 1.1 (`thm:phase-retrieval-d`): bounded open zero sets allow phase retrieval. -/
theorem bounded_openZeros_phaseRetrieval
    {d : ℕ} (hd : 1 ≤ d) (w : L2 d) (hw : w ≠ 0)
    (hbounded : Bornology.IsBounded (openZeros w)) :
    DoesPhaseRetrieval w := by
  sorry

/-- Theorem 1.2 (`thm:main`): any bounded regular open pattern can be realized
near any nonzero center, at every sufficiently small positive scale.
The equation Ω = interior (closure Ω) says that Ω is regular open. -/
theorem prescribed_openZeros
    {d : ℕ} (hd : 1 ≤ d) (Ω : Set (PhaseSpace d))
    (hbounded : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (hregular : Ω = interior (closure Ω))
    (a : PhaseSpace d) (ha : a ≠ 0) :
    ∃ b₀ > (0 : ℝ), ∀ b : ℝ, 0 < b → b < b₀ →
      ∃ f : L2 d,
        openZeros f =
          (fun z ↦ a + b • z) '' Ω ∪ (fun z ↦ -(a + b • z)) '' Ω := by
  sorry

/-- The Euclidean annulus O_{r,R}; the sum of squares avoids the max norm on pairs. -/
def annulus (d : ℕ) (r R : ℝ) : Set (PhaseSpace d) :=
  {z | r < Real.sqrt (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) ∧
       Real.sqrt (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) < R}

/-- Theorem 1.3 (`thm:counterexample`): an entire annulus can be forbidden,
even as a subset of the open zero set of a nonzero L²(ℝ) signal. -/
theorem forbidden_annulus :
    ∃ r R : ℝ, 0 < r ∧ r < R ∧
      ∀ f : L2 1, f ≠ 0 → ¬ annulus 1 r R ⊆ openZeros f := by
  sorry

end AmbiguityHoles
