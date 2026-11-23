module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

@[expose] public section

/-! Shared function-level API for the full-dimensional proof development. -/

noncomputable section
open MeasureTheory

namespace AmbiguityHoles.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def crossAmbiguity (f g : E → ℂ) (x ω : E) : ℂ :=
  ∫ t, f (t + (1 / 2 : ℝ) • x) * star (g (t - (1 / 2 : ℝ) • x)) *
    (Real.fourierChar (-(inner ℝ ω t)) : ℂ)

def ambiguity (f : E → ℂ) (x ω : E) : ℂ := crossAmbiguity f f x ω

def stft (w f : E → ℂ) (x ω : E) : ℂ :=
  ∫ t, f t * star (w (t - x)) * (Real.fourierChar (-(inner ℝ ω t)) : ℂ)

def translate (x : E) (f : E → ℂ) : E → ℂ := fun t ↦ f (t - x)

def modulate (ω : E) (f : E → ℂ) : E → ℂ :=
  fun t ↦ (Real.fourierChar (inner ℝ ω t) : ℂ) * f t

def openZeros (f : E → ℂ) : Set (E × E) :=
  interior {z | ambiguity f z.1 z.2 = 0}

def DoesPhaseRetrieval (w : E → ℂ) : Prop :=
  ∀ f g : E → ℂ, MemLp f 2 volume → MemLp g 2 volume →
    (∀ x ω, ‖stft w f x ω‖ = ‖stft w g x ω‖) →
    ∃ θ : ℝ, g =ᵐ[volume] fun t ↦ Complex.exp (θ * Complex.I) * f t

end AmbiguityHoles.Analysis
