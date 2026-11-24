module

public import LeanCode.Definitions
public import LeanCode.Analysis.PhaseRetrieval
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open MeasureTheory

namespace AmbiguityHoles

theorem character_eq_exponential (s : ℝ) :
    (Real.fourierChar (-s) : ℂ) = Complex.exp (-2 * Real.pi * Complex.I * s) := by
  rw [Real.fourierChar_apply]
  congr 1
  push_cast
  ring

theorem raw_ambiguity_eq {d : ℕ} (f : L2 d) (x ω : Rd d) :
    Analysis.ambiguity (f : Rd d → ℂ) x ω = ambiguity f (x, ω) := by
  simp only [Analysis.ambiguity, Analysis.crossAmbiguity, ambiguity, character_eq_exponential]

theorem raw_stft_eq {d : ℕ} (w f : L2 d) (x ω : Rd d) :
    Analysis.stft (w : Rd d → ℂ) (f : Rd d → ℂ) x ω = stft w f (x, ω) := by
  simp only [Analysis.stft, stft, character_eq_exponential]

theorem raw_openZeros_eq {d : ℕ} (f : L2 d) :
    Analysis.openZeros (f : Rd d → ℂ) = openZeros f := by
  simp only [Analysis.openZeros, openZeros, raw_ambiguity_eq]

theorem openZeros_toLp {d : ℕ} (f : Rd d → ℂ) (hf : MemLp f 2 volume) :
    openZeros (hf.toLp f) = Analysis.openZeros f := by
  rw [← raw_openZeros_eq]
  unfold Analysis.openZeros
  congr 1
  ext z
  change Analysis.ambiguity (hf.toLp f : Rd d → ℂ) z.1 z.2 = 0 ↔
    Analysis.ambiguity f z.1 z.2 = 0
  rw [Analysis.ambiguity_congr_ae (Lp.memLp (hf.toLp f)) hf hf.coeFn_toLp]

theorem realization_toLp {d : ℕ} {T : Set (PhaseSpace d)}
    (h : ∃ f : Rd d → ℂ, MemLp f 2 volume ∧ Analysis.openZeros f = T) :
    ∃ f : L2 d, openZeros f = T := by
  obtain ⟨f, hf, hzeros⟩ := h
  exact ⟨hf.toLp f, (openZeros_toLp f hf).trans hzeros⟩

/-- Theorem 1.1, for every finite dimension, with the exact definitions of the Challenge. -/
theorem bounded_openZeros_phaseRetrieval_proved
    {d : ℕ} (_hd : 1 ≤ d) (w : L2 d) (hw : w ≠ 0)
    (hbounded : Bornology.IsBounded (openZeros w)) : DoesPhaseRetrieval w := by
  have hne : ¬ (w : Rd d → ℂ) =ᵐ[volume] 0 := by
    intro h
    exact hw (Lp.ext (h.trans (Lp.coeFn_zero ℂ 2 volume).symm))
  have hb : Bornology.IsBounded (Analysis.openZeros (w : Rd d → ℂ)) := by
    rwa [raw_openZeros_eq]
  have hpr := Analysis.phase_retrieval_of_bounded_openZeros
    (w : Rd d → ℂ) (Lp.memLp w) hne hb
  intro f g hmag
  obtain ⟨θ, hθ⟩ := hpr (f : Rd d → ℂ) (g : Rd d → ℂ) (Lp.memLp f) (Lp.memLp g)
    (fun x ω ↦ by simpa only [raw_stft_eq] using hmag (x, ω))
  exact ⟨θ, Lp.ext (hθ.trans (Lp.coeFn_smul (Complex.exp (θ * Complex.I)) f).symm)⟩

end AmbiguityHoles
