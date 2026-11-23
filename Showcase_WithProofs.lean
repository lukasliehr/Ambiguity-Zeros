import LeanCode

/-!
Checked counterparts to `Showcase.lean`.

The statements below match the paper-facing Showcase. All proofs are supplied
by the internal library, without proof placeholders or additional assumptions.
-/

namespace AmbiguityHoles

/-- Theorem 1.1 (`thm:phase-retrieval-d`). -/
theorem bounded_openZeros_phaseRetrieval
    {d : ℕ} (hd : 1 ≤ d) (w : L2 d) (hw : w ≠ 0)
    (hbounded : Bornology.IsBounded (openZeros w)) :
    DoesPhaseRetrieval w :=
  bounded_openZeros_phaseRetrieval_proved hd w hw hbounded

/-- Theorem 1.2 (`thm:main`). -/
theorem prescribed_openZeros
    {d : ℕ} (hd : 1 ≤ d) (Ω : Set (PhaseSpace d))
    (hbounded : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (hregular : Ω = interior (closure Ω))
    (a : PhaseSpace d) (ha : a ≠ 0) :
    ∃ b₀ > (0 : ℝ), ∀ b : ℝ, 0 < b → b < b₀ →
      ∃ f : L2 d,
        openZeros f =
          (fun z ↦ a + b • z) '' Ω ∪ (fun z ↦ -(a + b • z)) '' Ω :=
  prescribed_openZeros_proved hd Ω hbounded hne hregular a ha

/-- Theorem 1.3 (`thm:counterexample`). -/
theorem forbidden_annulus :
    ∃ r R : ℝ, 0 < r ∧ r < R ∧
      ∀ f : L2 1, f ≠ 0 → ¬ annulus 1 r R ⊆ openZeros f :=
  forbidden_annulus_proved

end AmbiguityHoles
