module

public import LeanCode.Definitions
import LeanCode

@[expose] public section

/-!
The three main results of the paper, with proofs.

The definitions and statements are those of `Challenge.lean`. The definitions are imported from
`LeanCode/Definitions.lean` and the proofs are supplied by the library `LeanCode`.
-/

noncomputable section
open MeasureTheory

namespace AmbiguityHoles

/-- Theorem 1.1 (`thm:phase-retrieval-d`): bounded open zero sets allow phase retrieval. -/
theorem bounded_openZeros_phaseRetrieval
    {d : ℕ} (hd : 1 ≤ d) (w : L2 d) (hw : w ≠ 0)
    (hbounded : Bornology.IsBounded (openZeros w)) :
    DoesPhaseRetrieval w :=
  bounded_openZeros_phaseRetrieval_proved hd w hw hbounded

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
          (fun z ↦ a + b • z) '' Ω ∪ (fun z ↦ -(a + b • z)) '' Ω :=
  prescribed_openZeros_proved hd Ω hbounded hne hregular a ha

/-- Theorem 1.3 (`thm:counterexample`): an entire annulus can be forbidden,
even as a subset of the open zero set of a nonzero L²(ℝ) signal. -/
theorem forbidden_annulus :
    ∃ r R : ℝ, 0 < r ∧ r < R ∧
      ∀ f : L2 1, f ≠ 0 → ¬ annulus 1 r R ⊆ openZeros f :=
  forbidden_annulus_proved

end AmbiguityHoles
