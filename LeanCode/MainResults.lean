module

public import LeanCode.AnalysisBridge
public import LeanCode.Local.Realization
public import LeanCode.Symplectic.Covariance

public section

namespace AmbiguityHoles

/-- Theorem 1.2, with the exact hypotheses and conclusion of the Challenge. -/
theorem prescribed_openZeros_proved
    {d : ℕ} (hd : 1 ≤ d) (Ω : Set (PhaseSpace d))
    (hbounded : Bornology.IsBounded Ω) (_hne : Ω.Nonempty)
    (hregular : Ω = interior (closure Ω))
    (a : PhaseSpace d) (ha : a ≠ 0) :
    ∃ b₀ > (0 : ℝ), ∀ b : ℝ, 0 < b → b < b₀ →
      ∃ f : L2 d,
        openZeros f =
          (fun z ↦ a + b • z) '' Ω ∪ (fun z ↦ -(a + b • z)) '' Ω := by
  obtain ⟨e, he, N, hN, heN, hlocal⟩ := Local.localRealization d hd
  obtain ⟨b₀, hb₀, hscale⟩ :=
    Symplectic.prescribed_of_axis_local he N hN heN hlocal Ω hbounded hregular a ha
  exact ⟨b₀, hb₀, fun b hb hbsmall ↦ realization_toLp (hscale b hb hbsmall)⟩

end AmbiguityHoles
