module

public import LeanCode.Analysis.Fourier
public import LeanCode.Symplectic.Chirp
public import LeanCode.Symplectic.Dilation
public import LeanCode.Symplectic.Geometry
public import LeanCode.Symplectic.Reduction

public section

noncomputable section
open MeasureTheory Set

namespace AmbiguityHoles.Symplectic

open Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem pullback_shear (M : E →L[ℝ] E)
    (hM : ∀ a b, inner ℝ (M a) b = inner ℝ a (M b)) :
    Pullback (shear M) := by
  intro f hf
  refine ⟨chirp M f, memLp_chirp M hf, openZeros_eq_preimage _ ?_⟩
  intro z
  rw [shear_apply, ambiguity_chirp M hM]

theorem pullback_phaseDilation (B : E ≃L[ℝ] E) : Pullback (phaseDilation B) := by
  intro f hf
  refine ⟨f ∘ B, memLp_dilation B hf, openZeros_eq_preimage _ ?_⟩
  intro z
  exact ambiguity_dilation_zero_iff B f z.1 z.2

theorem pullback_quarterTurn : Pullback (quarterTurn (E := E)) := by
  intro f hf
  refine ⟨l2Fourier f hf, l2Fourier_memLp f hf, openZeros_eq_preimage _ ?_⟩
  intro z
  rw [quarterTurn_apply, ambiguity_fourier hf]

/-- The covariant changes used in the reduction act transitively on nonzero centers. -/
theorem exists_pullback_to_axis {a : E × E} (ha : a ≠ 0) {e : E} (he : e ≠ 0) :
    ∃ S : (E × E) ≃L[ℝ] (E × E), Pullback S ∧ S a = (e, 0) := by
  have axis (z : E × E) (hz : z.1 ≠ 0) :
      ∃ S : (E × E) ≃L[ℝ] (E × E), Pullback S ∧ S z = (e, 0) := by
    obtain ⟨M, hM, hMz⟩ := exists_symmetric_map hz z.2
    obtain ⟨B, hB⟩ := exists_dilation hz he
    refine ⟨(shear M).trans (phaseDilation B),
      (pullback_shear M hM).trans (pullback_phaseDilation B), ?_⟩
    change phaseDilation B (shear M z) = (e, 0)
    simp [hMz, hB]
  by_cases hx : a.1 = 0
  · have hp : a.2 ≠ 0 := fun hp ↦ ha (Prod.ext hx hp)
    have hq : (quarterTurn a).1 ≠ 0 := by simpa using hp
    obtain ⟨S, hS, heq⟩ := axis (quarterTurn a) hq
    exact ⟨quarterTurn.trans S, pullback_quarterTurn.trans hS, heq⟩
  · exact axis a hx

/-- Transfer the exact local realization statement to every nonzero center. -/
theorem prescribed_of_axis_local
    {e : E} (he : e ≠ 0) (N : Set (E × E)) (hN : IsOpen N) (heN : (e, 0) ∈ N)
    (hlocal : ∀ U : Set (E × E), IsOpen U → interior (closure U) = U → U ⊆ N →
      ∃ f : E → ℂ, MemLp f 2 volume ∧ openZeros f = U ∪ ((fun z ↦ -z) '' U))
    (Ω : Set (E × E)) (hbounded : Bornology.IsBounded Ω)
    (hregular : Ω = interior (closure Ω)) (a : E × E) (ha : a ≠ 0) :
    ∃ b₀ > (0 : ℝ), ∀ b : ℝ, 0 < b → b < b₀ →
      ∃ f : E → ℂ, MemLp f 2 volume ∧ openZeros f =
        (fun z ↦ a + b • z) '' Ω ∪ (fun z ↦ -(a + b • z)) '' Ω := by
  obtain ⟨S, hS, hSa⟩ := exists_pullback_to_axis ha he
  exact prescribed_of_local S hS N hN a (by rwa [hSa]) hlocal Ω hbounded hregular

end AmbiguityHoles.Symplectic
