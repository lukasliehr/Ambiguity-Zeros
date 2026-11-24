module

public import LeanCode.Analysis.Definitions

/-! The local realization statement transfers along covariant phase-space maps. -/

@[expose] public section

noncomputable section
open MeasureTheory Set

namespace AmbiguityHoles.Symplectic

open Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A phase-space change of variables for which every (L^2) ambiguity
zero pattern can be pulled back. -/
def Pullback (S : (E × E) ≃L[ℝ] (E × E)) : Prop :=
  ∀ f : E → ℂ, MemLp f 2 volume →
    ∃ g : E → ℂ, MemLp g 2 volume ∧ openZeros g = S ⁻¹' openZeros f

theorem Pullback.trans {S T : (E × E) ≃L[ℝ] (E × E)} (hS : Pullback S)
    (hT : Pullback T) : Pullback (S.trans T) := by
  intro f hf
  obtain ⟨g, hg, hz⟩ := hT f hf
  obtain ⟨k, hk, hkz⟩ := hS g hg
  exact ⟨k, hk, by rw [hkz, hz]; rfl⟩

theorem openZeros_eq_preimage {f g : E → ℂ} (S : (E × E) ≃L[ℝ] (E × E))
    (h : ∀ z : E × E, ambiguity g z.1 z.2 = 0 ↔
      ambiguity f (S z).1 (S z).2 = 0) :
    openZeros g = S ⁻¹' openZeros f := by
  unfold openZeros
  rw [show S ⁻¹' interior {z | ambiguity f z.1 z.2 = 0} =
      interior (S ⁻¹' {z | ambiguity f z.1 z.2 = 0}) from
    S.toHomeomorph.preimage_interior _]
  exact congrArg interior (Set.ext h)

/-- A local theorem at an arbitrary delay-axis neighborhood suffices once
a covariant linear map sends the requested center into that neighborhood. -/
theorem prescribed_of_local
    (S : (E × E) ≃L[ℝ] (E × E)) (hS : Pullback S)
    (N : Set (E × E)) (hN : IsOpen N) (a : E × E) (ha : S a ∈ N)
    (hlocal : ∀ U : Set (E × E), IsOpen U → interior (closure U) = U → U ⊆ N →
      ∃ f : E → ℂ, MemLp f 2 volume ∧ openZeros f = U ∪ ((fun z ↦ -z) '' U))
    (Ω : Set (E × E)) (hbounded : Bornology.IsBounded Ω)
    (hregular : Ω = interior (closure Ω)) :
    ∃ b₀ > (0 : ℝ), ∀ b : ℝ, 0 < b → b < b₀ →
      ∃ f : E → ℂ, MemLp f 2 volume ∧ openZeros f =
        (fun z ↦ a + b • z) '' Ω ∪ (fun z ↦ -(a + b • z)) '' Ω := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hN.preimage S.continuous) a ha
  obtain ⟨C, hC⟩ := hbounded.exists_norm_le
  let R := max C 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨r / R, div_pos hr hR, ?_⟩
  intro b hb hbr
  let A : (E × E) ≃ₜ (E × E) :=
    (Homeomorph.smulOfNeZero b hb.ne').trans (Homeomorph.addLeft a)
  let H := A.trans S.toHomeomorph
  let U := H '' Ω
  have hΩ : IsOpen Ω := by rw [hregular]; exact isOpen_interior
  have hU : IsOpen U := H.isOpenMap _ hΩ
  have hUreg : interior (closure U) = U := by
    dsimp only [U]
    rw [← H.image_closure, ← H.image_interior, ← hregular]
  have hUN : U ⊆ N := by
    rintro _ ⟨z, hz, rfl⟩
    change A z ∈ S ⁻¹' N
    apply hball
    change dist (a + b • z) a < r
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hb]
    calc
      b * ‖z‖ ≤ b * R := mul_le_mul_of_nonneg_left ((hC z hz).trans (le_max_left _ _)) hb.le
      _ < r := (lt_div_iff₀ hR).mp hbr
  obtain ⟨f, hf, hz⟩ := hlocal U hU hUreg hUN
  obtain ⟨g, hg, hgz⟩ := hS f hf
  refine ⟨g, hg, ?_⟩
  rw [hgz, hz, preimage_union]
  congr 1
  · ext z
    constructor
    · rintro ⟨u, hu, heq⟩
      exact ⟨u, hu, S.injective heq⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, rfl⟩
  · ext z
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, heq⟩
      refine ⟨u, hu, S.injective ?_⟩
      simp only [map_neg]
      exact heq
    · rintro ⟨u, hu, rfl⟩
      exact ⟨H u, ⟨u, hu, rfl⟩, (map_neg S (A u)).symm⟩

end AmbiguityHoles.Symplectic
