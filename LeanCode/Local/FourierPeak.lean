module

public import LeanCode.Local.FourierPeriodization
public import Mathlib.Geometry.Manifold.PartitionOfUnity

@[expose] public section

noncomputable section
open Set
open scoped Manifold ContDiff

namespace AmbiguityHoles.Local

structure SmoothPeak {d : ℕ} (F : Set (Coordinates d)) (a : Coordinates d) where
  η : Coordinates d → ℝ
  smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) η
  nonneg : ∀ x, 0 ≤ η x
  le_one : ∀ x, η x ≤ 1
  eq_one_iff : ∀ x, η x = 1 ↔ x ∈ F
  compact : HasCompactSupport η
  support_inside : tsupport η ⊆ openCell a

theorem exists_smoothPeak {d : ℕ} {F : Set (Coordinates d)}
    (hF : IsCompact F) {a : Coordinates d} (hFa : F ⊆ openCell a) :
    Nonempty (SmoothPeak F a) := by
  obtain ⟨V, hVo, hFV, hVa, hVc⟩ :=
    exists_open_between_and_isCompact_closure hF (isOpen_openCell a) hFa
  have hdisjoint : Disjoint Vᶜ F := by
    rw [Set.disjoint_left]
    exact fun x hx hxf ↦ hx (hFV hxf)
  obtain ⟨η, hηsmooth, hηrange, hηzero, hηone⟩ :=
    exists_contMDiff_zero_iff_one_iff_of_isClosed (I := 𝓘(ℝ, Coordinates d))
      (n := (⊤ : ℕ∞)) hVo.isClosed_compl hF.isClosed hdisjoint
  have hsupp : Function.support η ⊆ V := by
    intro x hx
    by_contra hnot
    exact hx ((hηzero x).1 hnot)
  refine ⟨{
    η := η
    smooth := contMDiff_iff_contDiff.mp hηsmooth
    nonneg := fun x ↦ (hηrange ⟨x, rfl⟩).1
    le_one := fun x ↦ (hηrange ⟨x, rfl⟩).2
    eq_one_iff := fun x ↦ (hηone x).symm
    compact := hVc.of_isClosed_subset isClosed_closure (closure_mono hsupp)
    support_inside := (closure_mono hsupp).trans hVa
  }⟩

end AmbiguityHoles.Local
