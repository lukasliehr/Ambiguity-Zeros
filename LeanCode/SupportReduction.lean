module

public import Mathlib

@[expose] public section

/-! The dimension-independent support argument in the proof of Theorem 1.1. -/

namespace AmbiguityHoles

theorem interior_zeroSet_eq_compl_tsupport
    {X : Type*} [TopologicalSpace X] (W : X → ℂ) :
    interior {z | W z = 0} = (tsupport W)ᶜ := by
  rw [tsupport, ← interior_compl]
  congr 1
  ext z
  simp

/-- The spectrogram identity forces the support of A(f) - A(g) into the
closure of the window's open zero set. No dimension assumption is needed. -/
theorem tsupport_sub_subset_closure_openZeros
    {X : Type*} [TopologicalSpace X] (F G W : X → ℂ)
    (hF : Continuous F) (hG : Continuous G)
    (hproduct : ∀ z, (F z - G z) * star (W z) = 0) :
    tsupport (fun z ↦ F z - G z) ⊆ closure (interior {z | W z = 0}) := by
  have hzero : Function.support W ⊆ {z | F z - G z = 0} := by
    intro z hz
    exact (mul_eq_zero.mp (hproduct z)).resolve_right (by simpa using hz)
  have hclosure : tsupport W ⊆ {z | F z - G z = 0} :=
    closure_minimal hzero (isClosed_eq (hF.sub hG) continuous_const)
  apply closure_mono
  rw [interior_zeroSet_eq_compl_tsupport]
  intro z hz hW
  exact hz (hclosure hW)

theorem compactSupport_sub_of_bounded_openZeros
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    (F G W : X → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hproduct : ∀ z, (F z - G z) * star (W z) = 0)
    (hbounded : Bornology.IsBounded (interior {z | W z = 0})) :
    HasCompactSupport (fun z ↦ F z - G z) :=
  (Metric.isCompact_of_isClosed_isBounded isClosed_closure hbounded.closure).of_isClosed_subset
    isClosed_closure (tsupport_sub_subset_closure_openZeros F G W hF hG hproduct)

end AmbiguityHoles
