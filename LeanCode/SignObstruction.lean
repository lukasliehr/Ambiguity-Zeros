module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith

public section

/-! The positivity argument in Proposition `prop:certificate`, isolated from Fourier analysis. -/

open MeasureTheory

namespace AmbiguityHoles

/-- A nonnegative continuous density which is positive at one point cannot vanish on the
negative set of a continuous, orthogonal certificate that is positive at the same point. -/
theorem sign_obstruction
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {μ : Measure X} [Measure.IsOpenPosMeasure μ]
    (F h : X → ℝ) (x₀ : X)
    (hF : Continuous F) (hh : Continuous h)
    (hF_nonneg : ∀ x, 0 ≤ F x) (hF_pos : 0 < F x₀) (hh_pos : 0 < h x₀)
    (hint : Integrable (fun x ↦ F x * h x) μ)
    (horthogonal : ∫ x, F x * h x ∂μ = 0) :
    ¬ (∀ x, h x < 0 → F x = 0) := by
  intro hvanish
  have hnonneg : 0 ≤ fun x ↦ F x * h x := by
    intro x
    change 0 ≤ F x * h x
    by_cases hx : h x < 0
    · rw [hvanish x hx, zero_mul]
    · exact mul_nonneg (hF_nonneg x) (le_of_not_gt hx)
  have hpositive := integral_pos_of_integrable_nonneg_nonzero
    (hF.mul hh) hint hnonneg (ne_of_gt (mul_pos hF_pos hh_pos))
  change 0 < ∫ x, F x * h x ∂μ at hpositive
  linarith

end AmbiguityHoles
