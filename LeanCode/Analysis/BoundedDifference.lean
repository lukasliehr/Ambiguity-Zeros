module

public import LeanCode.Analysis.Definitions

public section

noncomputable section

namespace AmbiguityHoles.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {f g w : E → ℂ}

theorem ambiguity_eq_outside_of_bounded_openZeros
    (hcont : Continuous (fun z : E × E ↦ ambiguity f z.1 z.2 - ambiguity g z.1 z.2))
    (hbounded : Bornology.IsBounded (openZeros w))
    (hprod : ∀ x ω, (ambiguity f x ω - ambiguity g x ω) * star (ambiguity w x ω) = 0) :
    ∃ R S : ℝ, ∀ x ω, R < ‖x‖ ∨ S < ‖ω‖ → ambiguity f x ω = ambiguity g x ω := by
  have hopen : IsOpen {z : E × E | ambiguity f z.1 z.2 - ambiguity g z.1 z.2 ≠ 0} :=
    isOpen_ne_fun hcont continuous_const
  have hsubset :
      {z : E × E | ambiguity f z.1 z.2 - ambiguity g z.1 z.2 ≠ 0} ⊆ openZeros w := by
    apply hopen.subset_interior_iff.mpr
    intro z hz
    exact star_eq_zero.mp ((mul_eq_zero.mp (hprod z.1 z.2)).resolve_left hz)
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E × E)).mp hbounded
  refine ⟨R, R, fun x ω houtside ↦ sub_eq_zero.mp ?_⟩
  by_contra hne
  have hb := hR (hsubset (show (x, ω) ∈ _ from hne))
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff] at hb
  exact houtside.elim (fun h ↦ (not_lt_of_ge hb.1) h) (fun h ↦ (not_lt_of_ge hb.2) h)

end AmbiguityHoles.Analysis
