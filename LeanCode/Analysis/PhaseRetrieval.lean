module

public import LeanCode.Analysis.Spectrogram
public import LeanCode.Analysis.BoundedDifference
public import LeanCode.Analysis.Rigidity
public import LeanCode.Analysis.Continuity

public section

noncomputable section
open MeasureTheory

namespace AmbiguityHoles.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A nonzero square integrable window with bounded open ambiguity zeros does phase retrieval. -/
theorem phase_retrieval_of_bounded_openZeros (w : E → ℂ) (hw : MemLp w 2 volume)
    (hne : ¬ w =ᵐ[volume] 0) (hbounded : Bornology.IsBounded (openZeros w)) :
    DoesPhaseRetrieval w := by
  intro f g hf hg heq
  have hprod (x ω : E) :
      (ambiguity f x ω - ambiguity g x ω) * star (ambiguity w x ω) = 0 := by
    rw [sub_mul, ambiguity_product_eq_of_stft_norm_eq hw hf hg heq x ω, sub_self]
  have hw0 : star (ambiguity w 0 0) ≠ 0 :=
    star_ne_zero.mpr (fun h ↦ hne ((ambiguity_zero_zero_eq_zero_iff hw).mp h))
  have h0 : ambiguity f 0 0 = ambiguity g 0 0 :=
    sub_eq_zero.mp ((mul_eq_zero.mp (hprod 0 0)).resolve_right hw0)
  have hcont : Continuous (fun z : E × E ↦ ambiguity f z.1 z.2 - ambiguity g z.1 z.2) :=
    (crossAmbiguity_continuous hf hf).sub (crossAmbiguity_continuous hg hg)
  exact phase_of_ambiguity_eq hf hg (ambiguity_eq_of_bounded_difference hf hg
    (ambiguity_eq_outside_of_bounded_openZeros hcont hbounded hprod) h0)

end AmbiguityHoles.Analysis
