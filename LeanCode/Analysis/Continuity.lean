module

public import LeanCode.Analysis.Fourier
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.Tactic.FunProp

@[expose] public section

noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace AmbiguityHoles.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem continuous_translation_apply :
    Continuous (fun q : E × L2 E ↦ translation q.1 q.2) := by
  let shifts : E × L2 E → C(E, E) := fun q ↦ ⟨fun t ↦ t - q.1, continuous_id.sub continuous_const⟩
  have hshifts : Continuous shifts := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_snd.sub continuous_fst.fst
  exact continuous_snd.compMeasurePreservingLp hshifts
    (fun q ↦ measurePreserving_sub_right volume q.1) ENNReal.ofNat_ne_top

theorem modulation_eq_fourierInv_translation (ω : E) (f : L2 E) :
    modulation ω f = 𝓕⁻ (translation ω (𝓕 f)) := by
  simpa using congrArg FourierTransform.fourierInv (fourier_modulation ω f)

theorem continuous_modulation_apply :
    Continuous (fun q : E × L2 E ↦ modulation q.1 q.2) := by
  have h : Continuous (fun q : E × L2 E ↦ translation q.1 (𝓕 q.2)) :=
    continuous_translation_apply.comp
      (continuous_fst.prodMk (FourierTransform.continuous_fourier.comp continuous_snd))
  simp only [modulation_eq_fourierInv_translation]
  exact FourierTransform.continuous_fourierInv.comp h

theorem crossAmbiguity_continuous {f g : E → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Continuous (fun z : E × E ↦ crossAmbiguity f g z.1 z.2) := by
  simp_rw [crossAmbiguity_inner hf hg]
  apply Continuous.mul
  · exact continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (continuous_const.mul (continuous_snd.inner continuous_fst)))
  · apply Continuous.inner _ continuous_const
    exact continuous_modulation_apply.comp
      (continuous_snd.prodMk (continuous_translation_apply.comp
        (continuous_fst.prodMk continuous_const)))

theorem ambiguity_continuous {f : E → ℂ} (hf : MemLp f 2 volume) :
    Continuous (fun z : E × E ↦ ambiguity f z.1 z.2) :=
  crossAmbiguity_continuous hf hf

theorem continuous_ambiguity_eval (x ω : E) :
    Continuous (fun f : Lp ℂ 2 (volume : Measure E) ↦ ambiguity (f : E → ℂ) x ω) := by
  have hrepr (f : L2 E) :
      ambiguity (f : E → ℂ) x ω =
        (Real.fourierChar ((1 / 2 : ℝ) * inner ℝ ω x) : ℂ) *
          inner ℂ (modulation ω (translation x f)) f := by
    have h := crossAmbiguity_inner (Lp.memLp f) (Lp.memLp f) x ω
    have he : (Lp.memLp f).toLp (f : E → ℂ) = f := Lp.ext (Lp.memLp f).coeFn_toLp
    simpa only [ambiguity, he] using h
  simp_rw [hrepr]
  exact continuous_const.mul
    (((continuous_modulation ω).comp (translation x).continuous).inner continuous_id)

end AmbiguityHoles.Analysis
