module

public import LeanCode.Analysis.Definitions
public import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

public section

noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform

namespace AmbiguityHoles.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[expose] abbrev L2 (E : Type*) [MeasurableSpace E] [MeasureSpace E] :=
  MeasureTheory.Lp (α := E) ℂ 2 volume

@[expose] def l2Fourier (f : E → ℂ) (hf : MemLp f 2 volume) : E → ℂ :=
  (𝓕 (hf.toLp f) : L2 E)

theorem l2Fourier_memLp (f : E → ℂ) (hf : MemLp f 2 volume) :
    MemLp (l2Fourier f hf) 2 volume :=
  Lp.memLp _

private theorem char_mul (a b : ℝ) :
    (Real.fourierChar a : ℂ) * Real.fourierChar b = Real.fourierChar (a + b) := by
  rw [Real.fourierChar.map_add_eq_mul, Circle.coe_mul]

private theorem char_star (a : ℝ) :
    star (Real.fourierChar a : ℂ) = Real.fourierChar (-a) := by
  rw [Real.fourierChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj _).symm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem char_cont (ω : E) :
    Continuous (fun t : E ↦ (Real.fourierChar (inner ℝ ω t) : ℂ)) :=
  continuous_subtype_val.comp (Real.continuous_fourierChar.comp (continuous_const.inner continuous_id))

private theorem translate_mem {f : E → ℂ} (x : E) (hf : MemLp f 2 volume) :
    MemLp (translate x f) 2 volume :=
  hf.comp_measurePreserving (measurePreserving_sub_right volume x)

private theorem modulate_mem {f : E → ℂ} (ω : E) (hf : MemLp f 2 volume) :
    MemLp (modulate ω f) 2 volume := by
  refine ⟨(char_cont ω).aestronglyMeasurable.mul hf.1, ?_⟩
  convert hf.2 using 1
  apply eLpNorm_congr_norm_ae
  exact Filter.Eventually.of_forall fun t ↦ by simp [modulate]

@[expose] def translation (x : E) : L2 E →ₗᵢ[ℂ] L2 E :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun t : E ↦ t - x) (measurePreserving_sub_right volume x)

def modulation (ω : E) (g : L2 E) : L2 E :=
  (modulate_mem ω (Lp.memLp g)).toLp (modulate ω g)

private theorem translation_toLp {f : E → ℂ} (x : E) (hf : MemLp f 2 volume) :
    translation x (hf.toLp f) = (translate_mem x hf).toLp (translate x f) :=
  rfl

private theorem modulation_toLp {f : E → ℂ} (ω : E) (hf : MemLp f 2 volume) :
    modulation ω (hf.toLp f) = (modulate_mem ω hf).toLp (modulate ω f) := by
  apply MemLp.toLp_congr
  filter_upwards [hf.coeFn_toLp] with t ht
  simp [modulate, ht]

theorem continuous_modulation (ω : E) : Continuous (modulation ω : L2 E → L2 E) := by
  refine (show Isometry (modulation ω : L2 E → L2 E) from ?_).continuous
  apply Isometry.of_dist_eq
  intro f g
  simp only [dist_eq_norm, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [Lp.coeFn_sub (modulation ω f) (modulation ω g), Lp.coeFn_sub f g,
    (modulate_mem ω (Lp.memLp f)).coeFn_toLp,
    (modulate_mem ω (Lp.memLp g)).coeFn_toLp] with t h₁ h₂ hf hg
  change _ = ‖(f - g) t‖
  rw [h₁, h₂]
  change ‖modulation ω f t - modulation ω g t‖ = ‖f t - g t‖
  change modulation ω f t = _ at hf
  change modulation ω g t = _ at hg
  rw [hf, hg]
  simp [modulate, ← mul_sub]

private theorem fourier_translate (x : E) (f : E → ℂ) :
    𝓕 (translate x f) = modulate (-x) (𝓕 f) := by
  have h := VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume (innerₗ E) f (-x)
  funext w
  have h₁ := congrFun h w
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ E) (translate x f) w =
    modulate (-x) (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ E) f) w
  rw [show translate x f = f ∘ (fun v ↦ v + -x) by funext v; simp [translate, sub_eq_add_neg]]
  simpa [modulate, innerₗ_apply_apply, Circle.smul_def] using h₁

private theorem fourier_modulate (ω : E) (f : E → ℂ) :
    𝓕 (modulate ω f) = translate ω (𝓕 f) := by
  ext t
  rw [Real.fourier_eq, translate, Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [Circle.smul_def, smul_eq_mul, modulate, ← mul_assoc, char_mul]
  congr 2
  rw [inner_sub_right, real_inner_comm ω v]
  simp [sub_eq_add_neg, add_comm]

private theorem translate_schwartz (x : E) (s : SchwartzMap E ℂ) :
    translation x (s.toLp 2 volume) = (s.compSubConstCLM ℂ x).toLp 2 volume :=
  rfl

private theorem modulate_schwartz (ω : E) (s : SchwartzMap E ℂ) :
    ∃ r : SchwartzMap E ℂ, (r : E → ℂ) = modulate ω s := by
  refine ⟨𝓕 ((𝓕⁻ s : SchwartzMap E ℂ).compSubConstCLM ℂ (-ω)), ?_⟩
  have h := fourier_translate (-ω) (𝓕⁻ s : SchwartzMap E ℂ)
  rw [SchwartzMap.fourier_coe]
  change 𝓕 (translate (-ω) (𝓕⁻ s : SchwartzMap E ℂ)) = modulate ω s
  rw [h, neg_neg, ← SchwartzMap.fourier_coe, fourier_fourierInv_eq]

private theorem fourier_translation (x : E) (f : L2 E) :
    𝓕 (translation x f) = modulation (-x) (𝓕 f) := by
  refine DenseRange.induction_on
    (p := fun g : L2 E ↦ 𝓕 (translation x g) = modulation (-x) (𝓕 g))
    (SchwartzMap.denseRange_toLpCLM (p := (2 : ENNReal)) ENNReal.ofNat_ne_top) f ?_ ?_
  · exact isClosed_eq (FourierTransform.continuous_fourier.comp (translation x).continuous)
      ((continuous_modulation (-x)).comp FourierTransform.continuous_fourier)
  intro s
  change 𝓕 (translation x (s.toLp 2 volume)) = modulation (-x) (𝓕 (s.toLp 2 volume))
  rw [translate_schwartz, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  have hmod : modulation (-x) ((𝓕 s).toLp 2 volume) =
      (modulate_mem (-x) ((𝓕 s).memLp 2 volume)).toLp (modulate (-x) (𝓕 s : SchwartzMap E ℂ)) :=
    modulation_toLp (-x) ((𝓕 s).memLp 2 volume)
  rw [hmod]
  apply MemLp.toLp_congr
  apply Filter.Eventually.of_forall
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  exact congrFun (fourier_translate x s)

theorem fourier_modulation (ω : E) (f : L2 E) :
    𝓕 (modulation ω f) = translation ω (𝓕 f) := by
  refine DenseRange.induction_on
    (p := fun g : L2 E ↦ 𝓕 (modulation ω g) = translation ω (𝓕 g))
    (SchwartzMap.denseRange_toLpCLM (p := (2 : ENNReal)) ENNReal.ofNat_ne_top) f ?_ ?_
  · exact isClosed_eq (FourierTransform.continuous_fourier.comp (continuous_modulation ω))
      ((translation ω).continuous.comp FourierTransform.continuous_fourier)
  intro s
  obtain ⟨r, hr⟩ := modulate_schwartz ω s
  change 𝓕 (modulation ω (s.toLp 2 volume)) = translation ω (𝓕 (s.toLp 2 volume))
  have hmod : modulation ω (s.toLp 2 volume) =
      (modulate_mem ω (s.memLp 2 volume)).toLp (modulate ω s) :=
    modulation_toLp ω (s.memLp 2 volume)
  rw [hmod]
  have h : (modulate_mem ω (s.memLp 2 volume)).toLp (modulate ω s) = r.toLp 2 volume :=
    MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (congrFun hr.symm))
  rw [h, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  have htrans : translation ω ((𝓕 s).toLp 2 volume) =
      (translate_mem ω ((𝓕 s).memLp 2 volume)).toLp (translate ω (𝓕 s : SchwartzMap E ℂ)) :=
    translation_toLp ω ((𝓕 s).memLp 2 volume)
  rw [htrans]
  apply MemLp.toLp_congr
  apply Filter.Eventually.of_forall
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, hr]
  exact congrFun (fourier_modulate ω s)

theorem crossAmbiguity_inner {f g : E → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (x ω : E) :
    crossAmbiguity f g x ω = (Real.fourierChar ((1 / 2 : ℝ) * inner ℝ ω x) : ℂ) *
      inner ℂ (modulation ω (translation x (hg.toLp g))) (hf.toLp f) := by
  rw [translation_toLp, modulation_toLp, L2.inner_def, ← integral_const_mul]
  unfold crossAmbiguity
  let a : E := (1 / 2 : ℝ) • x
  let F : E → ℂ := fun t ↦ f (t + a) * star (g (t - a)) *
    (Real.fourierChar (-(inner ℝ ω t)) : ℂ)
  change (∫ t, F t) = _
  rw [← integral_add_right_eq_self F (-a)]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,
    (modulate_mem ω (translate_mem x hg)).coeFn_toLp] with t hft hgt
  change hf.toLp f t = f t at hft
  change _ = modulate ω (translate x g) t at hgt
  rw [hft, hgt]
  have ha : a + a = x := by
    dsimp [a]
    rw [← add_smul]
    norm_num
  have h₁ : t + -a + a = t := by abel
  have h₂ : t + -a - a = t - x := by rw [← ha]; abel
  have h₃ : -(inner ℝ ω (t + -a)) =
      (1 / 2 : ℝ) * inner ℝ ω x + -(inner ℝ ω t) := by
    simp [a, inner_add_right, real_inner_smul_right]
  dsimp only [F]
  rw [h₁, h₂, h₃, ← char_mul]
  simp only [RCLike.inner_apply, modulate, translate, map_mul, starRingEnd_apply, char_star]
  ring

private theorem translation_modulation (x ω : E) (f : L2 E) :
    translation x (modulation ω f) =
      (Real.fourierChar (-(inner ℝ ω x)) : ℂ) • modulation ω (translation x f) := by
  let h := Lp.memLp f
  have he : h.toLp (f : E → ℂ) = f := Lp.ext h.coeFn_toLp
  rw [← he, modulation_toLp, translation_toLp, translation_toLp, modulation_toLp]
  apply Lp.ext
  filter_upwards [(translate_mem x (modulate_mem ω h)).coeFn_toLp,
    (modulate_mem ω (translate_mem x h)).coeFn_toLp,
    Lp.coeFn_smul (Real.fourierChar (-(inner ℝ ω x)) : ℂ)
      ((modulate_mem ω (translate_mem x h)).toLp (modulate ω (translate x f)))] with
    t ht hm hs
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hs]
  change _ = translate x (modulate ω f) t at ht
  change _ = modulate ω (translate x f) t at hm
  rw [ht, hm]
  simp only [translate, modulate, ← mul_assoc, char_mul, inner_sub_right]
  congr 2
  rw [sub_eq_add_neg, add_comm]

theorem crossAmbiguity_fourier {f g : E → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (x ω : E) :
    crossAmbiguity (l2Fourier f hf) (l2Fourier g hg) x ω = crossAmbiguity f g (-ω) x := by
  have hf' : (l2Fourier_memLp f hf).toLp (l2Fourier f hf) = 𝓕 (hf.toLp f) :=
    Lp.ext (l2Fourier_memLp f hf).coeFn_toLp
  have hg' : (l2Fourier_memLp g hg).toLp (l2Fourier g hg) = 𝓕 (hg.toLp g) :=
    Lp.ext (l2Fourier_memLp g hg).coeFn_toLp
  rw [crossAmbiguity_inner (l2Fourier_memLp f hf) (l2Fourier_memLp g hg),
    crossAmbiguity_inner hf hg, hf', hg', ← fourier_modulation]
  rw [show modulation ω (𝓕 (modulation x (hg.toLp g))) =
      𝓕 (translation (-ω) (modulation x (hg.toLp g))) by rw [fourier_translation, neg_neg]]
  rw [Lp.inner_fourier_eq, translation_modulation, inner_smul_left]
  rw [starRingEnd_apply, char_star, ← mul_assoc, char_mul]
  congr 2
  rw [inner_neg_right, real_inner_comm x ω]
  ring

theorem ambiguity_fourier {f : E → ℂ} (hf : MemLp f 2 volume) (x ω : E) :
    ambiguity (l2Fourier f hf) x ω = ambiguity f (-ω) x :=
  crossAmbiguity_fourier hf hf x ω

end AmbiguityHoles.Analysis
