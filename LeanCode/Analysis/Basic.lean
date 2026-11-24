module

public import LeanCode.Analysis.Definitions
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

public section

noncomputable section
open MeasureTheory

namespace AmbiguityHoles.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {f g f₁ f₂ g₁ g₂ : E → ℂ} {p : ENNReal}

theorem norm_fourierChar (a : ℝ) : ‖(Real.fourierChar a : ℂ)‖ = 1 :=
  Circle.norm_coe _

theorem translate_memLp (x : E) (hf : MemLp f p volume) :
    MemLp (translate x f) p volume := by
  change MemLp (fun t ↦ f (t - x)) p volume
  simpa [sub_eq_add_neg, Function.comp_def] using
    hf.comp_measurePreserving (MeasureTheory.measurePreserving_add_right volume (-x))

theorem modulate_memLp (ω : E) (hf : MemLp f p volume) :
    MemLp (modulate ω f) p volume := by
  have hmeas : AEStronglyMeasurable (modulate ω f) volume :=
    (continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (continuous_const.inner continuous_id))).aestronglyMeasurable.mul hf.aestronglyMeasurable
  have hnorm : eLpNorm (modulate ω f) p volume = eLpNorm f p volume :=
    eLpNorm_congr_norm_ae hmeas hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t ↦ by simp [modulate])
  rw [memLp_iff, hnorm]
  exact hf.eLpNorm_lt_top

theorem crossAmbiguity_integrand_integrable
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (x ω : E) :
    Integrable (fun t ↦ f (t + (1 / 2 : ℝ) • x) * star (g (t - (1 / 2 : ℝ) • x)) *
      (Real.fourierChar (-(inner ℝ ω t)) : ℂ)) volume := by
  have h₁ : MemLp (fun t ↦ f (t + (1 / 2 : ℝ) • x)) 2 volume := by
    simpa only [Function.comp_def] using
      hf.comp_measurePreserving (measurePreserving_add_right volume ((1 / 2 : ℝ) • x))
  have h₂ : MemLp (fun t ↦ star (g (t - (1 / 2 : ℝ) • x))) 2 volume :=
    (translate_memLp ((1 / 2 : ℝ) • x) hg).star
  exact (h₁.integrable_mul h₂).mul_bdd
    (continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      ((continuous_const.inner continuous_id).neg))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t ↦ le_of_eq (norm_fourierChar (-(inner ℝ ω t))))

theorem crossAmbiguity_add_left
    (hf₁ : MemLp f₁ 2 volume) (hf₂ : MemLp f₂ 2 volume) (hg : MemLp g 2 volume)
    (x ω : E) :
    crossAmbiguity (f₁ + f₂) g x ω = crossAmbiguity f₁ g x ω + crossAmbiguity f₂ g x ω := by
  have h1 : Integrable (fun t ↦ f₁ (t + (1 / 2 : ℝ) • x) * star (g (t - (1 / 2 : ℝ) • x)) *
      (Real.fourierChar (-(inner ℝ ω t)) : ℂ)) volume :=
    crossAmbiguity_integrand_integrable hf₁ hg x ω
  have h2 : Integrable (fun t ↦ f₂ (t + (1 / 2 : ℝ) • x) * star (g (t - (1 / 2 : ℝ) • x)) *
      (Real.fourierChar (-(inner ℝ ω t)) : ℂ)) volume :=
    crossAmbiguity_integrand_integrable hf₂ hg x ω
  simpa [crossAmbiguity, add_mul, mul_add, mul_assoc] using
    (MeasureTheory.integral_add h1 h2)

theorem crossAmbiguity_add_right
    (hf : MemLp f 2 volume) (hg₁ : MemLp g₁ 2 volume) (hg₂ : MemLp g₂ 2 volume)
    (x ω : E) :
    crossAmbiguity f (g₁ + g₂) x ω = crossAmbiguity f g₁ x ω + crossAmbiguity f g₂ x ω := by
  have h1 : Integrable (fun t ↦ f (t + (1 / 2 : ℝ) • x) * star (g₁ (t - (1 / 2 : ℝ) • x)) *
      (Real.fourierChar (-(inner ℝ ω t)) : ℂ)) volume :=
    crossAmbiguity_integrand_integrable hf hg₁ x ω
  have h2 : Integrable (fun t ↦ f (t + (1 / 2 : ℝ) • x) * star (g₂ (t - (1 / 2 : ℝ) • x)) *
      (Real.fourierChar (-(inner ℝ ω t)) : ℂ)) volume :=
    crossAmbiguity_integrand_integrable hf hg₂ x ω
  simpa [crossAmbiguity, add_mul, mul_add, mul_assoc] using
    (MeasureTheory.integral_add h1 h2)

theorem crossAmbiguity_smul_left (c : ℂ) (_hf : MemLp f 2 volume) (_hg : MemLp g 2 volume)
    (x ω : E) :
    crossAmbiguity (c • f) g x ω = c * crossAmbiguity f g x ω := by
  calc
    crossAmbiguity (c • f) g x ω
        = ∫ t, ((c • f) (t + (1 / 2 : ℝ) • x) * star (g (t - (1 / 2 : ℝ) • x)) *
            (Real.fourierChar (-(inner ℝ ω t)) : ℂ)) := by
            rfl
    _ = ∫ t, c * (f (t + (1 / 2 : ℝ) • x) * star (g (t - (1 / 2 : ℝ) • x)) *
            (Real.fourierChar (-(inner ℝ ω t)) : ℂ)) := by
            simp [smul_eq_mul, mul_assoc]
    _ = c * crossAmbiguity f g x ω := by
            simpa [crossAmbiguity, mul_assoc] using
              (MeasureTheory.integral_const_mul c
                (fun t ↦ f (t + (1 / 2 : ℝ) • x) * star (g (t - (1 / 2 : ℝ) • x)) *
                  (Real.fourierChar (-(inner ℝ ω t)) : ℂ)))

theorem crossAmbiguity_smul_right (c : ℂ) (_hf : MemLp f 2 volume) (_hg : MemLp g 2 volume)
    (x ω : E) :
    crossAmbiguity f (c • g) x ω = star c * crossAmbiguity f g x ω := by
  calc
    crossAmbiguity f (c • g) x ω
        = ∫ t, (f (t + (1 / 2 : ℝ) • x) * star ((c • g) (t - (1 / 2 : ℝ) • x)) *
            (Real.fourierChar (-(inner ℝ ω t)) : ℂ)) := by
            rfl
    _ = ∫ t, star c * (f (t + (1 / 2 : ℝ) • x) * star (g (t - (1 / 2 : ℝ) • x)) *
            (Real.fourierChar (-(inner ℝ ω t)) : ℂ)) := by
            simp [smul_eq_mul, mul_assoc, mul_left_comm]
    _ = star c * crossAmbiguity f g x ω := by
            simpa [crossAmbiguity, mul_assoc] using
              (MeasureTheory.integral_const_mul (star c)
                (fun t ↦ f (t + (1 / 2 : ℝ) • x) * star (g (t - (1 / 2 : ℝ) • x)) *
                  (Real.fourierChar (-(inner ℝ ω t)) : ℂ)))

theorem crossAmbiguity_sub_left
    (hf₁ : MemLp f₁ 2 volume) (hf₂ : MemLp f₂ 2 volume) (hg : MemLp g 2 volume)
    (x ω : E) :
    crossAmbiguity (f₁ - f₂) g x ω = crossAmbiguity f₁ g x ω - crossAmbiguity f₂ g x ω := by
  calc
    crossAmbiguity (f₁ - f₂) g x ω
        = crossAmbiguity (f₁ + -f₂) g x ω := by rfl
    _ = crossAmbiguity f₁ g x ω + crossAmbiguity (-f₂) g x ω := by
          simpa using
            crossAmbiguity_add_left (f₁ := f₁) (f₂ := -f₂) (g := g) hf₁ hf₂.neg hg
              x ω
    _ = crossAmbiguity f₁ g x ω - crossAmbiguity f₂ g x ω := by
          simpa [sub_eq_add_neg] using
            congrArg (fun z : ℂ ↦ crossAmbiguity f₁ g x ω + z)
              (crossAmbiguity_smul_left (f := f₂) (g := g) (-1 : ℂ) hf₂ hg x ω)

theorem crossAmbiguity_sub_right
    (hf : MemLp f 2 volume) (hg₁ : MemLp g₁ 2 volume) (hg₂ : MemLp g₂ 2 volume)
    (x ω : E) :
    crossAmbiguity f (g₁ - g₂) x ω = crossAmbiguity f g₁ x ω - crossAmbiguity f g₂ x ω := by
  calc
    crossAmbiguity f (g₁ - g₂) x ω
        = crossAmbiguity f (g₁ + -g₂) x ω := by rfl
    _ = crossAmbiguity f g₁ x ω + crossAmbiguity f (-g₂) x ω := by
          simpa using
            crossAmbiguity_add_right (f := f) (g₁ := g₁) (g₂ := -g₂) hf hg₁ hg₂.neg
              x ω
    _ = crossAmbiguity f g₁ x ω - crossAmbiguity f g₂ x ω := by
          simpa [sub_eq_add_neg] using
            congrArg (fun z : ℂ ↦ crossAmbiguity f g₁ x ω + z)
              (crossAmbiguity_smul_right (f := f) (g := g₂) (-1 : ℂ) hf hg₂ x ω)

theorem ambiguity_add (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (x ω : E) :
    ambiguity (f + g) x ω =
      ambiguity f x ω + crossAmbiguity f g x ω + crossAmbiguity g f x ω + ambiguity g x ω := by
  have hfg : MemLp (f + g) 2 volume := hf.add hg
  calc
    ambiguity (f + g) x ω = crossAmbiguity (f + g) (f + g) x ω := rfl
    _ = crossAmbiguity f (f + g) x ω + crossAmbiguity g (f + g) x ω := by
      simpa using
        (crossAmbiguity_add_left (f₁ := f) (f₂ := g) (g := f + g) hf hg hfg x ω)
    _ = (crossAmbiguity f f x ω + crossAmbiguity f g x ω) +
        (crossAmbiguity g f x ω + crossAmbiguity g g x ω) := by
      rw [crossAmbiguity_add_right (f := f) (g₁ := f) (g₂ := g) hf hf hg x ω,
        crossAmbiguity_add_right (f := g) (g₁ := f) (g₂ := g) hg hf hg x ω]
    _ = ambiguity f x ω + crossAmbiguity f g x ω + crossAmbiguity g f x ω + ambiguity g x ω := by
      simp [ambiguity, add_assoc]

theorem crossAmbiguity_zero_left (_hg : MemLp g 2 volume) (x ω : E) :
    crossAmbiguity 0 g x ω = 0 := by
  simp [crossAmbiguity]

theorem crossAmbiguity_zero_right (_hf : MemLp f 2 volume) (x ω : E) :
    crossAmbiguity f 0 x ω = 0 := by
  simp [crossAmbiguity]

theorem crossAmbiguity_zero_zero (_hf : MemLp f 2 volume) (_hg : MemLp g 2 volume) :
    crossAmbiguity f g 0 0 = ∫ t, f t * star (g t) := by
  simp [crossAmbiguity]

theorem ambiguity_zero (x ω : E) :
    ambiguity 0 x ω = 0 := by
  simp [ambiguity, crossAmbiguity]


theorem conj_memLp (hf : MemLp f p volume) :
    MemLp (fun t ↦ star (f t)) p volume := hf.star

theorem integrable_mul_of_memLp (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun t ↦ f t * g t) volume := hf.integrable_mul hg

theorem crossAmbiguity_congr_ae
    (_hf₁ : MemLp f₁ 2 volume) (_hf₂ : MemLp f₂ 2 volume)
    (_hg₁ : MemLp g₁ 2 volume) (_hg₂ : MemLp g₂ 2 volume)
    (hff : f₁ =ᵐ[volume] f₂) (hgg : g₁ =ᵐ[volume] g₂) (x ω : E) :
    crossAmbiguity f₁ g₁ x ω = crossAmbiguity f₂ g₂ x ω := by
  have h₁ := (measurePreserving_add_right volume ((1 / 2 : ℝ) • x)).quasiMeasurePreserving.ae_eq_comp hff
  have h₂ := (measurePreserving_add_right volume (-((1 / 2 : ℝ) • x))).quasiMeasurePreserving.ae_eq_comp hgg
  apply integral_congr_ae
  filter_upwards [h₁, h₂] with t ht₁ ht₂
  dsimp [Function.comp_def] at ht₁ ht₂
  simp only [sub_eq_add_neg, ht₁, ht₂]

theorem ambiguity_congr_ae
    (hf₁ : MemLp f₁ 2 volume) (hf₂ : MemLp f₂ 2 volume)
    (hff : f₁ =ᵐ[volume] f₂) (x ω : E) :
    ambiguity f₁ x ω = ambiguity f₂ x ω :=
  crossAmbiguity_congr_ae hf₁ hf₂ hf₁ hf₂ hff hff x ω

theorem star_fourierChar (a : ℝ) :
    star (Real.fourierChar a : ℂ) = (Real.fourierChar (-a) : ℂ) := by
  rw [Real.fourierChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj _).symm

theorem crossAmbiguity_neg_neg (_hf : MemLp f 2 volume) (_hg : MemLp g 2 volume)
    (x ω : E) :
    crossAmbiguity f g (-x) (-ω) = star (crossAmbiguity g f x ω) := by
  unfold crossAmbiguity
  let k : E → ℂ := fun t ↦ g (t + (1 / 2 : ℝ) • x) * star (f (t - (1 / 2 : ℝ) • x)) *
    (Real.fourierChar (-(inner ℝ ω t)) : ℂ)
  calc
    _ = ∫ t, star (k t) := by
      apply integral_congr_ae
      filter_upwards with t
      simp [k, star_mul, sub_eq_add_neg, mul_comm]
    _ = _ := integral_conj (f := k)

theorem ambiguity_neg_neg (hf : MemLp f 2 volume) (x ω : E) :
    ambiguity f (-x) (-ω) = star (ambiguity f x ω) :=
  crossAmbiguity_neg_neg hf hf x ω

theorem fourierChar_add (a b : ℝ) :
    (Real.fourierChar (a + b) : ℂ) = (Real.fourierChar a : ℂ) * (Real.fourierChar b : ℂ) := by
  exact congrArg (fun z : Circle ↦ (z : ℂ)) (Real.fourierChar.map_add_eq_mul a b)

theorem crossAmbiguity_translate_translate
    (_hf : MemLp f 2 volume) (_hg : MemLp g 2 volume) (a b x ω : E) :
    crossAmbiguity (translate a f) (translate b g) x ω =
      (Real.fourierChar (-(inner ℝ ω ((1 / 2 : ℝ) • (a + b)))) : ℂ) *
        crossAmbiguity f g (x - (a - b)) ω := by
  unfold crossAmbiguity
  let k : E → ℂ := fun t ↦ f (t + (1 / 2 : ℝ) • x - a) *
    star (g (t - (1 / 2 : ℝ) • x - b)) * (Real.fourierChar (-(inner ℝ ω t)) : ℂ)
  change (∫ t, k t) = _
  rw [← integral_add_right_eq_self (f := k) ((1 / 2 : ℝ) • (a + b))]
  let R : E → ℂ := fun t ↦ f (t + (1 / 2 : ℝ) • (x - (a - b))) *
    star (g (t - (1 / 2 : ℝ) • (x - (a - b)))) * (Real.fourierChar (-(inner ℝ ω t)) : ℂ)
  refine Eq.trans ?_ (integral_const_mul (μ := (volume : Measure E))
    (Real.fourierChar (-(inner ℝ ω ((1 / 2 : ℝ) • (a + b)))) : ℂ) R)
  apply integral_congr_ae
  filter_upwards with t
  have hl : t + (1 / 2 : ℝ) • (a + b) + (1 / 2 : ℝ) • x - a =
      t + (1 / 2 : ℝ) • (x - (a - b)) := by module
  have hr : t + (1 / 2 : ℝ) • (a + b) - (1 / 2 : ℝ) • x - b =
      t - (1 / 2 : ℝ) • (x - (a - b)) := by module
  simp only [R, k, hl, hr, inner_add_right, neg_add, fourierChar_add]
  ring

theorem crossAmbiguity_modulate_modulate (a b x ω : E) :
    crossAmbiguity (modulate a f) (modulate b g) x ω =
      (Real.fourierChar (inner ℝ (a + b) ((1 / 2 : ℝ) • x)) : ℂ) *
        crossAmbiguity f g x (ω - (a - b)) := by
  unfold crossAmbiguity modulate
  let R : E → ℂ := fun t ↦ f (t + (1 / 2 : ℝ) • x) *
    star (g (t - (1 / 2 : ℝ) • x)) * (Real.fourierChar (-(inner ℝ (ω - (a - b)) t)) : ℂ)
  refine Eq.trans ?_ (integral_const_mul (μ := (volume : Measure E))
    (Real.fourierChar (inner ℝ (a + b) ((1 / 2 : ℝ) • x)) : ℂ) R)
  apply integral_congr_ae
  filter_upwards with t
  simp only [R, star_mul, star_fourierChar]
  calc
    _ = ((Real.fourierChar (inner ℝ a (t + (1 / 2 : ℝ) • x)) : ℂ) *
        Real.fourierChar (-(inner ℝ b (t - (1 / 2 : ℝ) • x))) *
        Real.fourierChar (-(inner ℝ ω t))) *
          (f (t + (1 / 2 : ℝ) • x) * star (g (t - (1 / 2 : ℝ) • x))) := by ring
    _ = _ := by
      have harg : inner ℝ a (t + (1 / 2 : ℝ) • x) + -(inner ℝ b (t - (1 / 2 : ℝ) • x)) +
          -(inner ℝ ω t) =
          inner ℝ (a + b) ((1 / 2 : ℝ) • x) + -(inner ℝ (ω - (a - b)) t) := by
        simp only [inner_add_right, inner_sub_right, inner_add_left, inner_sub_left]
        ring
      rw [← fourierChar_add, ← fourierChar_add, harg, fourierChar_add]
      ring

end AmbiguityHoles.Analysis
