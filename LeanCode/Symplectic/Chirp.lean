module

public import LeanCode.Analysis.Definitions
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open MeasureTheory

namespace AmbiguityHoles.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def chirp (M : E →L[ℝ] E) (f : E → ℂ) : E → ℂ :=
  fun t ↦ (Real.fourierChar (inner ℝ (M t) t / 2) : ℂ) * f t

theorem exists_symmetric_map {x : E} (hx : x ≠ 0) (y : E) :
    ∃ M : E →L[ℝ] E, (∀ a b, inner ℝ (M a) b = inner ℝ a (M b)) ∧ M x = y := by
  let u : E := (inner ℝ x x)⁻¹ • x
  have hux : inner ℝ u x = 1 := by
    dsimp [u]
    rw [real_inner_smul_left, inv_mul_cancel₀ (inner_self_eq_zero.not.mpr hx)]
  let M : E →L[ℝ] E := (innerSL ℝ u).smulRight y + (innerSL ℝ y).smulRight u -
    (inner ℝ y x) • (innerSL ℝ u).smulRight u
  have hM (t : E) : M t = inner ℝ u t • y + inner ℝ y t • u -
      (inner ℝ y x) • (inner ℝ u t • u) := by
    simp [M, innerSL_apply_apply]
  refine ⟨M, ?_, ?_⟩
  · intro a b
    rw [hM a, hM b]
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm u a, real_inner_comm y a]
    ring
  · simp [hM, hux]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem memLp_chirp (M : E →L[ℝ] E) {f : E → ℂ} (hf : MemLp f 2 volume) :
    MemLp (chirp M f) 2 volume := by
  have h : Continuous (fun t ↦ (Real.fourierChar (inner ℝ (M t) t / 2) : ℂ)) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      ((M.continuous.inner continuous_id).div_const 2))
  refine hf.congr_norm (h.aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun t ↦ by simp [chirp, norm_mul, Circle.norm_coe]

private theorem char_add (a b : ℝ) :
    (Real.fourierChar (a + b) : ℂ) =
      (Real.fourierChar a : ℂ) * (Real.fourierChar b : ℂ) :=
  congrArg (fun z : Circle ↦ (z : ℂ)) (Real.fourierChar.map_add_eq_mul' a b)

theorem ambiguity_chirp (M : E →L[ℝ] E)
    (hM : ∀ a b, inner ℝ (M a) b = inner ℝ a (M b))
    (f : E → ℂ) (x ω : E) :
    ambiguity (chirp M f) x ω = ambiguity f x (ω - M x) := by
  unfold ambiguity crossAmbiguity
  apply integral_congr_ae
  filter_upwards with t
  let a := inner ℝ (M (t + (1 / 2 : ℝ) • x)) (t + (1 / 2 : ℝ) • x) / 2
  let b := inner ℝ (M (t - (1 / 2 : ℝ) • x)) (t - (1 / 2 : ℝ) • x) / 2
  have hphase : a + -b + -(inner ℝ ω t) = -(inner ℝ (ω - M x) t) := by
    dsimp [a, b]
    simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    rw [hM t x, real_inner_comm (M x) t]
    ring
  have hstar : star (Real.fourierChar b : ℂ) = (Real.fourierChar (-b) : ℂ) := by
    rw [Real.fourierChar.map_neg_eq_inv, Circle.coe_inv_eq_conj] <;> rfl
  simp only [chirp, star_mul]
  change ((Real.fourierChar a : ℂ) * f _) *
    (star (f _) * star (Real.fourierChar b : ℂ)) * _ = _
  rw [hstar, ← hphase, char_add, char_add]
  ring

end AmbiguityHoles.Analysis
