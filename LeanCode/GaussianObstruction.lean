module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-! An alternative Fourier certificate for the existential annular obstruction.
Four Gaussians suffice; no general Laguerre eigenfunction theorem is needed.
-/

noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace AmbiguityHoles.GaussianObstruction

abbrev Plane := WithLp 2 (ℝ × ℝ)

theorem plane_finrank : Module.finrank ℝ Plane = 2 := by
  rw [(WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).finrank_eq]
  simp

def rotation : Plane ≃ₗᵢ[ℝ] Plane :=
  (LinearIsometryEquiv.withLpProdComm 2 ℝ ℝ ℝ).trans
    (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ ℝ)
      (LinearIsometryEquiv.neg ℝ))

theorem rotation_apply (z : Plane) : rotation z = WithLp.toLp 2 (z.snd, -z.fst) := rfl

def gaussian (a : ℝ) (z : Plane) : ℂ :=
  Complex.exp (-Real.pi * a * (‖z‖ : ℂ) ^ 2)

theorem gaussian_integrable {a : ℝ} (ha : 0 < a) : Integrable (gaussian a) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := Plane) (b := (Real.pi * a : ℝ)) (by simpa using mul_pos Real.pi_pos ha) 0 0
  convert h using 1
  ext z
  unfold gaussian
  congr 1
  push_cast
  ring

theorem fourier_gaussian {a : ℝ} (ha : 0 < a) (z : Plane) :
    𝓕 (gaussian a) z = (a⁻¹ : ℝ) * gaussian a⁻¹ z := by
  have h := fourier_gaussian_innerProductSpace (V := Plane)
    (b := (Real.pi * a : ℝ)) (by simpa using mul_pos Real.pi_pos ha) z
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [plane_finrank] at h
  norm_num at h
  have hfun : gaussian a = fun v : Plane ↦ Complex.exp (-(↑Real.pi * ↑a * (‖v‖ : ℂ) ^ 2)) := by
    funext v
    unfold gaussian
    congr 1
    ring
  rw [hfun, h]
  unfold gaussian
  push_cast
  congr 1
  · field_simp
  · congr 1
    field_simp


def certificate (z : Plane) : ℂ :=
  gaussian 2 z - (1 / 2 : ℂ) * gaussian (1 / 2) z -
    (1 / 4 : ℂ) * gaussian 4 z + (1 / 16 : ℂ) * gaussian (1 / 4) z

theorem gaussian_continuous (a : ℝ) : Continuous (gaussian a) := by
  unfold gaussian
  fun_prop

theorem certificate_continuous : Continuous certificate := by
  unfold certificate gaussian
  fun_prop

theorem certificate_integrable : Integrable certificate :=
  (((gaussian_integrable (by norm_num : (0 : ℝ) < 2)).sub
    ((gaussian_integrable (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _)).sub
    ((gaussian_integrable (by norm_num : (0 : ℝ) < 4)).const_mul _)).add
    ((gaussian_integrable (by norm_num : (0 : ℝ) < 1 / 4)).const_mul _)

theorem certificate_zero : certificate 0 = 5 / 16 := by
  norm_num [certificate, gaussian]

private theorem fourier_add_integrable {f g : Plane → ℂ}
    (hf : Integrable f) (hg : Integrable g) : 𝓕 (f + g) = 𝓕 f + 𝓕 g :=
  VectorFourier.fourierIntegral_add Real.continuous_fourierChar
    (by simpa using (continuous_fst.inner continuous_snd :
      Continuous fun p : Plane × Plane ↦ inner ℝ p.1 p.2)) hf hg

private theorem fourier_const_mul (c : ℂ) (f : Plane → ℂ) :
    𝓕 (fun z ↦ c * f z) = fun z ↦ c * 𝓕 f z :=
  VectorFourier.fourierIntegral_const_smul _ _ _ _ _

theorem fourier_certificate : 𝓕 certificate = -certificate := by
  have h₂ := gaussian_integrable (by norm_num : (0 : ℝ) < 2)
  have hh := gaussian_integrable (by norm_num : (0 : ℝ) < 1 / 2)
  have h₄ := gaussian_integrable (by norm_num : (0 : ℝ) < 4)
  have hq := gaussian_integrable (by norm_num : (0 : ℝ) < 1 / 4)
  have hc : certificate =
      ((gaussian 2 + (fun z ↦ (-1 / 2 : ℂ) * gaussian (1 / 2) z)) +
        (fun z ↦ (-1 / 4 : ℂ) * gaussian 4 z)) +
        (fun z ↦ (1 / 16 : ℂ) * gaussian (1 / 4) z) := by
    funext z
    simp only [certificate, Pi.add_apply]
    ring
  rw [hc, fourier_add_integrable ((h₂.add (hh.const_mul _)).add (h₄.const_mul _))
    (hq.const_mul _), fourier_add_integrable (h₂.add (hh.const_mul _)) (h₄.const_mul _),
    fourier_add_integrable h₂ (hh.const_mul _)]
  simp only [fourier_const_mul]
  funext z
  simp only [Pi.add_apply, Pi.neg_apply]
  rw [fourier_gaussian (by norm_num : (0 : ℝ) < 2),
    fourier_gaussian (by norm_num : (0 : ℝ) < 1 / 2),
    fourier_gaussian (by norm_num : (0 : ℝ) < 4),
    fourier_gaussian (by norm_num : (0 : ℝ) < 1 / 4)]
  norm_num
  ring

theorem gaussian_eq_real (a : ℝ) (z : Plane) :
    gaussian a z = (Real.exp (-Real.pi * a * ‖z‖ ^ 2) : ℂ) := by
  rw [Complex.ofReal_exp]
  unfold gaussian
  congr 1
  push_cast
  rfl

theorem certificate_real (z : Plane) :
    certificate z = (Complex.re (certificate z) : ℂ) := by
  apply Complex.ext
  · simp
  · simp only [certificate, gaussian_eq_real, Complex.add_im, Complex.sub_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    norm_num

theorem certificate_rotation (z : Plane) : certificate (rotation z) = certificate z := by
  simp [certificate, gaussian, rotation.norm_map]

theorem certificate_tail {z : Plane}
    (hz : 4 * Real.log 16 ≤ Real.pi * ‖z‖ ^ 2) : 0 ≤ (certificate z).re := by
  let s := Real.pi * ‖z‖ ^ 2
  have hs : 0 ≤ s := by positivity
  have hu : 0 < Real.exp (-s / 4) := Real.exp_pos _
  have hub : Real.exp (-s / 4) ≤ 1 / 16 := by
    calc
      Real.exp (-s / 4) ≤ Real.exp (-Real.log 16) :=
        Real.exp_le_exp.mpr (by dsimp [s]; linarith)
      _ = 1 / 16 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hsmall : Real.exp (-4 * s) ≤ Real.exp (-s / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hsq : Real.exp (-s / 2) = Real.exp (-s / 4) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hre : (certificate z).re = Real.exp (-2 * s) -
      1 / 2 * Real.exp (-s / 2) - 1 / 4 * Real.exp (-4 * s) +
      1 / 16 * Real.exp (-s / 4) := by
    simp only [certificate, gaussian_eq_real, Complex.add_re, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    norm_num
    dsimp [s]
    congr 3 <;> congr 1 <;> ring_nf
  rw [hre]
  have hp := Real.exp_pos (-2 * s)
  have hh : 0 ≤ Real.exp (-s / 4) * (1 / 16 - Real.exp (-s / 4)) :=
    mul_nonneg hu.le (sub_nonneg.mpr hub)
  rw [hsq] at hsmall ⊢
  nlinarith

end AmbiguityHoles.GaussianObstruction
