import LeanCode.Definitions
import AmbiguityZeros.ToMathlib.STFT

noncomputable section
open MeasureTheory

namespace AmbiguityHoles

def realLine : ℝ ≃ₗᵢ[ℝ] Rd 1 := (OrthonormalBasis.singleton (Fin 1) ℝ).repr

def realPhaseSpace : (ℝ × ℝ) ≃L[ℝ] PhaseSpace 1 :=
  realLine.toContinuousLinearEquiv.prodCongr realLine.toContinuousLinearEquiv

theorem fourierChar_eq_exp (ω t : ℝ) :
    (Real.fourierChar (-(ω * t)) : ℂ) =
      Complex.exp (-2 * Real.pi * Complex.I * (inner ℝ ω t : ℝ)) := by
  rw [Real.fourierChar_apply]
  congr 1
  rw [show inner ℝ ω t = t * ω from rfl]
  simp only [Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_ofNat]
  ring

theorem ambiguity_realLine (f : L2 1) (x ω : ℝ) :
    AmbiguityZeros.ToMathlib.ambiguity (fun t ↦ f (realLine t)) x ω =
      ambiguity f (realLine x, realLine ω) := by
  unfold AmbiguityZeros.ToMathlib.ambiguity AmbiguityZeros.ToMathlib.crossAmbiguity ambiguity
  rw [← realLine.measurePreserving.integral_comp
    realLine.toMeasurableEquiv.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [map_add, map_sub, realLine.inner_map_map, fourierChar_eq_exp]
  congr 3 <;> rw [show x / 2 = (1 / 2 : ℝ) • x by simp [smul_eq_mul]; ring, map_smul]

theorem stft_realLine (w f : L2 1) (x ω : ℝ) :
    AmbiguityZeros.ToMathlib.stft (fun t ↦ w (realLine t)) (fun t ↦ f (realLine t)) x ω =
      stft w f (realLine x, realLine ω) := by
  unfold AmbiguityZeros.ToMathlib.stft stft
  rw [← realLine.measurePreserving.integral_comp
    realLine.toMeasurableEquiv.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [map_sub, realLine.inner_map_map, fourierChar_eq_exp]

end AmbiguityHoles
