module

public import LeanCode.Definitions

@[expose] public section

/-! The exact sign calculation for the dimension-one Laguerre--Gaussian certificate.
The Fourier eigenfunction identity is a separate analytic obligation.
-/

noncomputable section
open MeasureTheory

namespace AmbiguityHoles

def certificatePolynomial (u : ℝ) : ℝ := u ^ 3 - 9 * u ^ 2 + u + 11

def innerRadius : ℝ := Real.sqrt ((5 - Real.sqrt 14) / (2 * Real.pi))
def outerRadius : ℝ := Real.sqrt ((5 + Real.sqrt 14) / (2 * Real.pi))

theorem sqrt_fourteen_bounds : 0 < Real.sqrt 14 ∧ Real.sqrt 14 < 5 := by
  constructor
  · positivity
  · have hs : (Real.sqrt 14) ^ 2 = 14 := Real.sq_sqrt (by norm_num)
    have hp := Real.sqrt_nonneg (14 : ℝ)
    nlinarith

theorem certificatePolynomial_factorization (u : ℝ) :
    certificatePolynomial u =
      (u + 1) * (u - (5 - Real.sqrt 14)) * (u - (5 + Real.sqrt 14)) := by
  have hs : (Real.sqrt 14) ^ 2 = 14 := Real.sq_sqrt (by norm_num)
  unfold certificatePolynomial
  linear_combination (u + 1) * hs

theorem certificatePolynomial_negative_iff {u : ℝ} (hu : 0 ≤ u) :
    certificatePolynomial u < 0 ↔ 5 - Real.sqrt 14 < u ∧ u < 5 + Real.sqrt 14 := by
  have hpos : 0 < u + 1 := by linarith
  have hmul (v : ℝ) : (u + 1) * v < 0 ↔ v < 0 := by
    simpa using (mul_lt_mul_iff_right₀ hpos : (u + 1) * v < (u + 1) * 0 ↔ v < 0)
  rw [certificatePolynomial_factorization, mul_assoc, hmul, mul_neg_iff]
  have hs := sqrt_fourteen_bounds.1
  constructor
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · constructor <;> linarith
    · exfalso
      linarith
  · rintro ⟨h₁, h₂⟩
    exact Or.inl ⟨by linarith, by linarith⟩

theorem annular_radii : 0 < innerRadius ∧ innerRadius < outerRadius := by
  have hs := sqrt_fourteen_bounds
  have hp : 0 < 2 * Real.pi := by positivity
  constructor
  · exact Real.sqrt_pos.2 (div_pos (by linarith) hp)
  · apply Real.sqrt_lt_sqrt (le_of_lt (div_pos (by linarith) hp))
    exact (div_lt_div_iff_of_pos_right hp).2 (by linarith)

/-- The explicit real certificate h(z) = q(2π|z|²) exp(-π|z|²). -/
def annularCertificate {d : ℕ} (z : PhaseSpace d) : ℝ :=
  certificatePolynomial (2 * Real.pi * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)) *
    Real.exp (-Real.pi * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2))

theorem annularCertificate_continuous {d : ℕ} :
    Continuous (annularCertificate (d := d)) := by
  unfold annularCertificate certificatePolynomial
  fun_prop

theorem annularCertificate_zero {d : ℕ} :
    annularCertificate (0 : PhaseSpace d) = 11 := by
  norm_num [annularCertificate, certificatePolynomial]

/-- Only the sign geometry is dimension independent; the Fourier identity uses d = 1. -/
theorem annularCertificate_negative_set {d : ℕ} :
    {z : PhaseSpace d | annularCertificate z < 0} = annulus d innerRadius outerRadius := by
  ext z
  have hs := sqrt_fourteen_bounds
  have hp : 0 < 2 * Real.pi := by positivity
  have hz : 0 ≤ ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by positivity
  change certificatePolynomial (2 * Real.pi * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)) *
      Real.exp (-Real.pi * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)) < 0 ↔ _
  have hexp : 0 < Real.exp (-Real.pi * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)) := Real.exp_pos _
  have hmul (v : ℝ) :
      v * Real.exp (-Real.pi * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)) < 0 ↔ v < 0 := by
    simpa using (mul_lt_mul_iff_left₀ hexp :
      v * Real.exp (-Real.pi * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)) <
        0 * Real.exp (-Real.pi * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)) ↔ v < 0)
  rw [hmul, certificatePolynomial_negative_iff (mul_nonneg hp.le hz)]
  change _ ↔ Real.sqrt ((5 - Real.sqrt 14) / (2 * Real.pi)) <
      Real.sqrt (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) ∧
    Real.sqrt (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) <
      Real.sqrt ((5 + Real.sqrt 14) / (2 * Real.pi))
  rw [Real.sqrt_lt_sqrt_iff (le_of_lt (div_pos (by linarith) hp)),
    Real.sqrt_lt_sqrt_iff hz, div_lt_iff₀ hp, lt_div_iff₀ hp]
  simp only [mul_comm]

end AmbiguityHoles
