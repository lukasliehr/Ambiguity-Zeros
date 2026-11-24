module

public import LeanCode.AmbiguityFourier
public import LeanCode.SignObstruction
public import LeanCode.RealLine

@[expose] public section

/-! Theorem 1.3: a nonzero ambiguity function cannot vanish on an entire annulus. -/

noncomputable section
open MeasureTheory

namespace AmbiguityHoles.GaussianObstruction

theorem certificate_negative_contained :
    ∃ r R : ℝ, 0 < r ∧ r < R ∧
      ∀ z : Plane, (certificate z).re < 0 → r < ‖z‖ ∧ ‖z‖ < R := by
  have hnear : ∀ᶠ z in nhds (0 : Plane), 0 < (certificate z).re :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp certificate_continuous)).eventually_mem
      (by change 0 < (certificate (0 : Plane)).re; rw [certificate_zero]; norm_num)
  obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hnear
  let c : ℝ := 4 * Real.log 16 / Real.pi
  have hc : 0 ≤ c := by
    exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))) Real.pi_pos.le
  let r := ε / 2
  let R := max (r + 1) (c + 1)
  have hr : 0 < r := half_pos hε
  have hrR : r < R := lt_of_lt_of_le (by dsimp [r]; linarith) (le_max_left _ _)
  refine ⟨r, R, hr, hrR, ?_⟩
  intro z hz
  constructor
  · by_contra hn
    have hn' : ‖z‖ ≤ r := le_of_not_gt hn
    have hp := hnear (y := z) (by rw [dist_zero_right]; dsimp [r] at hn'; linarith)
    linarith
  · by_contra hn
    have hlarge : c + 1 ≤ ‖z‖ := le_trans (le_max_right _ _) (le_of_not_gt hn)
    have hs : c ≤ ‖z‖ ^ 2 := by nlinarith [sq_nonneg (‖z‖ - 1)]
    have htail : 4 * Real.log 16 ≤ Real.pi * ‖z‖ ^ 2 := by
      simpa [mul_comm] using (div_le_iff₀ Real.pi_pos).1 hs
    exact (certificate_tail htail).not_gt hz

theorem exists_annulus_no_vanishing :
    ∃ r R : ℝ, 0 < r ∧ r < R ∧
      ∀ f : ℝ → ℂ, MemLp f 2 volume → ¬ f =ᵐ[volume] 0 →
        ¬ (∀ z : Plane, r < ‖z‖ → ‖z‖ < R →
          AmbiguityZeros.ToMathlib.ambiguity f z.fst z.snd = 0) := by
  obtain ⟨r, R, hr, hrR, hnegative⟩ := certificate_negative_contained
  refine ⟨r, R, hr, hrR, ?_⟩
  intro f hf hne hvanish
  have hprod := density_certificate_integrable hf
  have hre (z : Plane) : (density f z * certificate z).re =
      (density f z).re * (certificate z).re := by
    simp only [density, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hint : Integrable (fun z ↦ (density f z).re * (certificate z).re) := by
    have h : Integrable (fun z ↦ (density f z * certificate z).re) := hprod.re
    simpa only [hre] using h
  have horthogonal : ∫ z, (density f z).re * (certificate z).re = 0 := by
    have h : (∫ z, (density f z * certificate z).re) =
        (∫ z, density f z * certificate z).re := integral_re hprod
    rw [density_certificate_orthogonal hf] at h
    simpa only [hre, map_zero] using! h
  apply sign_obstruction (fun z ↦ (density f z).re) (fun z ↦ (certificate z).re) 0
    (Complex.continuous_re.comp (density_continuous hf))
    (Complex.continuous_re.comp certificate_continuous)
    (fun z ↦ by simp only [density, Complex.ofReal_re]; positivity)
    (density_zero_pos hf hne)
    (by change 0 < (certificate (0 : Plane)).re; rw [certificate_zero]; norm_num)
    hint horthogonal
  intro z hz
  obtain ⟨hzr, hzR⟩ := hnegative z hz
  simp [density, hvanish z hzr hzR]

end AmbiguityHoles.GaussianObstruction

namespace AmbiguityHoles

/-- The exact statement of Theorem 1.3 from the Challenge. -/
theorem forbidden_annulus_proved :
    ∃ r R : ℝ, 0 < r ∧ r < R ∧
      ∀ f : L2 1, f ≠ 0 → ¬ annulus 1 r R ⊆ openZeros f := by
  obtain ⟨r, R, hr, hrR, hforbid⟩ := GaussianObstruction.exists_annulus_no_vanishing
  refine ⟨r, R, hr, hrR, ?_⟩
  intro f hf hsubset
  let fR : ℝ → ℂ := fun t ↦ f (realLine t)
  have hfR : MemLp fR 2 volume := (Lp.memLp f).comp_measurePreserving realLine.measurePreserving
  have hfR_ne : ¬ fR =ᵐ[volume] 0 := by
    intro hzero
    apply hf
    apply Lp.ext
    have h := realLine.symm.measurePreserving.quasiMeasurePreserving.ae hzero
    have hfzero : (f : Rd 1 → ℂ) =ᵐ[volume] 0 := by
      simpa [fR] using! h
    exact hfzero.trans (Lp.coeFn_zero ℂ 2 volume).symm
  apply hforbid fR hfR hfR_ne
  intro z hzr hzR
  have hnorm : Real.sqrt (‖realLine z.fst‖ ^ 2 + ‖realLine z.snd‖ ^ 2) = ‖z‖ := by
    rw [realLine.norm_map, realLine.norm_map, ← WithLp.prod_norm_sq_eq_of_L2,
      Real.sqrt_sq (norm_nonneg z)]
  have hmem : (realLine z.fst, realLine z.snd) ∈ annulus 1 r R := by
    change r < Real.sqrt _ ∧ Real.sqrt _ < R
    rw [hnorm]
    exact ⟨hzr, hzR⟩
  have hz := interior_subset (hsubset hmem)
  simpa only [fR, ambiguity_realLine] using! hz

end AmbiguityHoles
