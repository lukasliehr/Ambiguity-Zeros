import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

namespace AmbiguityZeros.ToMathlib

noncomputable section

open MeasureTheory
open scoped Topology

theorem integral_cexp_neg_mul_I (a b ω : ℝ) :
    ∫ t in a..b, Complex.exp (-2 * Real.pi * Complex.I * (ω : ℂ) * t) =
      if ω = 0 then (b - a : ℂ)
      else (Complex.exp (-2 * Real.pi * Complex.I * (ω : ℂ) * b)
        - Complex.exp (-2 * Real.pi * Complex.I * (ω : ℂ) * a))
        / (-2 * Real.pi * Complex.I * (ω : ℂ)) := by
  by_cases hω : ω = 0
  · subst hω
    have hconst : ∫ t in a..b, (1 : ℂ) = (b - a) • (1 : ℂ) := by
      exact intervalIntegral.integral_const (a := a) (b := b) (c := (1 : ℂ))
    have hsmul : (b - a) • (1 : ℂ) = (b - a : ℂ) := by
      rw [Complex.real_smul]
      simp [sub_eq_add_neg]
    simpa using hconst.trans hsmul
  · have hc : (-2 * Real.pi * Complex.I * (ω : ℂ)) ≠ 0 := by
      have h2 : (-2 : ℂ) ≠ 0 := by norm_num
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hpi) Complex.I_ne_zero) (by exact_mod_cast hω)
    have h := integral_exp_mul_complex (a := a) (b := b)
      (c := -2 * Real.pi * Complex.I * (ω : ℂ)) hc
    simpa [hω, mul_comm, mul_left_comm, mul_assoc] using h

theorem integral_fourierChar_Icc (a b ω : ℝ) :
    ∫ t in a..b, (Real.fourierChar (-(ω * t)) : ℂ) =
      if ω = 0 then (b - a : ℂ)
      else ((Real.fourierChar (-(ω * b)) : ℂ) - (Real.fourierChar (-(ω * a)) : ℂ))
        / (-2 * Real.pi * Complex.I * (ω : ℂ)) := by
  simpa [Real.fourierChar_apply, mul_comm, mul_left_comm, mul_assoc, neg_mul] using
    (integral_cexp_neg_mul_I (a := a) (b := b) (ω := ω))

def sincPiComplex (x : ℝ) : ℂ :=
  (Real.sinc (Real.pi * x) : ℂ)

theorem integral_cexp_symmetric (L ω : ℝ) (_hL : 0 < L) :
    ∫ t in (0 : ℝ)..L, (Real.fourierChar (-(ω * t)) : ℂ) =
      (Real.fourierChar (-(ω * L / 2)) : ℂ) * sincPiComplex (ω * L) * L := by
  by_cases hω : ω = 0
  · subst hω
    have hconst : ∫ t in (0 : ℝ)..L, ((Real.fourierChar (-(0 * t)) : ℂ)) = (L : ℂ) := by
      have h := intervalIntegral.integral_const (a := (0 : ℝ)) (b := L) (c := (1 : ℂ))
      have hsmul : (L - 0) • (1 : ℂ) = (L : ℂ) := by
        rw [Complex.real_smul]
        simp [sub_eq_add_neg]
      simpa [Real.fourierChar_apply] using h.trans hsmul
    simpa [sincPiComplex] using hconst
  · have hneq : (-(2 : ℝ) * Real.pi * ω) ≠ 0 := by
      have h2 : (-(2 : ℝ)) ≠ 0 := by norm_num
      have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
      exact mul_ne_zero (mul_ne_zero h2 hpi) hω
    have hshift :
        ∫ t in (0 : ℝ)..L, (Real.fourierChar (-(ω * t)) : ℂ) =
          (Real.fourierChar (-(L * ω / 2)) : ℂ) *
            ∫ t in (-L / 2)..(L / 2), (Real.fourierChar (-(ω * t)) : ℂ) := by
      have h := intervalIntegral.integral_comp_add_right
        (f := fun t : ℝ => (Real.fourierChar (-(ω * t)) : ℂ))
        (a := (-L / 2)) (b := (L / 2)) (d := L / 2)
      have hphase : ∀ t : ℝ,
          (Real.fourierChar (-(ω * (t + L / 2))) : ℂ) =
            (Real.fourierChar (-(ω * (L / 2))) : ℂ) * (Real.fourierChar (-(ω * t)) : ℂ) := by
        intro t
        have hmul := Real.fourierChar.map_add_eq_mul' (-(ω * (L / 2))) (-(ω * t))
        simpa [mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
          mul_assoc] using congrArg (fun z : Circle => (z : ℂ)) hmul
      have hphase0 :
          (Real.fourierChar (-(ω * (L / 2))) : ℂ) = (Real.fourierChar (-(L * ω / 2)) : ℂ) := by
        have harg : -(ω * (L / 2)) = -(L * ω / 2) := by ring
        simp [harg]
      have hfun :
          (fun t : ℝ => (Real.fourierChar (-(ω * (t + L / 2))) : ℂ)) =
            fun t : ℝ =>
              (Real.fourierChar (-(ω * (L / 2))) : ℂ) *
                (Real.fourierChar (-(ω * t)) : ℂ) := by
        funext t
        exact hphase t
      have hconst :
          ∫ t in (-L / 2)..(L / 2), (Real.fourierChar (-(ω * (t + L / 2))) : ℂ) =
            (Real.fourierChar (-(ω * (L / 2))) : ℂ) * ∫ t in (-L / 2)..(L / 2),
              (Real.fourierChar (-(ω * t)) : ℂ) := by
        rw [hfun]
        exact intervalIntegral.integral_const_mul
          (r := (Real.fourierChar (-(ω * (L / 2))) : ℂ))
          (f := fun t : ℝ => (Real.fourierChar (-(ω * t)) : ℂ))
      have hhalf : (L / 2 : ℝ) + (-L / 2) = 0 := by ring
      simpa [mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg, hhalf, add_comm, add_left_comm,
        add_assoc, hphase0] using h.symm.trans hconst
    have hcore :
        ∫ t in (-L / 2)..(L / 2), (Real.fourierChar (-(ω * t)) : ℂ) =
          sincPiComplex (ω * L) * L := by
      have hcomp :=
        intervalIntegral.integral_comp_mul_right
          (f := fun x : ℝ => (Complex.exp (x * Complex.I) : ℂ))
          (a := (-L / 2)) (b := (L / 2)) (c := (-2 * Real.pi * ω)) hneq
      have hleft : (-L / 2 : ℝ) * (-2 * Real.pi * ω) = Real.pi * ω * L := by ring
      have hright : (L / 2 : ℝ) * (-2 * Real.pi * ω) = -(Real.pi * ω * L) := by ring
      have hcomp1 := hcomp
      rw [hleft, hright] at hcomp1
      have hcomp' :
          ∫ x in (-L / 2)..(L / 2), (Real.fourierChar (-(ω * x)) : ℂ) =
            (-2 * Real.pi * ω)⁻¹ •
              ∫ x in (Real.pi * ω * L)..(-(Real.pi * ω * L)),
                (Complex.exp (x * Complex.I) : ℂ) := by
        have hfun :
            (fun x : ℝ => (Real.fourierChar (-(ω * x)) : ℂ)) =
              fun x : ℝ => (Complex.exp (((x * (-2 * Real.pi * ω)) : ℝ) * Complex.I) : ℂ) := by
          funext x
          rw [Real.fourierChar_apply]
          simp [mul_comm, mul_left_comm, mul_assoc, neg_mul]
        rw [hfun]
        exact hcomp1
      have hsym :
          ∫ x in (Real.pi * ω * L)..(-(Real.pi * ω * L)),
              (Complex.exp (x * Complex.I) : ℂ) =
            - ∫ x in (-(Real.pi * ω * L))..(Real.pi * ω * L),
              (Complex.exp (x * Complex.I) : ℂ) := by
        simpa using (intervalIntegral.integral_symm (a := -(Real.pi * ω * L))
          (b := (Real.pi * ω * L)) (f := fun x : ℝ => (Complex.exp (x * Complex.I) : ℂ)))
      have hsin :
          ∫ x in (-(Real.pi * ω * L))..(Real.pi * ω * L), (Complex.exp (x * Complex.I) : ℂ) =
            2 * (Real.pi * ω * L) * sincPiComplex (ω * L) := by
        simpa [sincPiComplex, mul_comm, mul_left_comm, mul_assoc] using
          (integral_exp_mul_I_eq_sinc (r := Real.pi * ω * L))
      have hcalc :
          ∫ t in (-L / 2)..(L / 2), (Real.fourierChar (-(ω * t)) : ℂ) =
            (-2 * Real.pi * ω)⁻¹ • (-(2 * (Real.pi * ω * L) * sincPiComplex (ω * L))) := by
        rw [hcomp', hsym, hsin]
      have hcalc' :
          ∫ t in (-L / 2)..(L / 2), (Real.fourierChar (-(ω * t)) : ℂ) =
            ((-(2 : ℝ) * Real.pi * ω)⁻¹ : ℂ) *
              (-(2 * (Real.pi * ω * L) * sincPiComplex (ω * L))) := by
        simpa [smul_eq_mul] using hcalc
      have hcoeff :
          ((-(2 : ℝ) * Real.pi * ω)⁻¹ : ℂ) * (-(2 * (Real.pi * ω * L) * sincPiComplex (ω * L))) =
            sincPiComplex (ω * L) * L := by
        field_simp [hω, Real.pi_ne_zero]
        simp [sincPiComplex, mul_comm, mul_left_comm, mul_assoc]
      exact hcalc'.trans hcoeff
    calc
      ∫ t in (0 : ℝ)..L, (Real.fourierChar (-(ω * t)) : ℂ)
        = (Real.fourierChar (-(ω * L / 2)) : ℂ) *
            ∫ t in (-L / 2)..(L / 2), (Real.fourierChar (-(ω * t)) : ℂ) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hshift
      _ = (Real.fourierChar (-(ω * L / 2)) : ℂ) * sincPiComplex (ω * L) * L := by
        rw [hcore]
        ring

theorem sincPiComplex_zero : sincPiComplex 0 = 1 := by
  simp [sincPiComplex]

theorem sincPiComplex_continuous : Continuous sincPiComplex := by
  simpa [sincPiComplex] using
    (Complex.continuous_ofReal.comp
      (Real.continuous_sinc.comp (continuous_const.mul continuous_id)))

theorem sincPiComplex_ne_zero_of_abs_lt_one (x : ℝ) (hx : |x| < 1) :
    sincPiComplex x ≠ 0 := by
  intro hzero
  have hx0 : x ≠ 0 := by
    intro hx0
    simp [hx0, sincPiComplex] at hzero
  have hzero' : Real.sinc (Real.pi * x) = 0 := by
    simpa [sincPiComplex] using hzero
  have hpi : Real.pi * x ≠ 0 := mul_ne_zero Real.pi_ne_zero hx0
  have hsin : Real.sin (Real.pi * x) = 0 := by
    rw [Real.sinc_of_ne_zero hpi] at hzero'
    exact (div_eq_zero_iff.mp hzero').resolve_right hpi
  rcases (Real.sin_eq_zero_iff).mp hsin with ⟨n, hn⟩
  have hx_eq : x = (n : ℝ) := by
    have hmul : (x : ℝ) * Real.pi = (n : ℝ) * Real.pi := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hn.symm
    exact mul_right_cancel₀ Real.pi_ne_zero hmul
  have hlt : |(n : ℝ)| < 1 := by
    simpa [hx_eq] using hx
  have hlt' : |n| < 1 := by
    exact_mod_cast hlt
  exact hx0 (by
    have hn0 : n = 0 := Int.abs_lt_one_iff.mp hlt'
    simp [hx_eq, hn0])

theorem sincPiComplex_eq_zero_iff (x : ℝ) :
    sincPiComplex x = 0 ↔ ∃ n : ℤ, n ≠ 0 ∧ x = n := by
  by_cases hx : x = 0
  · subst hx
    constructor
    · intro h
      simp [sincPiComplex] at h
    · rintro ⟨n, hn0, hn⟩
      exfalso
      exact hn0 (by simpa using hn.symm)
  · constructor
    · intro hzero
      have hzero' : Real.sinc (Real.pi * x) = 0 := by
        simpa [sincPiComplex] using hzero
      have hpi : Real.pi * x ≠ 0 := mul_ne_zero Real.pi_ne_zero hx
      have hsin : Real.sin (Real.pi * x) = 0 := by
        rw [Real.sinc_of_ne_zero hpi] at hzero'
        exact (div_eq_zero_iff.mp hzero').resolve_right hpi
      rcases (Real.sin_eq_zero_iff).mp hsin with ⟨n, hn⟩
      have hx_eq : x = (n : ℝ) := by
        have hmul : (x : ℝ) * Real.pi = (n : ℝ) * Real.pi := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hn.symm
        exact mul_right_cancel₀ Real.pi_ne_zero hmul
      refine ⟨n, ?_, ?_⟩
      · intro hn0
        simp [hx_eq, hn0] at hx
      · exact hx_eq
    · rintro ⟨n, hn0, rfl⟩
      have hnonzero : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
      have hpi : Real.pi * (n : ℝ) ≠ 0 := mul_ne_zero Real.pi_ne_zero hnonzero
      have hsin : Real.sin (Real.pi * (n : ℝ)) = 0 := by
        simpa [mul_comm] using Real.sin_int_mul_pi n
      simp [sincPiComplex, Real.sinc_of_ne_zero hpi, hsin]

theorem sincPiComplex_zero_set :
    {x : ℝ | sincPiComplex x = 0} = {x : ℝ | ∃ n : ℤ, n ≠ 0 ∧ x = n} := by
  ext x
  exact sincPiComplex_eq_zero_iff x

def sincPiComplexExt (z : ℂ) : ℂ :=
  if z = 0 then 1 else Complex.sin (Real.pi * z) / (Real.pi * z)

theorem sincPiComplexExt_ofReal (x : ℝ) :
    sincPiComplexExt x = sincPiComplex x := by
  by_cases hx : x = 0
  · simp [sincPiComplexExt, sincPiComplex, hx]
  · simp [sincPiComplexExt, sincPiComplex, Real.sinc_apply, hx, Complex.ofReal_sin]

theorem sincPiComplexExt_analyticOnNhd :
    AnalyticOnNhd ℂ sincPiComplexExt Set.univ := by
  intro z hz
  by_cases h0 : z = 0
  · subst h0
    have hcont : ContinuousAt sincPiComplexExt 0 := by
      have hmul : HasDerivAt (fun z : ℂ => z * (Real.pi : ℂ)) (Real.pi : ℂ) 0 := by
        simpa using ((hasDerivAt_id 0).mul_const (Real.pi : ℂ))
      have hsin0 : HasDerivAt Complex.sin (1 : ℂ) (0 * (Real.pi : ℂ)) := by
        simpa using (Complex.hasDerivAt_sin (0 : ℂ))
      have h : HasDerivAt (fun z : ℂ => Complex.sin (z * (Real.pi : ℂ))) (Real.pi : ℂ) 0 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (HasDerivAt.comp (x := 0) (h := fun z : ℂ => z * (Real.pi : ℂ))
            (h₂ := Complex.sin) (h' := (Real.pi : ℂ)) (h₂' := (1 : ℂ)) hsin0 hmul)
      have hcont' : ContinuousAt
          (Function.update (fun z : ℂ => Complex.sin (z * (Real.pi : ℂ)) / z) 0
            (Real.pi : ℂ)) 0 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using h.continuousAt_div
      have hcont'' : ContinuousAt
          (fun z : ℂ =>
            Function.update (fun z : ℂ => Complex.sin (z * (Real.pi : ℂ)) / z) 0
              (Real.pi : ℂ) z / (Real.pi : ℂ)) 0 :=
        hcont'.div_const (Real.pi : ℂ)
      have hfun :
          (fun z : ℂ =>
            Function.update (fun z : ℂ => Complex.sin (z * (Real.pi : ℂ)) / z) 0
              (Real.pi : ℂ) z / (Real.pi : ℂ)) =
            sincPiComplexExt := by
        funext z
        by_cases hz : z = 0
        · subst hz
          simp [sincPiComplexExt, Function.update, Real.pi_ne_zero]
        · simp [sincPiComplexExt, Function.update, hz, div_eq_mul_inv, mul_comm,
            mul_assoc]
      simpa [hfun] using hcont''
    have hd : ∀ᶠ z in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ sincPiComplexExt z := by
      rw [eventually_nhdsWithin_iff]
      refine Filter.Eventually.of_forall ?_
      intro z hz
      have hmul : AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) * z) z := by
        simpa [mul_comm] using
          ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (Real.pi : ℂ)) z).mul analyticAt_id)
      have hsin : AnalyticAt ℂ (fun z : ℂ => Complex.sin (Real.pi * z)) z := by
        simpa [Function.comp, mul_comm, mul_left_comm, mul_assoc] using
          (Complex.analyticAt_sin.comp hmul)
      have hne : (Real.pi * z : ℂ) ≠ 0 := by
        have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        exact mul_ne_zero hpi hz
      have hdiff : DifferentiableAt ℂ (fun z : ℂ => Complex.sin (Real.pi * z) / (Real.pi * z)) z :=
        (hsin.div hmul hne).differentiableAt
      have hEq :
          sincPiComplexExt =ᶠ[nhds z]
            fun w : ℂ => Complex.sin (Real.pi * w) / (Real.pi * w) := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
        have hw0 : w ≠ 0 := hw
        simp [sincPiComplexExt, hw0]
      exact hdiff.congr_of_eventuallyEq hEq
    exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd hcont
  · have hmul : AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) * z) z := by
      simpa [mul_comm] using
        ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (Real.pi : ℂ)) z).mul analyticAt_id)
    have hsin : AnalyticAt ℂ (fun z : ℂ => Complex.sin (Real.pi * z)) z := by
      simpa [Function.comp, mul_comm, mul_left_comm, mul_assoc] using
        (Complex.analyticAt_sin.comp hmul)
    have hne : (Real.pi * z : ℂ) ≠ 0 := by
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero hpi h0
    have hEq :
        sincPiComplexExt =ᶠ[nhds z]
          fun w : ℂ => Complex.sin (Real.pi * w) / (Real.pi * w) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds h0] with w hw
      have hw0 : w ≠ 0 := hw
      simp [sincPiComplexExt, hw0]
    exact (hsin.div hmul hne).congr hEq.symm

theorem integral_cexp_ne_zero
    (a b ω : ℝ) (hab : a < b)
    (hω : ω = 0 ∨ ¬ ∃ n : ℤ, ω * (b - a) = n) :
    ∫ t in a..b, (Real.fourierChar (-(ω * t)) : ℂ) ≠ 0 := by
  have hL : 0 < b - a := sub_pos.mpr hab
  rcases hω with rfl | hω
  · have hconst : ∫ t in a..b, ((Real.fourierChar (-(0 * t)) : ℂ)) = (b - a : ℂ) := by
      have h := intervalIntegral.integral_const (a := a) (b := b) (c := (1 : ℂ))
      have hsmul : (b - a) • (1 : ℂ) = (b - a : ℂ) := by
        rw [Complex.real_smul]
        simp [sub_eq_add_neg]
      simpa [Real.fourierChar_apply] using h.trans hsmul
    have hne : (b - a : ℂ) ≠ 0 := by
      have hba : b - a ≠ 0 := by
        linarith
      exact_mod_cast hba
    intro hzero
    exact hne (hconst.symm.trans hzero)
  · have hshift :
        ∫ t in a..b, (Real.fourierChar (-(ω * t)) : ℂ) =
          (Real.fourierChar (-(ω * a)) : ℂ) * ∫ t in 0..(b - a),
            (Real.fourierChar (-(ω * t)) : ℂ) := by
      have h :=
        intervalIntegral.integral_comp_add_right
          (f := fun t : ℝ => (Real.fourierChar (-(ω * t)) : ℂ)) (a := (0 : ℝ)) (b := b - a) a
      have hphase : ∀ t : ℝ,
          (Real.fourierChar (-(ω * (t + a))) : ℂ) =
            (Real.fourierChar (-(ω * a)) : ℂ) * (Real.fourierChar (-(ω * t)) : ℂ) := by
        intro t
        have hmul := Real.fourierChar.map_add_eq_mul' (-(ω * a)) (-(ω * t))
        simpa [mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
          mul_assoc] using
          congrArg (fun z : Circle => (z : ℂ)) hmul
      have hfun :
          (fun t : ℝ => (Real.fourierChar (-(ω * (t + a))) : ℂ)) =
            fun t : ℝ => (Real.fourierChar (-(ω * a)) : ℂ) * (Real.fourierChar (-(ω * t)) : ℂ) := by
        funext t
        exact hphase t
      have hconst :
          ∫ t in 0..(b - a), (Real.fourierChar (-(ω * (t + a))) : ℂ) =
            (Real.fourierChar (-(ω * a)) : ℂ) * ∫ t in 0..(b - a),
              (Real.fourierChar (-(ω * t)) : ℂ) := by
        rw [hfun]
        exact intervalIntegral.integral_const_mul
          (r := (Real.fourierChar (-(ω * a)) : ℂ))
          (f := fun t : ℝ => (Real.fourierChar (-(ω * t)) : ℂ))
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h.symm.trans hconst
    have hcore :
        ∫ t in 0..(b - a), (Real.fourierChar (-(ω * t)) : ℂ) ≠ 0 := by
      have hsym := integral_cexp_symmetric (L := b - a) (ω := ω) hL
      have hphase : (Real.fourierChar (-(ω * (b - a) / 2)) : ℂ) ≠ 0 := by
        simp [Real.fourierChar_apply]
      have hsinc : sincPiComplex (ω * (b - a)) ≠ 0 := by
        intro hzero
        exact hω (by
          rcases (sincPiComplex_eq_zero_iff (ω * (b - a))).mp hzero with ⟨n, hn0, hn⟩
          exact ⟨n, hn⟩)
      have hlen : (b - a : ℂ) ≠ 0 := by
        have hba : b - a ≠ 0 := by
          linarith
        exact_mod_cast hba
      rw [hsym]
      simpa using (mul_ne_zero (mul_ne_zero hphase hsinc) hlen)
    have hphase0 : (Real.fourierChar (-(ω * a)) : ℂ) ≠ 0 := by
      simp [Real.fourierChar_apply]
    simpa [hshift] using (mul_ne_zero hphase0 hcore)

end

end AmbiguityZeros.ToMathlib
