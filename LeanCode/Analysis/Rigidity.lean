module

public import LeanCode.Analysis.Injectivity
public import LeanCode.Analysis.Uncertainty
public import LeanCode.Analysis.Origin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push

public section

/-! Compact rigidity for differences of ambiguity functions. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate FourierTransform

namespace AmbiguityHoles.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem ae_bounded_of_kernel_band {f g : E → ℂ} {R : ℝ}
    (hband : ∀ᵐ s ∂(volume : Measure E), ∀ᵐ t ∂(volume : Measure E),
      R < ‖t - s‖ → f t * star (f s) - g t * star (g s) = 0)
    (hf : ¬ f =ᵐ[volume] 0) (hfg : ¬ ∃ c : ℂ, g =ᵐ[volume] fun t ↦ c * f t) :
    ∃ C : ℝ, ∀ᵐ t ∂volume, C < ‖t‖ → f t = 0 ∧ g t = 0 := by
  have hs : ∃ s : E, f s ≠ 0 ∧
      ∀ᵐ t ∂(volume : Measure E), R < ‖t - s‖ →
        f t * star (f s) - g t * star (g s) = 0 := by
    by_contra hn
    apply hf
    filter_upwards [hband] with s h
    by_contra hz
    exact hn ⟨s, hz, h⟩
  obtain ⟨s, hfs, hs⟩ := hs
  have hq : ∃ q : E, f s * g q - g s * f q ≠ 0 ∧
      ∀ᵐ t ∂(volume : Measure E), R < ‖t - q‖ →
        f t * star (f q) - g t * star (g q) = 0 := by
    by_contra hn
    apply hfg
    refine ⟨g s / f s, ?_⟩
    filter_upwards [hband] with q h
    have hz : f s * g q - g s * f q = 0 := by
      by_contra hne
      exact hn ⟨q, hne, h⟩
    change g q = (g s / f s) * f q
    rw [div_mul_eq_mul_div, eq_div_iff hfs]
    linear_combination hz
  obtain ⟨q, hdet, hq⟩ := hq
  have hdet' : star (f s) * star (g q) - star (g s) * star (f q) ≠ 0 := by
    have h := star_ne_zero.mpr hdet
    simpa [star_sub, star_mul, mul_comm] using h
  refine ⟨R + max ‖s‖ ‖q‖, ?_⟩
  filter_upwards [hs, hq] with t hts htq ht
  have hs' : R < ‖t - s‖ := by
    linarith [norm_sub_rev t s, norm_le_insert' t s, le_max_left ‖s‖ ‖q‖]
  have hq' : R < ‖t - q‖ := by
    linarith [norm_sub_rev t q, norm_le_insert' t q, le_max_right ‖s‖ ‖q‖]
  specialize hts hs'
  specialize htq hq'
  constructor
  · apply (mul_eq_zero.mp (_ : f t * _ = 0)).resolve_right hdet'
    linear_combination star (g q) * hts - star (g s) * htq
  · apply (mul_eq_zero.mp (_ : g t * _ = 0)).resolve_right hdet'
    linear_combination star (f q) * hts - star (f s) * htq

private theorem ambiguity_eq_of_slice_bounded [Nontrivial E] {f g : E → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) {C S : ℝ}
    (ht : ∀ᵐ t ∂volume, C < ‖t‖ → f t = 0 ∧ g t = 0)
    (hS : ∀ x ω, S < ‖ω‖ → ambiguity f x ω = ambiguity g x ω) :
    ∀ x ω, ambiguity f x ω = ambiguity g x ω := by
  intro x
  let a : E := (1 / 2 : ℝ) • x
  let F : E → ℂ := fun t ↦ f (t + a) * star (f (t - a))
  let G : E → ℂ := fun t ↦ g (t + a) * star (g (t - a))
  have hF : Integrable F := kernel_slice_integrable hf hf x
  have hG : Integrable G := kernel_slice_integrable hg hg x
  have hFourier (ω : E) : 𝓕 (F - G) ω = ambiguity f x ω - ambiguity g x ω := by
    rw [fourier_sub_integrable hF hG]
    exact congrArg₂ (· - ·) (fourier_kernel_slice f x ω) (fourier_kernel_slice g x ω)
  have htime : ∃ R : ℝ, ∀ᵐ t ∂volume, R < ‖t‖ → (F - G) t = 0 := by
    refine ⟨C + ‖a‖, ?_⟩
    have hshift := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae ht
    filter_upwards [hshift] with t h ht'
    have hta : C < ‖t + a‖ := by
      have hle : ‖t‖ ≤ ‖t + a‖ + ‖a‖ := by
        simpa using norm_le_insert' t (t + a)
      linarith
    obtain ⟨hft, hgt⟩ := h hta
    simp [F, G, hft, hgt]
  have hfreq : ∃ R : ℝ, ∀ᵐ ω ∂volume, R < ‖ω‖ → 𝓕 (F - G) ω = 0 :=
    ⟨S, ae_of_all _ fun ω hω ↦ by rw [hFourier, hS x ω hω, sub_self]⟩
  have hz := ae_eq_zero_of_aeBoundedSupport_fourier (F - G) (hF.sub hG) htime hfreq
  intro ω
  apply sub_eq_zero.mp
  rw [← hFourier]
  rw [Real.fourier_eq]
  apply integral_eq_zero_of_ae
  filter_upwards [hz] with t h
  change (F - G) t = 0 at h
  rw [h, smul_zero]
  rfl

/-- A difference of ambiguity functions with bounded support forces dependence. -/
theorem ae_dependent_of_bounded_ambiguity_difference [Nontrivial E] {f g : E → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hbound : ∃ R S : ℝ, ∀ x ω, R < ‖x‖ ∨ S < ‖ω‖ →
      ambiguity f x ω = ambiguity g x ω) :
    f =ᵐ[volume] 0 ∨ ∃ c : ℂ, g =ᵐ[volume] fun t ↦ c * f t := by
  by_contra h
  push Not at h
  obtain ⟨R, S, hRS⟩ := hbound
  have hK := ambiguity_eq_kernel_ae_of hf hg
    (S := {x : E | R < ‖x‖}) (measurableSet_lt measurable_const continuous_norm.measurable)
    (fun x hx ω ↦ hRS x ω (Or.inl hx))
  have hKswap := (Measure.measurePreserving_swap (μ := (volume : Measure E))
    (ν := (volume : Measure E))).quasiMeasurePreserving.ae hK
  have hband : ∀ᵐ s ∂(volume : Measure E), ∀ᵐ t ∂(volume : Measure E),
      R < ‖t - s‖ → f t * star (f s) - g t * star (g s) = 0 := by
    have hp : ∀ᵐ p : E × E ∂(volume.prod volume), R < ‖p.2 - p.1‖ →
        f p.2 * star (f p.1) - g p.2 * star (g p.1) = 0 := by
      filter_upwards [hKswap] with p hp hnorm
      exact sub_eq_zero.mpr (hp hnorm)
    exact Measure.ae_ae_of_ae_prod hp
  obtain ⟨C, hC⟩ := ae_bounded_of_kernel_band hband h.1 (fun ⟨c, hc⟩ ↦ h.2 c hc)
  have hA := ambiguity_eq_of_slice_bounded hf hg hC (fun x ω hω ↦ hRS x ω (Or.inr hω))
  obtain ⟨θ, hθ⟩ := phase_of_ambiguity_eq hf hg hA
  exact h.2 (Complex.exp (θ * Complex.I)) hθ

/-- Bounded support and equality at the origin force equality everywhere. -/
theorem ambiguity_eq_of_bounded_difference {f g : E → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hbound : ∃ R S : ℝ, ∀ x ω, R < ‖x‖ ∨ S < ‖ω‖ →
      ambiguity f x ω = ambiguity g x ω)
    (h0 : ambiguity f 0 0 = ambiguity g 0 0) :
    ∀ x ω, ambiguity f x ω = ambiguity g x ω := by
  cases subsingleton_or_nontrivial E with
  | inl h =>
    letI := h
    intro x ω
    rw [Subsingleton.elim x 0, Subsingleton.elim ω 0]
    exact h0
  | inr h =>
    letI := h
    exact ambiguity_eq_of_ae_dependent_of_origin_eq hf hg
      (ae_dependent_of_bounded_ambiguity_difference hf hg hbound) h0

end AmbiguityHoles.Analysis
