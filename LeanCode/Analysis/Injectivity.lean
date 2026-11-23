module

public import LeanCode.Analysis.FourierUniqueness
public import LeanCode.Analysis.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.Linarith

public section

/-! Injectivity of the ambiguity function on square integrable signals, up to phase. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace AmbiguityHoles.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The delay slice of the integral kernel of two square integrable signals. -/
theorem kernel_slice_integrable {f g : E → ℂ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (x : E) :
    Integrable (fun t ↦ f (t + (1 / 2 : ℝ) • x) * star (g (t - (1 / 2 : ℝ) • x))) volume := by
  have h₁ : MemLp (fun t ↦ f (t + (1 / 2 : ℝ) • x)) 2 volume := by
    exact hf.comp_measurePreserving (measurePreserving_add_right volume _)
  have h₂ : MemLp (fun t ↦ star (g (t - (1 / 2 : ℝ) • x))) 2 volume :=
    (hg.comp_measurePreserving (measurePreserving_sub_right volume ((1 / 2 : ℝ) • x))).star
  exact h₁.integrable_mul h₂

theorem fourier_kernel_slice (f : E → ℂ) (x ω : E) :
    𝓕 (fun t ↦ f (t + (1 / 2 : ℝ) • x) * star (f (t - (1 / 2 : ℝ) • x))) ω =
      ambiguity f x ω := by
  simp [Real.fourier_eq, Circle.smul_def,
    ambiguity, crossAmbiguity, mul_comm, real_inner_comm]

theorem fourier_sub_integrable {F G : E → ℂ} (hF : Integrable F)
    (hG : Integrable G) (ω : E) : 𝓕 (F - G) ω = 𝓕 F ω - 𝓕 G ω := by
  simp only [Real.fourier_eq, Pi.sub_apply, smul_sub]
  rw [integral_sub]
  · exact (Real.fourierIntegral_convergent_iff ω).2 hF
  · exact (Real.fourierIntegral_convergent_iff ω).2 hG

theorem ambiguity_eq_kernel_slice_ae {f g : E → ℂ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (x : E) (h : ∀ ω, ambiguity f x ω = ambiguity g x ω) :
    ∀ᵐ t ∂volume, f (t + (1 / 2 : ℝ) • x) * star (f (t - (1 / 2 : ℝ) • x)) =
      g (t + (1 / 2 : ℝ) • x) * star (g (t - (1 / 2 : ℝ) • x)) := by
  let F : E → ℂ := fun t ↦ f (t + (1 / 2 : ℝ) • x) * star (f (t - (1 / 2 : ℝ) • x))
  let G : E → ℂ := fun t ↦ g (t + (1 / 2 : ℝ) • x) * star (g (t - (1 / 2 : ℝ) • x))
  have hF : Integrable F volume := kernel_slice_integrable hf hf x
  have hG : Integrable G volume := kernel_slice_integrable hg hg x
  have hz : 𝓕 (F - G) = 0 := by
    funext ω
    rw [fourier_sub_integrable hF hG]
    have heq : 𝓕 F ω = 𝓕 G ω := by
      rw [show 𝓕 F ω = ambiguity f x ω from fourier_kernel_slice f x ω,
        show 𝓕 G ω = ambiguity g x ω from fourier_kernel_slice g x ω]
      exact h ω
    exact sub_eq_zero.mpr heq
  filter_upwards [integrable_fourier_eq_zero_ae (F - G) (hF.sub hG) hz] with t ht
  exact sub_eq_zero.mp ht

private def kernelCoords : (E × E) ≃ₗ[ℝ] E × E where
  toFun p := (p.2 + (1 / 2 : ℝ) • p.1, p.2 - (1 / 2 : ℝ) • p.1)
  invFun p := (p.1 - p.2, (1 / 2 : ℝ) • (p.1 + p.2))
  left_inv := by
    intro p
    ext <;> simp <;> module
  right_inv := by
    intro p
    ext <;> simp <;> module
  map_add' := by
    intro p q
    ext <;> simp <;> module
  map_smul' := by
    intro c p
    ext <;> simp <;> module

private theorem coords_qmp (L : (E × E) ≃ₗ[ℝ] E × E) :
    Measure.QuasiMeasurePreserving L (volume.prod volume) (volume.prod volume) := by
  exact MeasureTheory.Measure.LinearMap.quasiMeasurePreserving
    (volume.prod volume) L.toLinearMap (LinearEquiv.isUnit_det' L).ne_zero

/-- Equality at every frequency on a set of delays gives equality of the kernels there. -/
theorem ambiguity_eq_kernel_ae_of {f g : E → ℂ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) {S : Set E} (hS : MeasurableSet S)
    (h : ∀ x ∈ S, ∀ ω, ambiguity f x ω = ambiguity g x ω) :
    ∀ᵐ p : E × E ∂(volume.prod volume), p.1 - p.2 ∈ S →
      f p.1 * star (f p.2) = g p.1 * star (g p.2) := by
  let L : (E × E) ≃ₗ[ℝ] E × E := kernelCoords
  let f' := hf.aemeasurable.mk f
  let g' := hg.aemeasurable.mk g
  have hfm : Measurable f' := hf.aemeasurable.measurable_mk
  have hgm : Measurable g' := hg.aemeasurable.measurable_mk
  have hf' : f =ᵐ[volume] f' := hf.aemeasurable.ae_eq_mk
  have hg' : g =ᵐ[volume] g' := hg.aemeasurable.ae_eq_mk
  have h' : ∀ᵐ p : E × E ∂(volume.prod volume), p.1 ∈ S →
      f' (L p).1 * star (f' (L p).2) = g' (L p).1 * star (g' (L p).2) := by
    apply (Measure.ae_prod_iff_ae_ae ?_).2
    · filter_upwards [] with x
      have hp : MeasurePreserving (fun t : E ↦ t + (1 / 2 : ℝ) • x) volume volume :=
        measurePreserving_add_right volume _
      have hm : MeasurePreserving (fun t : E ↦ t - (1 / 2 : ℝ) • x) volume volume :=
        measurePreserving_sub_right volume _
      by_cases hx : x ∈ S
      · filter_upwards [ambiguity_eq_kernel_slice_ae hf hg x (h x hx),
          hp.quasiMeasurePreserving.ae_eq_comp hf', hm.quasiMeasurePreserving.ae_eq_comp hf',
          hp.quasiMeasurePreserving.ae_eq_comp hg', hm.quasiMeasurePreserving.ae_eq_comp hg']
          with t ht hf₁ hf₂ hg₁ hg₂ _
        change f' (t + (1 / 2 : ℝ) • x) * star (f' (t - (1 / 2 : ℝ) • x)) =
          g' (t + (1 / 2 : ℝ) • x) * star (g' (t - (1 / 2 : ℝ) • x))
        dsimp only [Function.comp_apply] at hf₁ hf₂ hg₁ hg₂
        rw [← hf₁, ← hf₂, ← hg₁, ← hg₂]
        exact ht
      · exact Filter.Eventually.of_forall fun _ hmem ↦ (hx hmem).elim
    · apply MeasurableSet.imp (hS.preimage measurable_fst)
      have hL : Measurable L := L.toLinearMap.continuous_of_finiteDimensional.measurable
      exact measurableSet_eq_fun
        ((hfm.comp (measurable_fst.comp hL)).mul (continuous_star.measurable.comp (hfm.comp (measurable_snd.comp hL))))
        ((hgm.comp (measurable_fst.comp hL)).mul (continuous_star.measurable.comp (hgm.comp (measurable_snd.comp hL))))
  have hpull := (coords_qmp L.symm).ae h'
  have hfst : Measure.QuasiMeasurePreserving (@Prod.fst E E) (volume.prod volume) volume :=
    Measure.quasiMeasurePreserving_fst
  have hsnd : Measure.QuasiMeasurePreserving (@Prod.snd E E) (volume.prod volume) volume :=
    Measure.quasiMeasurePreserving_snd
  filter_upwards [hpull, hfst.ae_eq_comp hf', hsnd.ae_eq_comp hf', hfst.ae_eq_comp hg', hsnd.ae_eq_comp hg']
    with p hp hf₁ hf₂ hg₁ hg₂ hmem
  dsimp only [Function.comp_apply] at hf₁ hf₂ hg₁ hg₂
  rw [hf₁, hf₂, hg₁, hg₂]
  rw [LinearEquiv.apply_symm_apply] at hp
  exact hp hmem


/-- The rank one kernel determines its generating signal up to a constant phase. -/
theorem phase_of_kernel_eq {f g : E → ℂ}
    (h : ∀ᵐ p : E × E ∂(volume.prod volume), f p.1 * star (f p.2) = g p.1 * star (g p.2)) :
    ∃ θ : ℝ, g =ᵐ[volume] fun t ↦ Complex.exp (θ * Complex.I) * f t := by
  have hsec : ∀ᵐ s ∂volume, ∀ᵐ t ∂volume, f s * star (f t) = g s * star (g t) :=
    Measure.ae_ae_of_ae_prod h
  by_cases hf : f =ᵐ[volume] 0
  · refine ⟨0, ?_⟩
    have hg : g =ᵐ[volume] 0 := by
      by_contra hgn
      obtain ⟨s, hs, hs'⟩ : ∃ s, g s ≠ 0 ∧
          (f s = 0 ∧ ∀ᵐ t ∂volume, f s * star (f t) = g s * star (g t)) := by
        have hh : ∀ᵐ s ∂volume, f s = 0 ∧
            ∀ᵐ t ∂volume, f s * star (f t) = g s * star (g t) := hf.and hsec
        by_contra! hn
        apply hgn
        filter_upwards [hh] with s hs
        by_contra hne
        exact hn s hne hs.1 (hs.2.mono fun _ heq hneq ↦ hneq heq)
      apply hgn
      filter_upwards [hs'.2] with t ht
      have hmul : g s * star (g t) = 0 := by simpa [hs'.1] using ht.symm
      simpa using (mul_eq_zero.mp hmul).resolve_left hs
    filter_upwards [hf, hg] with t ht ht'
    simp [ht, ht']
  · have pick : ∀ {P : E → Prop}, (∀ᵐ s ∂volume, P s) → ∃ s, f s ≠ 0 ∧ P s := by
      intro P hP
      by_contra! hn
      apply hf
      filter_upwards [hP] with s hs
      by_contra hs'
      exact hn s hs' hs
    obtain ⟨s, hs, hst⟩ := pick hsec
    have hgs : g s ≠ 0 := by
      intro hgs
      apply hf
      filter_upwards [hst] with t ht
      have hmul : f s * star (f t) = 0 := by simpa [hgs] using ht
      simpa using (mul_eq_zero.mp hmul).resolve_left hs
    let c : ℂ := star (f s) / star (g s)
    have hc : g =ᵐ[volume] fun t ↦ c * f t := by
      filter_upwards [hst] with t ht
      have he := congrArg (star : ℂ → ℂ) ht
      simp only [star_mul, star_star] at he
      change g t = star (f s) / star (g s) * f t
      rw [div_mul_eq_mul_div, eq_div_iff (star_ne_zero.mpr hgs)]
      simpa only [mul_comm] using he.symm
    obtain ⟨a, ha, ha₁, ha₂⟩ := pick (hc.and hsec)
    obtain ⟨b, hb, hb₁, hb₂⟩ := pick (hc.and ha₂)
    have hunit : c * star c = 1 := by
      rw [ha₁, hb₁, star_mul] at hb₂
      apply mul_right_cancel₀ (mul_ne_zero ha (star_ne_zero.mpr hb))
      calc
        (c * star c) * (f a * star (f b)) = (c * f a) * (star (f b) * star c) := by ring
        _ = 1 * (f a * star (f b)) := by rw [← hb₂, one_mul]
    have hnorm : ‖c‖ = 1 := by
      have he := congrArg norm hunit
      simp at he
      nlinarith [norm_nonneg c]
    obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff c).mp hnorm
    exact ⟨θ, by simpa [hθ] using hc⟩

/-- The full ambiguity function determines an `L²` signal up to constant phase. -/
theorem phase_of_ambiguity_eq {f g : E → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (h : ∀ x ω, ambiguity f x ω = ambiguity g x ω) :
    ∃ θ : ℝ, g =ᵐ[volume] fun t ↦ Complex.exp (θ * Complex.I) * f t :=
  phase_of_kernel_eq (by
    simpa using (ambiguity_eq_kernel_ae_of hf hg (S := Set.univ)
      MeasurableSet.univ (fun x _ ω ↦ h x ω)))

end AmbiguityHoles.Analysis
