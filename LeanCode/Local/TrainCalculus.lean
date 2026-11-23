module

public import LeanCode.Local.Trains
public import LeanCode.Local.Selected
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace AmbiguityHoles.Local
open Analysis

variable {d : ℕ} {ι : Type*} {L : ℝ}

private theorem unique_cube {site : ι → Coord d}
    (sep : ∀ i j, i ≠ j → ∃ k, L < |site i k - site j k|)
    {i j : ι} {t : Coord d} (hi : t - site i ∈ unitCube L)
    (hj : t - site j ∈ unitCube L) : i = j := by
  by_contra h
  obtain ⟨k, hk⟩ := sep i j h
  have u := hi k
  have v := hj k
  simp only [mem_Icc, PiLp.sub_apply] at u v
  exact hk.not_ge (abs_le.mpr ⟨by linarith [u.1, v.2], by linarith [u.2, v.1]⟩)

theorem support_cubeTrain {site : ι → Coord d} (c : ι → ℂ) :
    Function.support (cubeTrain L site c) ⊆ {t | ∃ i, t - site i ∈ unitCube L} := by
  intro t ht
  by_contra! hs
  exact ht (cubeTrain_off c (fun i hi ↦ hs ⟨i, hi⟩))

theorem cubeTrain_cross_zero {site other : ι → Coord d} (c b : ι → ℂ)
    (x ω : Coord d)
    (hsep : ∀ i j, ¬ coordBox L (x - (site i - other j))) :
    crossAmbiguity (cubeTrain L site c) (cubeTrain L other b) x ω = 0 := by
  apply selected_crossAmbiguity_zero_of_support (support_cubeTrain c) (support_cubeTrain b)
  rintro p ⟨i, hi⟩ q ⟨j, hj⟩ rfl
  apply hsep i j
  intro k
  have u := hi k
  have v := hj k
  simp only [mem_Icc, PiLp.sub_apply] at u v ⊢
  exact abs_le.mpr ⟨by linarith [u.1, v.2], by linarith [u.2, v.1]⟩

private theorem measurable_cube_term (site : ι → Coord d) (c : ι → ℂ) (i : ι) :
    Measurable (fun t ↦ c i * cubePulse L (t - site i)) :=
  measurable_const.mul ((measurable_cubePulse L).comp (measurable_id.sub_const _))

private theorem cube_term_lintegral (u : Coord d) (b : ℝ≥0∞) :
    (∫⁻ t : Coord d, ((fun t : Coord d ↦ t - u) ⁻¹' unitCube L).indicator (fun _ ↦ b) t) =
      b * volume (unitCube L : Set (Coord d)) := by
  have h : MeasurableSet ((fun t : Coord d ↦ t - u) ⁻¹' unitCube L) :=
    (measurable_unitCube L).preimage (measurable_id.sub_const _)
  rw [lintegral_indicator_const h]
  congr 1
  simpa only [sub_eq_add_neg] using
    (measurePreserving_add_right volume (-u)).measure_preimage (measurable_unitCube L).nullMeasurableSet

theorem cubeTrain_memLp [Countable ι] {site : ι → Coord d}
    (sep : ∀ i j, i ≠ j → ∃ k, L < |site i k - site j k|)
    {c : ι → ℂ} (hc : Summable fun i ↦ ‖c i‖ ^ 2) :
    MemLp (cubeTrain L site c) 2 volume := by
  classical
  have hterm (t : Coord d) :
      (Function.support fun i ↦ c i * cubePulse L (t - site i)).Subsingleton := by
    intro i hi j hj
    apply unique_cube sep (t := t)
    · by_contra hh
      exact hi (by simp [cubePulse, hh])
    · by_contra hh
      exact hj (by simp [cubePulse, hh])
  have hm : Measurable (cubeTrain L site c) := by
    refine measurable_of_tendsto_metrizable'
      (f := fun (s : Finset ι) t ↦ ∑ i ∈ s, c i * cubePulse L (t - site i)) atTop ?_ ?_
    · intro s
      exact s.measurable_fun_sum fun i _ ↦ measurable_cube_term site c i
    · rw [tendsto_pi_nhds]
      intro t
      have hs : Summable (fun i ↦ c i * cubePulse L (t - site i)) :=
        summable_of_hasFiniteSupport (hterm t).finite
      exact hs.hasSum
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have heq (t : Coord d) :
      ‖cubeTrain L site c t‖ₑ ^ 2 =
        ∑' i, ‖c i * cubePulse L (t - site i)‖ₑ ^ 2 := by
    by_cases ht : ∃ i, c i * cubePulse L (t - site i) ≠ 0
    · obtain ⟨i, hi⟩ := ht
      have hzero : ∀ j, j ≠ i → c j * cubePulse L (t - site j) = 0 := by
        intro j hj
        by_contra hz
        exact hj (hterm t hz hi)
      rw [cubeTrain, tsum_eq_single i hzero, tsum_eq_single i]
      intro j hj
      simp [hzero j hj]
    · push Not at ht
      simp [cubeTrain, ht]
  simp_rw [heq]
  rw [lintegral_tsum (fun i ↦ ((measurable_cube_term site c i).enorm.pow_const 2).aemeasurable)]
  have hval (i : ι) :
      (∫⁻ t : Coord d, ‖c i * cubePulse L (t - site i)‖ₑ ^ 2) =
        ENNReal.ofReal (‖c i‖ ^ 2) * volume (unitCube L : Set (Coord d)) := by
    rw [← cube_term_lintegral (L := L) (site i)]
    apply lintegral_congr
    intro t
    by_cases ht : t - site i ∈ unitCube L
    · simp [cubePulse, ht, ENNReal.ofReal_pow (norm_nonneg _), Set.indicator]
    · simp [cubePulse, ht, Set.indicator]
  simp_rw [hval]
  rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun i ↦ sq_nonneg _) hc]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (isCompact_unitCube L).measure_lt_top

theorem cubeTrain_cross_matched [Countable ι] {site other : ι → Coord d} {c b : ι → ℂ}
    (hsite : ∀ i j, i ≠ j → ∃ k, L < |site i k - site j k|)
    (hother : ∀ i j, i ≠ j → ∃ k, L < |other i k - other j k|)
    (hc : Summable fun i ↦ ‖c i * star (b i)‖)
    (x ω : Coord d)
    (hsep : ∀ i j, i ≠ j → ¬ coordBox L (x - (site i - other j))) :
    crossAmbiguity (cubeTrain L site c) (cubeTrain L other b) x ω =
      ∑' i, (c i * star (b i)) *
        crossAmbiguity (translate (site i) (cubePulse L)) (translate (other i) (cubePulse L)) x ω := by
  classical
  let u (t : Coord d) := t + (1/2 : ℝ) • x
  let v (t : Coord d) := t - (1/2 : ℝ) • x
  let ch (t : Coord d) : ℂ := (Real.fourierChar (-(inner ℝ ω t)) : ℂ)
  let term (i : ι) (t : Coord d) : ℂ :=
    (c i * star (b i)) * (cubePulse L (u t - site i) * star (cubePulse L (v t - other i)) * ch t)
  have ht (t : Coord d) :
      cubeTrain L site c (u t) * star (cubeTrain L other b (v t)) * ch t = ∑' i, term i t := by
    by_cases hu : ∃ i, u t - site i ∈ unitCube L
    · obtain ⟨i, hi⟩ := hu
      by_cases hv : ∃ j, v t - other j ∈ unitCube L
      · obtain ⟨j, hj⟩ := hv
        have hij : i = j := by
          by_contra hn
          exact hsep i j hn (pulse_overlap hi hj)
        subst j
        rw [cubeTrain_at hsite c hi, cubeTrain_at hother b hj, tsum_eq_single i]
        · simp [term, cubePulse, hi, hj]
        · intro j hj
          have hf : u t - site j ∉ unitCube L := fun hh ↦ hj (unique_cube hsite hh hi)
          simp [term, cubePulse, hf]
      · push Not at hv
        simp [cubeTrain_off b hv, term, cubePulse, hv]
    · push Not at hu
      simp [cubeTrain_off c hu, term, cubePulse, hu]
  have hm (i : ι) : AEStronglyMeasurable (term i) volume := by
    have hmU : Measurable (fun t ↦ cubePulse L (u t - site i)) :=
      (measurable_cubePulse L).comp (by dsimp [u]; fun_prop)
    have hmV : Measurable (fun t ↦ cubePulse L (v t - other i)) :=
      (measurable_cubePulse L).comp (by dsimp [v]; fun_prop)
    have hmC : Measurable ch := by dsimp [ch]; fun_prop
    exact aestronglyMeasurable_const.mul ((hmU.aestronglyMeasurable.mul
      hmV.aestronglyMeasurable.star).mul hmC.aestronglyMeasurable)
  have hbound (i : ι) :
      (∫⁻ t, ‖term i t‖ₑ) ≤
        ENNReal.ofReal ‖c i * star (b i)‖ * volume (unitCube L : Set (Coord d)) := by
    rw [← cube_term_lintegral (L := L) (site i - (1/2 : ℝ) • x)]
    apply lintegral_mono
    intro t
    have hx : u t - site i = t - (site i - (1/2 : ℝ) • x) := by dsimp [u]; module
    change ‖term i t‖ₑ ≤ ((fun t : Coord d ↦ t - (site i - (1/2 : ℝ) • x)) ⁻¹' unitCube L).indicator
      (fun _ ↦ ENNReal.ofReal ‖c i * star (b i)‖) t
    simp only [Set.indicator, Set.mem_preimage, ← hx]
    have hchar : ‖ch t‖₊ = 1 := NNReal.eq (norm_fourierChar _)
    by_cases hU : u t - site i ∈ unitCube L <;>
      by_cases hV : v t - other i ∈ unitCube L <;>
      simp [term, cubePulse, hU, hV, hchar, enorm_eq_nnnorm]
  have hfin : (∑' i, ∫⁻ t, ‖term i t‖ₑ) ≠ ∞ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (ENNReal.tsum_le_tsum hbound)
    rw [ENNReal.tsum_mul_right,
      ← ENNReal.ofReal_tsum_of_nonneg (fun i ↦ norm_nonneg _) hc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (isCompact_unitCube L).measure_lt_top
  unfold crossAmbiguity
  change (∫ t, cubeTrain L site c (u t) * star (cubeTrain L other b (v t)) * ch t) = _
  simp_rw [ht]
  rw [integral_tsum hm hfin]
  congr 1
  funext i
  simp only [term, translate, u, v, ch]
  exact integral_const_mul _ _

end AmbiguityHoles.Local
