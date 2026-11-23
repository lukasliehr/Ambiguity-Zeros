module

public import LeanCode.Analysis.Basic
import Mathlib.Tactic.Module

@[expose] public section

/-! Finite packet expansions and support at the selected delays. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace AmbiguityHoles.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} {R : ι → E → ℂ} {W : E → ℂ}

/-- On the positive selected band, only the packet-to-train terms survive.
The coefficients may be complex because every conjugate-linear term vanishes. -/
theorem selected_ambiguity_finset
    (hW : MemLp W 2 volume) (hR : ∀ i, MemLp (R i) 2 volume)
    {x ω : E} (hWW : ambiguity W x ω = 0)
    (hWR : ∀ i, crossAmbiguity W (R i) x ω = 0)
    (hRR : ∀ i j, crossAmbiguity (R i) (R j) x ω = 0)
    (s : Finset ι) (c : ι → ℂ) :
    ambiguity (W + ∑ i ∈ s, c i • R i) x ω =
      ∑ i ∈ s, c i * crossAmbiguity (R i) W x ω := by
  classical
  let T := fun i ↦ c i • R i
  have hT (i : ι) : MemLp (T i) 2 volume := (hR i).const_smul _
  have hsum (u : Finset ι) : MemLp (∑ i ∈ u, T i) 2 volume := by
    induction u using Finset.induction_on with
    | empty => simpa using (MemLp.zero : MemLp (0 : E → ℂ) 2 volume)
    | insert i u hi ih => simpa [Finset.sum_insert hi] using (hT i).add ih
  have hleft (f : E → ℂ) (hf : MemLp f 2 volume) (u : Finset ι) :
      crossAmbiguity (∑ i ∈ u, T i) f x ω =
        ∑ i ∈ u, c i * crossAmbiguity (R i) f x ω := by
    induction u using Finset.induction_on with
    | empty => simp [crossAmbiguity_zero_left hf]
    | insert i u hi ih =>
      simp only [Finset.sum_insert hi]
      rw [crossAmbiguity_add_left (hT i) (hsum u) hf, ih,
        crossAmbiguity_smul_left (c i) (hR i) hf]
  have hright (f : E → ℂ) (hf : MemLp f 2 volume) (u : Finset ι) :
      crossAmbiguity f (∑ i ∈ u, T i) x ω =
        ∑ i ∈ u, star (c i) * crossAmbiguity f (R i) x ω := by
    induction u using Finset.induction_on with
    | empty => simp [crossAmbiguity_zero_right hf]
    | insert i u hi ih =>
      simp only [Finset.sum_insert hi]
      rw [crossAmbiguity_add_right hf (hT i) (hsum u), ih,
        crossAmbiguity_smul_right (c i) hf (hR i)]
  change ambiguity (W + ∑ i ∈ s, T i) x ω = _
  rw [ambiguity_add hW (hsum s), hWW, hleft W hW s, hright W hW s, ambiguity,
    hleft _ (hsum s) s]
  have hzero (i : ι) : crossAmbiguity (R i) (∑ j ∈ s, T j) x ω = 0 := by
    simp [hright _ (hR i) s, hRR]
  simp [hzero, hWR]

/-- A selected direction whose two unwanted terms vanish acts affinely on the
ambiguity at that point. This also applies after adjoining any background
terms whose cross-ambiguities with the direction vanish there. -/
theorem selected_ambiguity_add_smul {f r : E → ℂ}
    (hf : MemLp f 2 volume) (hr : MemLp r 2 volume) {x ω : E}
    (hfr : crossAmbiguity f r x ω = 0) (hrr : ambiguity r x ω = 0) (c : ℂ) :
    ambiguity (f + c • r) x ω = ambiguity f x ω + c * crossAmbiguity r f x ω := by
  have hc : MemLp (c • r) 2 volume := hr.const_smul c
  have hself : ambiguity (c • r) x ω = 0 := by
    rw [ambiguity, crossAmbiguity_smul_left c hr hc, crossAmbiguity_smul_right c hr hr,
      ← ambiguity, hrr, mul_zero, mul_zero]
  rw [ambiguity_add hf hc, crossAmbiguity_smul_right c hf hr,
    crossAmbiguity_smul_left c hr hf, hfr, hself, mul_zero, add_zero, add_zero]

/-- Cross-ambiguity vanishes at any delay outside the difference of the
pointwise supports. -/
theorem selected_crossAmbiguity_zero_of_support
    {f g : E → ℂ} {x ω : E} {U V : Set E}
    (hf : Function.support f ⊆ U) (hg : Function.support g ⊆ V)
    (hsep : ∀ p ∈ U, ∀ q ∈ V, p - q ≠ x) :
    crossAmbiguity f g x ω = 0 := by
  rw [crossAmbiguity]
  apply integral_eq_zero_of_ae
  filter_upwards with t
  by_cases hp : f (t + (1 / 2 : ℝ) • x) = 0
  · rw [hp, zero_mul, zero_mul]; rfl
  by_cases hq : g (t - (1 / 2 : ℝ) • x) = 0
  · rw [hq, star_zero, mul_zero, zero_mul]; rfl
  exfalso
  exact hsep _ (hf hp) _ (hg hq) (by module)

/-- Vanishing on the positive hole gives vanishing on its central reflection. -/
theorem selected_kill_reflection {K : Set (E × E)}
    (hW : MemLp W 2 volume) (hkill : ∀ z ∈ K, ambiguity W z.1 z.2 = 0) :
    ∀ z ∈ K ∪ (fun p : E × E ↦ -p) '' K, ambiguity W z.1 z.2 = 0 := by
  rintro z (hz | ⟨p, hp, rfl⟩)
  · exact hkill z hz
  · change ambiguity W (-p.1) (-p.2) = 0
    rw [ambiguity_neg_neg hW p.1 p.2, hkill p hp, star_zero]

/-- Dense nonvanishing in the positive band gives support throughout the closure
of that region and throughout the closure of its central reflection. -/
theorem selected_support_reflection {U Z : Set (E × E)}
    (hW : MemLp W 2 volume) (hdense : U ⊆ closure Z)
    (halive : ∀ z ∈ Z, ambiguity W z.1 z.2 ≠ 0) :
    closure U ∪ closure ((fun p : E × E ↦ -p) '' U) ⊆
      tsupport (fun z : E × E ↦ ambiguity W z.1 z.2) := by
  let A : E × E → ℂ := fun z ↦ ambiguity W z.1 z.2
  have hpos : U ⊆ tsupport A :=
    hdense.trans (closure_mono halive)
  have hnegZ : (fun p : E × E ↦ -p) '' Z ⊆ Function.support A := by
    rintro _ ⟨p, hp, rfl⟩
    change ambiguity W (-p.1) (-p.2) ≠ 0
    rw [ambiguity_neg_neg hW p.1 p.2]
    exact fun hz ↦ halive p hp (star_eq_zero.mp hz)
  have hneg : (fun p : E × E ↦ -p) '' U ⊆ tsupport A := by
    calc
      (fun p : E × E ↦ -p) '' U ⊆ (fun p : E × E ↦ -p) '' closure Z :=
        image_mono hdense
      _ ⊆ closure ((fun p : E × E ↦ -p) '' Z) :=
        image_closure_subset_closure_image continuous_neg
      _ ⊆ tsupport A := closure_mono hnegZ
  exact union_subset (closure_minimal hpos isClosed_closure)
    (closure_minimal hneg isClosed_closure)

end AmbiguityHoles.Analysis
