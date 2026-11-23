module

public import LeanCode.Local.Baire
public import LeanCode.Analysis.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Abel

@[expose] public section

noncomputable section

open MeasureTheory Set Polynomial
open scoped Topology

namespace AmbiguityHoles.Local
open Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

abbrev LocalL2 (E : Type*) [MeasureSpace E] : Type _ :=
  Lp ℂ 2 (volume : Measure E)

def lpCross (x ω : E) (f g : Lp ℂ 2 (volume : Measure E)) : ℂ :=
  crossAmbiguity (f : E → ℂ) (g : E → ℂ) x ω

theorem lpCross_add_left (x ω : E) (f g h : Lp ℂ 2 (volume : Measure E)) :
    lpCross x ω (f+g) h = lpCross x ω f h + lpCross x ω g h := by
  rw [lpCross, crossAmbiguity_congr_ae (Lp.memLp (f+g)) ((Lp.memLp f).add (Lp.memLp g))
    (Lp.memLp h) (Lp.memLp h) (Lp.coeFn_add f g) Filter.EventuallyEq.rfl]
  exact crossAmbiguity_add_left (Lp.memLp f) (Lp.memLp g) (Lp.memLp h) x ω

theorem lpCross_add_right (x ω : E) (f g h : Lp ℂ 2 (volume : Measure E)) :
    lpCross x ω f (g+h) = lpCross x ω f g + lpCross x ω f h := by
  rw [lpCross, crossAmbiguity_congr_ae (Lp.memLp f) (Lp.memLp f) (Lp.memLp (g+h))
    ((Lp.memLp g).add (Lp.memLp h)) Filter.EventuallyEq.rfl (Lp.coeFn_add g h)]
  exact crossAmbiguity_add_right (Lp.memLp f) (Lp.memLp g) (Lp.memLp h) x ω

private theorem lpCross_smul_left (x ω : E) (a : ℝ) (f g : Lp ℂ 2 (volume : Measure E)) :
    lpCross x ω (a • f) g = (a : ℂ) * lpCross x ω f g := by
  have heq : ((a • f : Lp ℂ 2 (volume : Measure E)) : E → ℂ) =ᵐ[volume] (a : ℂ) • (f : E → ℂ) := by
    filter_upwards [Lp.coeFn_smul a f] with t ht
    simpa [Pi.smul_apply, Complex.real_smul] using ht
  rw [lpCross, crossAmbiguity_congr_ae (Lp.memLp (a • f)) ((Lp.memLp f).const_smul (a : ℂ))
    (Lp.memLp g) (Lp.memLp g) heq Filter.EventuallyEq.rfl]
  exact crossAmbiguity_smul_left (a : ℂ) (Lp.memLp f) (Lp.memLp g) x ω

private theorem lpCross_smul_right (x ω : E) (a : ℝ) (f g : Lp ℂ 2 (volume : Measure E)) :
    lpCross x ω f (a • g) = (a : ℂ) * lpCross x ω f g := by
  have heq : ((a • g : Lp ℂ 2 (volume : Measure E)) : E → ℂ) =ᵐ[volume] (a : ℂ) • (g : E → ℂ) := by
    filter_upwards [Lp.coeFn_smul a g] with t ht
    simpa [Pi.smul_apply, Complex.real_smul] using ht
  rw [lpCross, crossAmbiguity_congr_ae (Lp.memLp f) (Lp.memLp f) (Lp.memLp (a • g))
    ((Lp.memLp g).const_smul (a : ℂ)) Filter.EventuallyEq.rfl heq,
    crossAmbiguity_smul_right (a : ℂ) (Lp.memLp f) (Lp.memLp g)]
  simp [lpCross]

private theorem lpCross_zero_left (x ω : E) (f : Lp ℂ 2 (volume : Measure E)) :
    lpCross x ω 0 f = 0 := by
  simpa only [zero_smul, Complex.ofReal_zero, zero_mul] using lpCross_smul_left x ω 0 f f

private theorem lpCross_zero_right (x ω : E) (f : Lp ℂ 2 (volume : Measure E)) :
    lpCross x ω f 0 = 0 := by
  simpa only [zero_smul, Complex.ofReal_zero, zero_mul] using lpCross_smul_right x ω 0 f f

theorem lpCross_toLp (x ω : E) {f g : E → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    lpCross x ω (hf.toLp f) (hg.toLp g) = crossAmbiguity f g x ω :=
  crossAmbiguity_congr_ae (Lp.memLp _) hf (Lp.memLp _) hg hf.coeFn_toLp hg.coeFn_toLp x ω

theorem lpCross_polynomial (x ω : E) (f g : Lp ℂ 2 (volume : Measure E)) :
    ∃ p : Polynomial ℂ, ∀ t : ℝ, lpCross x ω ((1-t) • f+t • g) ((1-t) • f+t • g)
      = p.eval (t : ℂ) := by
  refine ⟨(1-X)^2 * C (lpCross x ω f f) +
      (1-X)*X*C (lpCross x ω f g + lpCross x ω g f) +
      X^2*C (lpCross x ω g g), ?_⟩
  intro t
  simp only [lpCross_add_left, lpCross_add_right, lpCross_smul_left, lpCross_smul_right,
    Complex.ofReal_sub, Complex.ofReal_one, eval_add, eval_sub, eval_mul, eval_pow,
    eval_C, eval_X, eval_one]
  ring

theorem exists_add_direction_ne_zero (x ω : E) (f g : Lp ℂ 2 (volume : Measure E))
    (h : lpCross x ω g g ≠ 0) :
    ∃ t : ℝ, lpCross x ω (f+t • g) (f+t • g) ≠ 0 := by
  by_contra! hz
  have h0 := hz 0
  have h1 := hz 1
  have hm := hz (-1)
  simp only [lpCross_add_left, lpCross_add_right, lpCross_smul_left, lpCross_smul_right,
    Complex.ofReal_one, Complex.ofReal_zero, Complex.ofReal_neg, zero_mul, one_mul,
    add_zero, neg_one_mul] at h0 h1 hm
  exact h (by linear_combination (h1 + hm - 2*h0)/2)

theorem lpCross_span_left_zero (x ω : E) {V : Set (Lp ℂ 2 (volume : Measure E))}
    {g : Lp ℂ 2 (volume : Measure E)} (h : ∀ v ∈ V, lpCross x ω v g = 0)
    {v : Lp ℂ 2 (volume : Measure E)} (hv : v ∈ Submodule.span ℝ V) :
    lpCross x ω v g = 0 := by
  induction hv using Submodule.span_induction with
  | mem v hv => exact h v hv
  | zero => exact lpCross_zero_left x ω g
  | add u v _ _ hu hv => rw [lpCross_add_left, hu, hv, add_zero]
  | smul a v _ hv => rw [lpCross_smul_left, hv, mul_zero]

theorem lpCross_span_right_zero (x ω : E) {V : Set (Lp ℂ 2 (volume : Measure E))}
    {g : Lp ℂ 2 (volume : Measure E)} (h : ∀ v ∈ V, lpCross x ω g v = 0)
    {v : Lp ℂ 2 (volume : Measure E)} (hv : v ∈ Submodule.span ℝ V) :
    lpCross x ω g v = 0 := by
  induction hv using Submodule.span_induction with
  | mem v hv => exact h v hv
  | zero => exact lpCross_zero_right x ω g
  | add u v _ _ hu hv => rw [lpCross_add_right, hu, hv, add_zero]
  | smul a v _ hv => rw [lpCross_smul_right, hv, mul_zero]

theorem realize_from_directions
    {Ω : Set (E × E)} (hΩ : interior (closure Ω) = Ω)
    (W : Lp ℂ 2 (volume : Measure E)) (V : Set (Lp ℂ 2 (volume : Measure E)))
    (hc : ∀ x ω, Continuous (fun f : Lp ℂ 2 (volume : Measure E) ↦ lpCross x ω f f))
    (hW : ∀ z ∈ Ω, lpCross z.1 z.2 W W = 0)
    (hWV : ∀ z ∈ Ω, ∀ v ∈ V, lpCross z.1 z.2 W v = 0 ∧ lpCross z.1 z.2 v W = 0)
    (hV : ∀ z ∈ Ω, ∀ v ∈ V, ∀ u ∈ V, lpCross z.1 z.2 v u = 0)
    (points : ℕ → E × E) (hdense : (closure Ω)ᶜ ⊆ closure (range points))
    (hw : ∀ n, ∃ v ∈ Submodule.span ℝ V,
      lpCross (points n).1 (points n).2 (W+v) (W+v) ≠ 0) :
    ∃ f : E → ℂ, MemLp f 2 volume ∧ openZeros f = Ω := by
  let S := Submodule.span ℝ V
  let C := (fun v : Lp ℂ 2 (volume : Measure E) ↦ W + v) '' (S : Set _)
  have hC : Convex ℝ C := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ a b ha hb hab
    refine ⟨a • u + b • v, S.add_mem (S.smul_mem a hu) (S.smul_mem b hv), ?_⟩
    rw [smul_add, smul_add]
    calc
      W + (a • u + b • v) = (a+b) • W + (a • u + b • v) := by rw [hab, one_smul]
      _ = _ := by rw [add_smul]; abel
  have hn : (closure C).Nonempty := ⟨W, subset_closure ⟨0, S.zero_mem, add_zero W⟩⟩
  have hvan : ∀ f ∈ closure C, ∀ z ∈ Ω, lpCross z.1 z.2 f f = 0 := by
    intro f hf z hzΩ
    apply closure_minimal (s := C) (t := {f | lpCross z.1 z.2 f f = 0}) _
      (isClosed_eq (hc z.1 z.2) continuous_const) hf
    rintro _ ⟨v, hv, rfl⟩
    have h₁ := lpCross_span_right_zero z.1 z.2 (fun u hu ↦ (hWV z hzΩ u hu).1) hv
    have h₂ := lpCross_span_left_zero z.1 z.2 (fun u hu ↦ (hWV z hzΩ u hu).2) hv
    have h₃ : lpCross z.1 z.2 v v = 0 :=
      lpCross_span_left_zero z.1 z.2
        (fun u hu ↦ lpCross_span_right_zero z.1 z.2 (hV z hzΩ u hu) hv) hv
    change lpCross z.1 z.2 (W+v) (W+v) = 0
    simp [lpCross_add_left, lpCross_add_right, h₁, h₂, h₃, hW z hzΩ]
  obtain ⟨f, _, hf⟩ := exists_mem_interior_zero_eq isClosed_closure hC.closure hn
    (fun f (z : E × E) ↦ lpCross z.1 z.2 f f) (fun z ↦ hc z.1 z.2)
    (fun z ↦ lpCross_polynomial z.1 z.2) hΩ hvan points hdense
    (fun n ↦ by
      obtain ⟨v, hv, hne⟩ := hw n
      exact ⟨W+v, subset_closure ⟨v, hv, rfl⟩, hne⟩)
  exact ⟨f, Lp.memLp f, hf⟩

end AmbiguityHoles.Local
