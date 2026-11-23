module

public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Data.Countable.Defs
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Push
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology

namespace AmbiguityHoles

/-- Countably many continuous polynomial evaluations can be made simultaneously
nonzero on a closed convex set, if each has a nonzero value somewhere on the set. -/
theorem exists_mem_forall_eval_ne_zero
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [Countable ι] {C : Set E} (hclosed : IsClosed C) (hconv : Convex ℝ C)
    (hne : C.Nonempty) (eval : ι → E → ℂ) (hc : ∀ i, Continuous (eval i))
    (hp : ∀ i x y, ∃ p : Polynomial ℂ, ∀ t : ℝ,
      eval i ((1 - t) • x + t • y) = p.eval (t : ℂ))
    (hw : ∀ i, ∃ x ∈ C, eval i x ≠ 0) :
    ∃ x ∈ C, ∀ i, eval i x ≠ 0 := by
  letI : CompleteSpace C := hclosed.completeSpace_coe
  letI : Nonempty C := hne.to_subtype
  let U (i : ι) : Set C := {x | eval i x ≠ 0}
  have hU (i : ι) : IsOpen (U i) :=
    isOpen_ne_fun ((hc i).comp continuous_subtype_val) continuous_const
  have hD (i : ι) : Dense (U i) := by
    rw [dense_iff_inter_open]
    intro V hV hVne
    obtain ⟨x, hx⟩ := hVne
    obtain ⟨y, hy, hye⟩ := hw i
    obtain ⟨p, heq⟩ := hp i (x : E) y
    have hpne : p ≠ 0 := by
      intro hpz
      apply hye
      simpa [hpz] using heq 1
    obtain ⟨W, hW, hWV⟩ := isOpen_induced_iff.mp hV
    have hxW : (x : E) ∈ W := by
      simpa [← hWV] using hx
    let line (t : ℝ) : E := (1 - t) • (x : E) + t • y
    have hl : Continuous line := by
      dsimp [line]
      fun_prop
    have hnhds : line ⁻¹' W ∈ 𝓝 (0 : ℝ) :=
      (hW.preimage hl).mem_nhds (by simpa [line] using hxW)
    obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
      (mem_nhdsWithin_of_mem_nhds hnhds)
    let ε := min δ 1
    have hε : 0 < ε := lt_min hδ zero_lt_one
    have hinf : ((fun t : ℝ => (t : ℂ)) '' Ioo 0 ε).Infinite :=
      (Ioo_infinite hε).image Complex.ofReal_injective.injOn
    have hex : ∃ t ∈ Ioo 0 ε, p.eval (t : ℂ) ≠ 0 := by
      by_contra! h
      apply (hinf.mono (t := {z | p.IsRoot z}) ?_) (Polynomial.finite_setOf_isRoot hpne)
      rintro _ ⟨t, ht, rfl⟩
      exact h t ht
    obtain ⟨t, ht, htn⟩ := hex
    have ht₁ := ht.2.trans_le (min_le_right δ 1)
    have hlineC : line t ∈ C :=
      hconv x.property hy (sub_nonneg.mpr ht₁.le) ht.1.le (sub_add_cancel 1 t)
    refine ⟨⟨line t, hlineC⟩, ?_, ?_⟩
    · rw [← hWV]
      exact hsub ⟨ht.1, ht.2.trans_le (min_le_left δ 1)⟩
    · exact (heq t).trans_ne htn
  obtain ⟨x, hx⟩ := (dense_iInter_of_isOpen hU hD).nonempty
  exact ⟨x, x.property, fun i => mem_iInter.mp hx i⟩

/-- Countable testing on the complement of the prescribed closed hole suffices
to determine the full interior of the zero set. -/
theorem exists_mem_interior_zero_eq
    {E Z ι : Type*} [Countable ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace Z] {C : Set E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    (eval : E → Z → ℂ) (hc : ∀ z, Continuous (fun x => eval x z))
    (hp : ∀ z x y, ∃ p : Polynomial ℂ, ∀ t : ℝ,
      eval ((1 - t) • x + t • y) z = p.eval (t : ℂ))
    {Ω : Set Z} (hΩ : interior (closure Ω) = Ω)
    (hvan : ∀ x ∈ C, ∀ z ∈ Ω, eval x z = 0)
    (points : ι → Z) (hdense : (closure Ω)ᶜ ⊆ closure (range points))
    (hw : ∀ i, ∃ x ∈ C, eval x (points i) ≠ 0) :
    ∃ x ∈ C, interior {z | eval x z = 0} = Ω := by
  let S := (closure Ω)ᶜ
  obtain ⟨x, hx, hxe⟩ := exists_mem_forall_eval_ne_zero hclosed hconv hne
    (fun i x => eval x (points i)) (fun i => hc (points i)) (fun i => hp (points i)) hw
  let N := {z | eval x z ≠ 0}
  have hsubset : S ⊆ closure N := hdense.trans (closure_mono (range_subset_iff.mpr hxe))
  have hs : closure S = Ωᶜ := by
    dsimp [S]
    rw [closure_compl, hΩ]
  have hcomp : Ωᶜ ⊆ closure N := by
    rw [← hs]
    exact closure_minimal hsubset isClosed_closure
  refine ⟨x, hx, le_antisymm ?_ ?_⟩
  · have he : interior {z | eval x z = 0} = (closure N)ᶜ := by
      rw [← interior_compl]
      congr 1
      ext z
      simp [N]
    rw [he, ← compl_compl Ω]
    exact compl_subset_compl.mpr hcomp
  · have ho : IsOpen Ω := hΩ ▸ isOpen_interior
    exact interior_maximal (hvan x hx) ho

end AmbiguityHoles
