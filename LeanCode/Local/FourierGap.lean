module

public import LeanCode.Local.FourierPeak
public import LeanCode.Local.FourierExpansion
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

public section

noncomputable section

open Set
open scoped ContDiff BigOperators

namespace AmbiguityHoles.Local

private theorem character_smooth {d : ℕ} (θ : Coordinates d) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (character θ) := by
  let r : Coordinates d → ℝ := fun x ↦ 2 * Real.pi * -(∑ i, θ i * x i)
  have hr : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) r := by dsimp [r]; fun_prop
  unfold character
  simp_rw [Real.fourierChar_apply]
  exact ((Complex.ofRealCLM.contDiff.comp hr).mul contDiff_const).cexp

private theorem exists_lattice_add_representative {d : ℕ} (a x : Coordinates d) :
    ∃ n : Lattice d, x = latticePoint n + torusRepresentative a (torusPoint x) := by
  let s := torusRepresentative a (torusPoint x)
  have h (i : Fin d) : ((s i : ℝ) : UnitAddCircle) = (x i : UnitAddCircle) :=
    congrFun (torusPoint_representative a (torusPoint x)) i
  have hn (i : Fin d) : ∃ n : ℤ, (n : ℝ) = x i - s i := by
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp
      (show ((x i - s i : ℝ) : UnitAddCircle) = 0 by rw [AddCircle.coe_sub, h i, sub_self])
    exact ⟨n, by simpa only [zsmul_eq_mul, mul_one] using hn⟩
  choose n hni using hn
  exact ⟨n, funext fun i ↦ by change x i = (n i : ℝ) + s i; rw [hni]; ring⟩

private theorem exists_peak_expansion {d : ℕ} {F : Set (Coordinates d)}
    {a : Coordinates d} (p : SmoothPeak F a)
    (M : Coordinates d → ℂ) (hM : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) M) :
    ∃ g : C(UnitAddTorus (Fin d), ℂ), ∃ c : Lattice d → ℂ,
      RapidCoefficients latticePoint c ∧
      (∀ x ∈ rightCell a, g (torusPoint x) = (p.η x : ℂ) * M x) ∧
      ∀ x, g (torusPoint x) = series latticePoint c x := by
  let e : Coordinates d → ℂ := fun x ↦ p.η x
  let f : Coordinates d → ℂ := e * M
  have he : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) e := Complex.ofRealCLM.contDiff.comp p.smooth
  have hce : HasCompactSupport e := p.compact.comp_left (g := Complex.ofReal) (by simp)
  have hcf : HasCompactSupport f := hce.mul_right
  have hse : tsupport e ⊆ tsupport p.η := by
    apply closure_mono
    intro x hx h
    exact hx (by simp [e, show p.η x = 0 from h])
  have hsf : tsupport f ⊆ openCell a :=
    tsupport_mul_subset_left.trans (hse.trans p.support_inside)
  obtain ⟨g, hg⟩ := exists_torus_periodization (he.mul hM).continuous hcf hsf
  obtain ⟨c, hc, hcg⟩ := exists_rapid_periodic_expansion f (he.mul hM) hcf hsf g hg
  exact ⟨g, c, hc, hg, hcg⟩

private theorem rapid_sum {d : ℕ} (θ : Coordinates d) {c b : Lattice d → ℂ}
    (hc : RapidCoefficients latticePoint c) (hb : RapidCoefficients latticePoint b) :
    RapidCoefficients (frequency θ) (Sum.elim c b) := by
  intro k
  apply Summable.sum
  · exact hc k
  · change Summable (fun n : Lattice d ↦ ‖b n‖ * (1 + ‖latticePoint n + θ‖) ^ k)
    have hs := (hb k).mul_right ((1 + ‖θ‖) ^ k)
    refine hs.of_nonneg_of_le (fun n ↦ by positivity) ?_
    intro n
    change ‖b n‖ * (1 + ‖latticePoint n + θ‖) ^ k ≤
      ‖b n‖ * (1 + ‖latticePoint n‖) ^ k * (1 + ‖θ‖) ^ k
    rw [mul_assoc, ← mul_pow]
    gcongr
    nlinarith [norm_add_le (latticePoint n) θ, mul_nonneg (norm_nonneg (latticePoint n)) (norm_nonneg θ)]

private theorem series_sum {d : ℕ} (θ : Coordinates d) {c b : Lattice d → ℂ}
    (hc : RapidCoefficients latticePoint c) (hb : RapidCoefficients latticePoint b) (x : Coordinates d) :
    series (frequency θ) (Sum.elim c b) x =
      series latticePoint c x + series latticePoint b x * character θ x := by
  unfold series
  have h₁ := summable_series (ξ := latticePoint) hc.summable_norm x
  have h₂ := (summable_series (ξ := latticePoint) hb.summable_norm x).mul_right (character θ x)
  have hsum (n : Lattice d) :
      b n * character (latticePoint n + θ) x =
        (b n * character (latticePoint n) x) * character θ x := by
    rw [character_add_left, mul_assoc]
  have hs₂ : Summable (fun n ↦ b n * character (latticePoint n + θ) x) := by simpa only [hsum] using h₂
  rw [Summable.tsum_sum (f := fun i ↦ Sum.elim c b i * character (frequency θ i) x) h₁ hs₂]
  change _ + (∑' n, b n * character (latticePoint n + θ) x) = _
  simp_rw [hsum, tsum_mul_right]
  rfl

private def delta {d : ℕ} (n : Lattice d) : ℂ := if n = 0 then 1 else 0

private theorem delta_rapid {d : ℕ} : RapidCoefficients latticePoint (delta (d := d)) := by
  intro k
  apply summable_of_hasFiniteSupport
  apply (Set.finite_singleton (0 : Lattice d)).subset
  intro n hn
  by_contra h
  exact hn (by simp [delta, show n ≠ 0 from h])

private theorem delta_series {d : ℕ} (x : Coordinates d) :
    series latticePoint delta x = 1 := by
  rw [series, tsum_eq_single (0 : Lattice d)]
  · simp [delta, latticePoint, character]
  · intro n hn
    simp [delta, hn]

/-- Two lattice cosets suffice for an exact compact gap and for multiplying its series
by any smooth function on a compact subset of the chosen cell. -/
theorem exists_rapid_gap {d : ℕ} {θ a : Coordinates d}
    (hnonres : ∀ n : Lattice d, character θ (latticePoint n) = 1 → n = 0)
    {F J : Set (Coordinates d)} (hF : IsCompact F) (hJ : IsCompact J)
    (hFJ : F ⊆ J) (hJa : J ⊆ openCell a) :
    ∃ c : CosetIndex d → ℂ, RapidCoefficients (frequency θ) c ∧
      (∀ x, series (frequency θ) c x = 0 ↔ x ∈ F) ∧
      ∀ M : Coordinates d → ℂ, ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) M →
        ∃ b : CosetIndex d → ℂ, RapidCoefficients (frequency θ) b ∧
        ∀ x ∈ J, series (frequency θ) b x = series (frequency θ) c x * M x := by
  obtain ⟨p⟩ := exists_smoothPeak hF (hFJ.trans hJa)
  obtain ⟨q⟩ := exists_smoothPeak hJ hJa
  let C : Coordinates d → ℂ := fun x ↦ -character θ x
  have hC : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) C := (character_smooth θ).neg
  obtain ⟨g, c, hc, hg, hgc⟩ := exists_peak_expansion p C hC
  refine ⟨Sum.elim c delta, rapid_sum θ hc delta_rapid, ?_, ?_⟩
  · intro x
    rw [series_sum θ hc delta_rapid, delta_series, one_mul, ← hgc x]
    constructor
    · intro hzero
      let s := torusRepresentative a (torusPoint x)
      have hs : s ∈ rightCell a := torusRepresentative_mem _ _
      have htor : torusPoint s = torusPoint x := torusPoint_representative _ _
      obtain ⟨n, hx⟩ := exists_lattice_add_representative a x
      change x = latticePoint n + s at hx
      have hval : character θ x = (p.η s : ℂ) * character θ s := by
        rw [← htor, hg s hs, show C s = -character θ s from rfl, mul_neg, neg_add_eq_sub,
          sub_eq_zero] at hzero
        exact hzero
      have hz : character θ (latticePoint n) = (p.η s : ℂ) := by
        have hs0 : character θ s ≠ 0 := by
          intro hz
          have he := congrArg norm hz
          rw [norm_character, norm_zero] at he
          exact one_ne_zero he
        apply mul_right_cancel₀ hs0
        rw [← character_add_right, ← hx, hval]
      have hη : p.η s = 1 := by
        simpa [Complex.norm_real, abs_of_nonneg (p.nonneg s)] using (congrArg norm hz).symm
      have hn : n = 0 := hnonres n (by simpa [hη] using hz)
      have hzeroL : latticePoint (0 : Lattice d) = 0 := by
        funext i
        simp [latticePoint]
      have hxs : x = s := by simpa only [hn, hzeroL, zero_add] using hx
      rw [hxs]
      exact (p.eq_one_iff s).mp hη
    · intro hx
      have hcx := openCell_subset_rightCell a (hJa (hFJ hx))
      rw [hg x hcx, (p.eq_one_iff x).mpr hx]
      simp [C]
  · intro M hM
    obtain ⟨g₁, b₁, hb₁, hg₁, hgb₁⟩ := exists_peak_expansion p (C * M) (hC.mul hM)
    obtain ⟨g₂, b₂, hb₂, hg₂, hgb₂⟩ := exists_peak_expansion q M hM
    refine ⟨Sum.elim b₁ b₂, rapid_sum θ hb₁ hb₂, ?_⟩
    intro x hx
    have hrx := openCell_subset_rightCell a (hJa hx)
    rw [series_sum θ hb₁ hb₂, series_sum θ hc delta_rapid, delta_series, one_mul,
      ← hgb₁, ← hgb₂, ← hgc, hg₁ x hrx, hg₂ x hrx, hg x hrx, (q.eq_one_iff x).mpr hx]
    simp only [Pi.mul_apply, Complex.ofReal_one, one_mul]
    ring

end AmbiguityHoles.Local
