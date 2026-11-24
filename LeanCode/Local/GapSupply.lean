module

public import LeanCode.Local.InnerPackets
public import LeanCode.Local.TrainWeights
public import LeanCode.Local.FourierGap
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

open Set
open scoped BigOperators
namespace AmbiguityHoles.Local

private theorem inner_eq_sum_coords {d : ℕ} (x y : Coord d) :
    inner ℝ x y = ∑ j, x j * y j := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl (fun j _ ↦ by change y j*x j = x j*y j; ring)

private theorem trainSeries_eq_series {d : ℕ} (θ : Coord d)
    (c : CosetIndex d → ℂ) (ω : Coord d) :
    trainSeries (latticeSite θ) c ω = series (frequency (WithLp.ofLp θ)) c (WithLp.ofLp ω) := by
  unfold trainSeries series character
  apply tsum_congr
  intro i
  have hi (j : Fin d) : latticeSite θ i j = frequency (WithLp.ofLp θ) i j := by
    cases i <;> rfl
  rw [inner_eq_sum_coords]
  simp_rw [hi, mul_comm (ω _)]

theorem exists_gapSupply {d : ℕ} (θ : Coord d)
    (hθ : ∀ i, 0 < θ i ∧ θ i < 1/2)
    (hres : ∀ n : Lattice d, Real.fourierChar (-(inner ℝ θ (integerSite n))) = 1 → n = 0)
    {ρ : ℝ} (_hρ : 0 ≤ ρ) (hr : ρ < 1/2) :
    ∃ w : CosetIndex d → ℂ, (Summable fun i ↦ ‖w i‖^2) ∧ GapSupply (latticeSite θ) w ρ := by
  classical
  let t : Coordinates d := WithLp.ofLp θ
  let ξ := frequency t
  have hres' (n : Lattice d) (hn : character t (latticePoint n) = 1) : n = 0 := by
    apply hres n
    apply Subtype.ext
    rw [inner_eq_sum_coords]
    exact hn
  let a : Coordinates d := fun _ ↦ -1/2
  let J : Set (Coordinates d) := {u | ∀ j, |u j| ≤ ρ}
  have hJ : IsCompact J := by
    have hJ' : J = {u : Coordinates d | ∀ j, u j ∈ Icc (-ρ) ρ} := by
      ext u
      simp [J, abs_le]
    rw [hJ']
    exact isCompact_pi_infinite (fun _ ↦ isCompact_Icc)
  have hJa : J ⊆ openCell a := by
    intro u hu j
    have huj := abs_le.mp (hu j)
    exact ⟨by change -(1:ℝ)/2 < u j; linarith [huj.1],
      by change u j < -(1:ℝ)/2+1; linarith [huj.2]⟩
  obtain ⟨w,hwne,hw,hquot⟩ := exists_train_weight θ hθ
  let fromRapid (c : CosetIndex d → ℂ) (hc : RapidCoefficients ξ c) : TrainCoefficients w :=
    ⟨fun i ↦ c i / star (w i), hquot c hc, by
      simpa only [div_mul_cancel₀ _ (star_ne_zero.mpr (hwne _))] using hc.summable_norm⟩
  have hfrom (c : CosetIndex d → ℂ) (hc : RapidCoefficients ξ c) (ω : Coord d) :
      (fromRapid c hc).series (latticeSite θ) ω = series ξ c (WithLp.ofLp ω) := by
    have he : (fun i ↦ (fromRapid c hc).coeff i * star (w i)) = c := by
      funext i
      exact div_mul_cancel₀ _ (star_ne_zero.mpr (hwne i))
    rw [TrainCoefficients.series,he,trainSeries_eq_series]
  refine ⟨w,hw,?_⟩
  intro F hF hFbox
  let e := PiLp.homeomorph 2 (fun _ : Fin d ↦ ℝ)
  let F' := e '' F
  have hF' : IsCompact F' := hF.image e.continuous
  have hFJ : F' ⊆ J := by
    rintro u ⟨x,hx,rfl⟩
    exact hFbox hx
  obtain ⟨c,hc,hzero,hmul⟩ := exists_rapid_gap hres' hF' hJ hFJ hJa
  refine ⟨fromRapid c hc, ?_, ?_⟩
  · intro ω
    rw [hfrom c hc ω, hzero]
    exact e.injective.mem_set_image
  · intro h k
    let M (u : Coordinates d) : ℂ :=
      ∏ j, differenceCoefficient (k j) (halfPhase (-(2*Real.pi*u j*h j)))
    have hM : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) M := by
      dsimp [M]
      apply contDiff_prod
      intro j _
      have H : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun u : Coordinates d ↦ halfPhase (-(2*Real.pi*u j*h j))) := by
        have H' : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
            (fun u : Coordinates d ↦ -(2*Real.pi*u j*h j)) := by fun_prop
        unfold halfPhase
        exact ((Complex.ofRealCLM.contDiff.comp H').neg.mul contDiff_const).cexp
      by_cases h0 : k j = 0
      · simp only [differenceCoefficient,h0,if_pos]
        exact contDiff_const
      by_cases h1 : k j = 1
      · have hk (r : ℂ) : differenceCoefficient (k j) r = -(1 + r) := by
          simp [differenceCoefficient, h1]
        simpa only [hk] using (contDiff_const.add H).neg
      · have hk (r : ℂ) : differenceCoefficient (k j) r = r := by
          simp [differenceCoefficient, h0, h1]
        simpa only [hk] using H
    obtain ⟨b,hb,hbmul⟩ := hmul M hM
    refine ⟨fromRapid b hb, fun ω hω ↦ ?_⟩
    rw [hfrom b hb ω, hfrom c hc ω, hbmul _ hω]

end AmbiguityHoles.Local
