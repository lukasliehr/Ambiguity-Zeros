module

public import LeanCode.Local.TrainCalculus
public import LeanCode.Local.BandGeometry
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section
open MeasureTheory Set
namespace AmbiguityHoles.Local
open Analysis

def trainSeries {d : ℕ} {ι : Type*} (site : ι → Coord d)
    (c : ι → ℂ) (ω : Coord d) : ℂ :=
  ∑' i, c i * (Real.fourierChar (-(inner ℝ ω (site i))) : ℂ)


section
variable {d : ℕ} {ι : Type*} {site : ι → Coord (d+1)} {σ s L ρ : ℝ}
  (G : TrainGeometry site σ s L ρ)

include G

theorem cross_reference_self (w : ι → ℂ) {x ω : Coord (d+1)} (hx : x ∈ band s ρ) :
    ambiguity (cubeTrain L site w) x ω = 0 := by
  have hzero : coordBox (2*(L+3*ρ)) ((0 : Coord (d+1)) - 0) := by
    intro i
    simp
    linarith [G.rho_pos, G.width]
  apply cubeTrain_cross_zero
  intro i j
  simpa only [add_zero, one_mul] using
    train_no_overlap_same G (i := i) (j := j) (Or.inl rfl)
      (by simpa only [one_mul] using (show coordBox ρ (x - s • firstAxis (d + 1)) from hx)) hzero

theorem cross_shifted_trains (c b : ι → ℂ) {a a' x ω : Coord (d+1)}
    (ha : a ∈ band s (L+3*ρ)) (ha' : a' ∈ band s (L+3*ρ)) (hx : x ∈ band s ρ) :
    crossAmbiguity (translate a (cubeTrain L site c)) (translate a' (cubeTrain L site b)) x ω = 0 := by
  have hab : coordBox (2*(L+3*ρ)) (a-a') := by
    intro i
    have u := abs_le.mp (ha i)
    have v := abs_le.mp (ha' i)
    simp only [PiLp.sub_apply] at u v ⊢
    exact abs_le.mpr ⟨by linarith [u.1,v.2], by linarith [u.2,v.1]⟩
  rw [translate_cubeTrain, translate_cubeTrain]
  apply cubeTrain_cross_zero
  intro i j
  exact train_no_overlap_same G (Or.inl rfl) (by simpa only [one_mul] using (show coordBox ρ (x - s • firstAxis (d + 1)) from hx)) hab

theorem cross_reference_shifted (w c : ι → ℂ) {a x ω : Coord (d+1)}
    (ha : a ∈ band s (L+3*ρ)) (hx : x ∈ band s ρ) :
    crossAmbiguity (cubeTrain L site w) (translate a (cubeTrain L site c)) x ω = 0 := by
  rw [translate_cubeTrain]
  apply cubeTrain_cross_zero
  intro i j ho
  exact (by norm_num : (1 : ℝ) ≠ -1) ((train_overlap_mixed G (e := 1) (Or.inl rfl)
    (by simpa only [one_mul] using (show coordBox ρ (x - s • firstAxis (d + 1)) from hx)) ha ho).2)

theorem cross_shifted_reference [Countable ι] (w c : ι → ℂ)
    (hc : Summable fun i ↦ ‖c i * star (w i)‖)
    {a x ω : Coord (d+1)} (ha : a ∈ band s (L+3*ρ)) (hx : x ∈ band s ρ) :
    crossAmbiguity (translate a (cubeTrain L site c)) (cubeTrain L site w) x ω =
      halfPhase (Real.pi * inner ℝ ω a) * trainSeries site (fun i ↦ c i * star (w i)) ω *
        ambiguity (cubePulse L) (x-a) ω := by
  rw [translate_cubeTrain]
  have hsep (i j : ι) (hij : i ≠ j) :
      ¬ coordBox L (x - ((site i+a)-site j)) := by
    intro h
    have hn : coordBox L (-x - (site j - (site i+a))) := by
      convert coordBox_neg h using 1
      module
    exact hij ((train_overlap_mixed G (e := -1) (Or.inr rfl)
      (by simpa only [band, mem_setOf_eq, neg_one_mul, neg_smul] using neg_mem_band hx) ha hn).1.symm)
  have hw : ∀ i j, i ≠ j → ∃ k, L < |site i k-site j k| := by
    simpa only [add_zero] using shifted_width_sep G 0
  rw [cubeTrain_cross_matched (shifted_width_sep G a) hw hc x ω hsep]
  have hphase (i : ι) :
      (Real.fourierChar (-(inner ℝ ω ((1/2 : ℝ) • ((site i+a)+site i)))) : ℂ) =
      halfPhase (Real.pi * inner ℝ ω a) *
        (Real.fourierChar (-(inner ℝ ω (site i))) : ℂ) := by
    have hv : (1/2 : ℝ) • ((site i+a)+site i) = (1/2 : ℝ) • a + site i := by module
    rw [hv, inner_add_right, neg_add, fourierChar_add, half_phase_fourierChar]
  simp_rw [crossAmbiguity_translate_translate (cubePulse_memLp L 2) (cubePulse_memLp L 2),
    hphase, show ∀ i, site i + a - site i = a by intro i; abel]
  rw [trainSeries, ambiguity, ← tsum_mul_left, ← tsum_mul_right]
  congr 1
  funext i
  ring

end
end AmbiguityHoles.Local
