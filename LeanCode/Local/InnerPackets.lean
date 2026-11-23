module

public import LeanCode.Local.BandTrains
public import LeanCode.Local.SeparationGeometry
public import LeanCode.Local.CubeKernel
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

@[expose] public section

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace AmbiguityHoles.Local
open Analysis

structure TrainCoefficients {ι : Type*} (w : ι → ℂ) where
  coeff : ι → ℂ
  sq_summable : Summable fun i ↦ ‖coeff i‖^2
  product_summable : Summable fun i ↦ ‖coeff i * star (w i)‖

def TrainCoefficients.series {d : ℕ} {ι : Type*} {w : ι → ℂ}
    (c : TrainCoefficients w) (site : ι → Coord d) (ω : Coord d) : ℂ :=
  trainSeries site (fun i ↦ c.coeff i * star (w i)) ω

def GapSupply {d : ℕ} {ι : Type*} (site : ι → Coord d) (w : ι → ℂ) (ρ : ℝ) : Prop :=
  ∀ F : Set (Coord d), IsCompact F → F ⊆ {ω | coordBox ρ ω} →
    ∃ c : TrainCoefficients w, (∀ ω, c.series site ω = 0 ↔ ω ∈ F) ∧
      ∀ (h : Coord d) (k : Fin d → Fin 3), ∃ b : TrainCoefficients w, ∀ ω,
        coordBox ρ ω → b.series site ω =
          c.series site ω * ∏ j, differenceCoefficient (k j) (halfPhase (-(2*Real.pi*ω j*h j)))

theorem support_shifted_train {d : ℕ} {ι : Type*} {site : ι → Coord d} {L : ℝ}
    {S : Set (Coord d)} {a : Coord d} (ha : a ∈ S) (c : ι → ℂ) :
    Function.support (translate a (cubeTrain L site c)) ⊆ trainRegion site L S := by
  rw [translate_cubeTrain]
  intro t ht
  obtain ⟨i, hi⟩ := support_cubeTrain c ht
  exact ⟨a, ha, i, hi⟩

private theorem cross_finset_left {d : ℕ} {ι : Type*} (T : ι → Coord d → ℂ)
    (ht : ∀ i, MemLp (T i) 2 volume) (w : Coord d → ℂ) (hw : MemLp w 2 volume)
    (u : Finset ι) (x ω : Coord d) :
    crossAmbiguity (∑ i ∈ u, T i) w x ω = ∑ i ∈ u, crossAmbiguity (T i) w x ω := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [crossAmbiguity_zero_left hw]
  | insert i u hi ih =>
    simp only [Finset.sum_insert hi]
    rw [crossAmbiguity_add_left (ht i) (memLp_finset_sum' u fun j _ ↦ ht j) hw, ih]

private theorem halfPhase_dot {d : ℕ} (a ω : Coord d) :
    halfPhase (Real.pi * inner ℝ ω a) = ∏ j, halfPhase (Real.pi * ω j * a j) := by
  have hsum (u : Finset (Fin d)) (r : Fin d → ℝ) :
      halfPhase (∑ j ∈ u, r j) = ∏ j ∈ u, halfPhase (r j) := by
    classical
    induction u using Finset.induction_on with
    | empty => simp [halfPhase]
    | insert j u hj ih => simp [Finset.sum_insert hj, Finset.prod_insert hj, halfPhase_add, ih]
  rw [PiLp.inner_apply, Finset.mul_sum, hsum]
  apply Finset.prod_congr rfl
  intro j _
  congr 1
  change Real.pi * (a j * ω j) = Real.pi * ω j * a j
  ring

theorem exists_inner_packet {d : ℕ} {ι : Type*} [Countable ι]
    {site : ι → Coord (d+1)} {σ s L ρ : ℝ} (G : TrainGeometry site σ s L ρ)
    (w : ι → ℂ) (hw : Summable fun i ↦ ‖w i‖^2) (gap : GapSupply site w ρ)
    {K : Set (Coord (d+1) × Coord (d+1))} (hK : IsCompact K)
    (hKx : ∀ z ∈ K, z.1 ∈ band s ρ) (hKω : ∀ z ∈ K, coordBox ρ z.2)
    {y η : Coord (d+1)} (hy : y ∈ band s ρ) (hz : (y,η) ∉ K) :
    ∃ R : Coord (d+1) → ℂ, MemLp R 2 volume ∧
      Function.support R ⊆ trainRegion site L (band s (L+3*ρ)) ∧
      (∀ z ∈ K, crossAmbiguity R (cubeTrain L site w) z.1 z.2 = 0) ∧
      crossAmbiguity R (cubeTrain L site w) y η ≠ 0 := by
  classical
  let W := cubeTrain L site w
  have hbase : ∀ i j, i ≠ j → ∃ k, L < |site i k-site j k| := by
    simpa only [add_zero] using shifted_width_sep G 0
  have hW : MemLp W 2 volume := cubeTrain_memLp hbase hw
  have hL : 0 < L := by linarith [G.width, G.rho_pos]
  by_cases hη : coordBox ρ η
  · obtain ⟨h, hh, hFη⟩ := exists_packetBox hK.isClosed hz G.rho_pos
    let F := projectedFrequencies K (packetBox y h)
    obtain ⟨c, hc, hmult⟩ := gap F
      (isCompact_projectedFrequencies hK (isClosed_packetBox y h))
      (projectedFrequencies_subset hKω)
    choose b hb using hmult h
    let ξ : Coord (d+1) := WithLp.toLp 2 fun j ↦ y j - L - h j
    let v (k : Fin (d+1) → Fin 3) : Coord (d+1) :=
      WithLp.toLp 2 fun j ↦ ((k j).val : ℝ)*h j
    let a (k : Fin (d+1) → Fin 3) := ξ + v k
    let T (k : Fin (d+1) → Fin 3) := translate (a k) (cubeTrain L site (b k).coeff)
    have ha (k : Fin (d+1) → Fin 3) : a k ∈ band s (L+3*ρ) := by
      intro j
      have hyj := abs_le.mp (hy j)
      have hk : ((k j).val : ℝ) ≤ 2 := by exact_mod_cast (show (k j).val ≤ 2 by omega)
      have hv₀ : 0 ≤ ((k j).val : ℝ) * h j := mul_nonneg (by positivity) (hh j).1.le
      have hv₂ : ((k j).val : ℝ) * h j ≤ 2 * h j :=
        mul_le_mul_of_nonneg_right hk (hh j).1.le
      change |y j-L-h j+((k j).val : ℝ)*h j-(s • firstAxis (d+1)) j| ≤ L+3*ρ
      change -ρ ≤ y j-(s • firstAxis (d+1)) j ∧ y j-(s • firstAxis (d+1)) j ≤ ρ at hyj
      exact abs_le.mpr ⟨by linarith [hyj.1,(hh j).2.1], by linarith [hyj.2,(hh j).2.1]⟩
    have hT (k : Fin (d+1) → Fin 3) : MemLp (T k) 2 volume :=
      translate_memLp _ (cubeTrain_memLp hbase (b k).sq_summable)
    have hsupp (k : Fin (d+1) → Fin 3) : Function.support (T k) ⊆
        trainRegion site L (band s (L+3*ρ)) := support_shifted_train (ha k) _
    let R := ∑ k, T k
    have hR (x ω : Coord (d+1)) (hx : x ∈ band s ρ) (hω : coordBox ρ ω) :
        crossAmbiguity R W x ω =
          (halfPhase (Real.pi * inner ℝ ω ξ) * c.series site ω *
            ∏ j, halfPhase (Real.pi*ω j*L)) *
          ∏ j, (intervalDifference L (h j) ((x-ξ) j) (ω j) : ℂ) := by
      rw [show R = ∑ k ∈ Finset.univ, T k from rfl, cross_finset_left T hT W hW]
      rw [← difference_product, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [show crossAmbiguity (T k) W x ω =
          halfPhase (Real.pi * inner ℝ ω (a k)) * (b k).series site ω *
            ambiguity (cubePulse L) (x-a k) ω from
          cross_shifted_reference G w _ (b k).product_summable (ha k) hx]
      rw [cubePulse_ambiguity, hb k ω hω]
      rw [show a k = ξ + v k from rfl, inner_add_right, mul_add, halfPhase_add, halfPhase_dot (v k)]
      have hsub (j : Fin (d+1)) :
          (x - (ξ+v k)) j = (x-ξ) j - ((k j).val : ℝ)*h j := by
        change x j - (ξ j + ((k j).val : ℝ)*h j) = x j-ξ j-((k j).val : ℝ)*h j
        ring
      simp_rw [hsub]
      let A (j : Fin (d+1)) := halfPhase (Real.pi * ω j * (v k) j)
      let B (j : Fin (d+1)) := differenceCoefficient (k j) (halfPhase (-(2*Real.pi*ω j*h j)))
      let C (j : Fin (d+1)) := halfPhase (Real.pi * ω j * L)
      let D (j : Fin (d+1)) := (intervalAmplitude L ((x-ξ) j - ((k j).val : ℝ)*h j) (ω j) : ℂ)
      change (halfPhase _ * (∏ j, A j)) * (c.series site ω * (∏ j, B j)) *
          (∏ j, C j * D j) =
        (halfPhase _ * c.series site ω * (∏ j, C j)) * (∏ j, A j * B j * D j)
      suffices he : (∏ j, A j) * (∏ j, B j) * (∏ j, C j * D j) =
          (∏ j, C j) * (∏ j, A j * B j * D j) by
        calc
          _ = (halfPhase (Real.pi * inner ℝ ω ξ) * c.series site ω) *
                ((∏ j, A j) * (∏ j, B j) * (∏ j, C j * D j)) := by ring
          _ = _ := by rw [he]; ring
      simp only [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun j _ ↦ by ring
    refine ⟨R, memLp_finset_sum' Finset.univ (fun k _ ↦ hT k), ?_, ?_, ?_⟩
    · intro t ht
      by_contra hn
      apply ht
      change (∑ k, T k) t = 0
      rw [Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro k _
      by_contra hne
      exact hn (hsupp k hne)
    · intro ⟨x,ω⟩ hxy
      rw [hR x ω (hKx _ hxy) (hKω _ hxy)]
      by_cases hbox : x ∈ packetBox y h
      · rw [(hc ω).2 (mem_projectedFrequencies hxy hbox), mul_zero, zero_mul, zero_mul]
      · have he : ∃ j, ¬ |x j - y j| ≤ h j := by simpa only [packetBox, mem_setOf_eq, not_forall] using hbox
        obtain ⟨j,hj⟩ := he
        have hdiff : intervalDifference L (h j) ((x-ξ) j) (ω j) = 0 := by
          by_contra hne
          exact hj (localized_coordinate (by linarith [G.width,G.rho_pos])
            (hh j).1 (hh j).2.1 ((hKx _ hxy) j) (hy j) hne)
        have hprod : (∏ i, (intervalDifference L (h i) ((x-ξ) i) (ω i) : ℂ)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ j) (Complex.ofReal_eq_zero.mpr hdiff)
        rw [hprod, mul_zero]
    · rw [hR y η hy hη]
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero (halfPhase_ne_zero _) ?_)
        (Finset.prod_ne_zero_iff.mpr fun j _ ↦ halfPhase_ne_zero _))
        (Finset.prod_ne_zero_iff.mpr fun j _ ↦ ?_)
      · exact fun hz ↦ hFη ((hc η).1 hz)
      · have hξ : (y-ξ) j = L+h j := by
          change y j-(y j-L-h j) = _
          ring
        rw [hξ, intervalDifference_at_tip (hh j).1 (by linarith [G.width,(hh j).2.1])]
        exact Complex.ofReal_ne_zero.mpr (sinc_mul_ne_zero (hh j).1 (hh j).2.2)
  · have hex (j : Fin (d+1)) := intervalAmplitude_exists_ne_zero hL (η j)
    choose β hβ hβne using hex
    let a : Coord (d+1) := WithLp.toLp 2 fun j ↦ y j - β j
    let F := projectedFrequencies K (packetBox a (WithLp.toLp 2 fun _ ↦ L))
    have ha : a ∈ band s (L+3*ρ) := by
      intro j
      have hj := abs_le.mp (hy j)
      change |y j-β j-(s • firstAxis (d+1)) j| ≤ L+3*ρ
      change -ρ ≤ y j-(s • firstAxis (d+1)) j ∧ y j-(s • firstAxis (d+1)) j ≤ ρ at hj
      exact abs_le.mpr ⟨by linarith [hj.1, (hβ j).2,G.rho_pos],
        by linarith [hj.2,(hβ j).1,G.rho_pos]⟩
    have hF : F ⊆ {ω | coordBox ρ ω} := projectedFrequencies_subset hKω
    obtain ⟨c,hc,_⟩ := gap F (isCompact_projectedFrequencies hK (isClosed_packetBox _ _)) hF
    let R := translate a (cubeTrain L site c.coeff)
    have hR (x ω : Coord (d+1)) (hx : x ∈ band s ρ) :
        crossAmbiguity R W x ω =
          halfPhase (Real.pi * inner ℝ ω a) * c.series site ω *
            ambiguity (cubePulse L) (x-a) ω :=
      cross_shifted_reference G w _ c.product_summable ha hx
    refine ⟨R, translate_memLp _ (cubeTrain_memLp hbase c.sq_summable),
      support_shifted_train ha _, ?_, ?_⟩
    · intro ⟨x,ω⟩ hxy
      rw [hR x ω (hKx _ hxy)]
      by_cases hbox : x ∈ packetBox a (WithLp.toLp 2 fun _ ↦ L)
      · rw [(hc ω).2 (mem_projectedFrequencies hxy hbox), mul_zero, zero_mul]
      · have he : ∃ j, ¬ |x j - a j| ≤ L := by
          simpa only [packetBox, mem_setOf_eq, not_forall] using hbox
        obtain ⟨j,hj⟩ := he
        have hdiff : intervalAmplitude L ((x-a) j) (ω j) = 0 :=
          intervalAmplitude_eq_zero (le_of_lt (lt_of_not_ge hj))
        have hprod : (∏ i, halfPhase (Real.pi * ω i * L) *
            (intervalAmplitude L ((x-a) i) (ω i) : ℂ)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ j) (mul_eq_zero.mpr (Or.inr (Complex.ofReal_eq_zero.mpr hdiff)))
        rw [cubePulse_ambiguity, hprod, mul_zero]
    · rw [hR y η hy, cubePulse_ambiguity]
      refine mul_ne_zero (mul_ne_zero (halfPhase_ne_zero _) (fun h ↦ hη (hF ((hc η).1 h))))
        (Finset.prod_ne_zero_iff.mpr fun j _ ↦ mul_ne_zero (halfPhase_ne_zero _) ?_)
      have hj : (y-a) j = β j := by
        change y j-(y j-β j) = _
        ring
      rw [hj]
      exact Complex.ofReal_ne_zero.mpr (hβne j)

end AmbiguityHoles.Local
