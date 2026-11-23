module

public import LeanCode.Local.BandGeometry
public import LeanCode.Local.CubeKernel
public import LeanCode.Local.Selected
public import LeanCode.Local.Trains
public import LeanCode.Local.OuterCorridor
public import LeanCode.Local.Lattice
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

@[expose] public section

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace AmbiguityHoles.Local
open Analysis

def corridorCenter {d : ℕ} (θ : Coord (d+1)) (s : ℝ)
    (i : Bool × Bool × Bool) : UnitAddCircle :=
  ((if i.1 then θ 0 else 0) + (if i.2.1 then s else 0) +
    (if i.2.2 then s else -s) : ℝ)

def GuardedStart {d : ℕ} (θ : Coord (d+1)) (s L ρ : ℝ) (α : Coord (d+1)) : Prop :=
  ∀ i, 2*L+5*ρ < dist (α 0 : UnitAddCircle) (corridorCenter θ s i)

def pairStart {d : ℕ} (α q : Coord d) (b : Bool) : Coord d :=
  if b then α+q else α

def pairRegion {d : ℕ} (α q : Coord d) (ε : ℝ) : Set (Coord d) :=
  {t | ∃ b : Bool, t - pairStart α q b ∈ unitCube ε}

def pairPulse {d : ℕ} (α q : Coord d) (ε : ℝ) : Coord d → ℂ :=
  if q = 0 then translate α (cubePulse ε) else
    translate (α+q) (cubePulse ε) + translate α (cubePulse ε)

theorem support_translate_pulse {d : ℕ} (a : Coord d) (ε : ℝ) :
    Function.support (translate a (cubePulse ε)) ⊆ {t | t-a ∈ unitCube ε} := by
  intro t ht
  by_contra hs
  exact ht (by simp [translate, cubePulse, show t-a ∉ unitCube ε from hs])

theorem support_pairPulse {d : ℕ} (α q : Coord d) (ε : ℝ) :
    Function.support (pairPulse α q ε) ⊆ pairRegion α q ε := by
  classical
  intro t ht
  by_contra h
  have h₀ : translate α (cubePulse ε) t = 0 := by
    by_contra hn
    exact h ⟨false, support_translate_pulse α ε hn⟩
  have h₁ : translate (α+q) (cubePulse ε) t = 0 := by
    by_contra hn
    exact h ⟨true, support_translate_pulse (α+q) ε hn⟩
  apply ht
  by_cases hq : q=0 <;> simp [pairPulse, hq, h₀, h₁]

theorem pairPulse_memLp {d : ℕ} (α q : Coord d) (ε : ℝ) :
    MemLp (pairPulse α q ε) 2 volume := by
  classical
  by_cases hq : q = 0
  · simpa only [pairPulse, if_pos hq] using translate_memLp α (cubePulse_memLp ε 2)
  · simpa only [pairPulse, if_neg hq] using (translate_memLp (α+q) (cubePulse_memLp ε 2)).add
      (translate_memLp α (cubePulse_memLp ε 2))

private theorem pulse_difference {d : ℕ} {a b p q : Coord d} {u v r : ℝ}
    (hp : p-a ∈ unitCube u) (hq : q-b ∈ unitCube v) (hu : u ≤ r) (hv : v ≤ r) :
    coordBox r ((p-q)-(a-b)) := by
  intro i
  have up := hp i
  have uq := hq i
  simp only [mem_Icc, PiLp.sub_apply] at up uq ⊢
  exact abs_le.mpr ⟨by linarith [up.1, uq.2], by linarith [up.2,uq.1]⟩

private theorem pulse_cross_zero {d : ℕ} {a b x ω : Coord d} {r : ℝ}
    (h : ¬ coordBox r (x-(a-b))) :
    crossAmbiguity (translate a (cubePulse r)) (translate b (cubePulse r)) x ω = 0 := by
  apply selected_crossAmbiguity_zero_of_support (support_translate_pulse a r)
    (support_translate_pulse b r)
  rintro p hp q hq rfl
  exact h (pulse_difference hp hq le_rfl le_rfl)

private theorem exists_radius_off_band {d : ℕ} {q : Coord d} {s ρ : ℝ}
    (hq : q ∉ band s ρ) : ∃ r > 0, ∀ x ∈ band s ρ, ¬ coordBox r (x-q) := by
  change ¬ ∀ j, |(q-s • firstAxis d) j| ≤ ρ at hq
  obtain ⟨j,hj⟩ := not_forall.mp hq
  let c := (s • firstAxis d) j
  change ¬ |q j-c| ≤ ρ at hj
  let r := (|q j-c|-ρ)/2
  refine ⟨r, by dsimp [r]; linarith [lt_of_not_ge hj], ?_⟩
  intro x hx ho
  have hv : |x j-c| ≤ ρ := hx j
  have hu : |x j-q j| ≤ r := ho j
  have htri := abs_sub_le (q j) (x j) c
  rw [abs_sub_comm (q j) (x j)] at htri
  dsimp [r] at hu
  linarith [lt_of_not_ge hj]

theorem zero_not_mem_band {d : ℕ} {s ρ : ℝ} (h : ρ < s) (hρ : 0 ≤ ρ) :
    (0 : Coord (d+1)) ∉ band s ρ := by
  intro hz
  have hz₀ := hz 0
  change |(0:ℝ)-s*1| ≤ ρ at hz₀
  rw [mul_one, zero_sub, abs_neg, abs_of_pos (hρ.trans_lt h)] at hz₀
  exact h.not_ge hz₀

theorem exists_pair_width {d : ℕ} {s ρ : ℝ} (hρ : 0 < ρ) (hs : ρ < s)
    {q ω : Coord (d+1)} (hq : q ∉ band s ρ) (hnq : -q ∉ band s ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ ρ ∧
      (∀ α : Coord (d+1), ambiguity (pairPulse α q ε) q ω ≠ 0) ∧
      ∀ x ∈ band s ρ, ∀ b b' : Bool,
        ¬ coordBox ε (x-(pairStart (0 : Coord (d+1)) q b - pairStart 0 q b')) := by
  obtain ⟨r₀, hr₀, h₀⟩ := exists_radius_off_band (zero_not_mem_band (d := d) hs hρ.le)
  obtain ⟨r₁, hr₁, h₁⟩ := exists_radius_off_band hq
  obtain ⟨r₂, hr₂, h₂⟩ := exists_radius_off_band hnq
  let r := min ρ (min r₀ (min r₁ r₂))
  have hr : 0 < r := lt_min hρ (lt_min hr₀ (lt_min hr₁ hr₂))
  have havoid (ε : ℝ) (he : ε ≤ r) (x : Coord (d+1)) (hx : x ∈ band s ρ) :
      ∀ b b' : Bool, ¬ coordBox ε (x-(pairStart (0 : Coord (d+1)) q b - pairStart 0 q b')) := by
    have hρ₀ : ε ≤ r₀ := he.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hρ₁ : ε ≤ r₁ := he.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    have hρ₂ : ε ≤ r₂ := he.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
    have h0 : ¬ coordBox ε (x-0) := fun H ↦ h₀ x hx (fun j ↦ (H j).trans hρ₀)
    have h1 : ¬ coordBox ε (x-q) := fun H ↦ h₁ x hx (fun j ↦ (H j).trans hρ₁)
    have h2 : ¬ coordBox ε (x-(-q)) := fun H ↦ h₂ x hx (fun j ↦ (H j).trans hρ₂)
    intro b b'
    cases b <;> cases b' <;> simp_all [pairStart]
  classical
  by_cases hq0 : q = 0
  · subst q
    obtain ⟨ε,hε,hεr,hn⟩ := exists_small_cubePulse_ambiguity_ne_zero ω hr
    refine ⟨ε,hε,hεr.le.trans (min_le_left _ _), ?_, fun x hx ↦ havoid ε hεr.le x hx⟩
    intro α
    rw [pairPulse, if_pos rfl, ambiguity, crossAmbiguity_translate_translate
      (cubePulse_memLp ε 2) (cubePulse_memLp ε 2), sub_self, sub_zero, ← ambiguity]
    exact mul_ne_zero (by rw [half_phase_fourierChar]; exact halfPhase_ne_zero _) hn
  · obtain ⟨j,hj⟩ : ∃ j, q j ≠ 0 := by
      by_contra! h
      exact hq0 (PiLp.ext h)
    obtain ⟨ε,hε,hεr,hn⟩ := exists_small_cubePulse_ambiguity_ne_zero ω
      (lt_min hr (abs_pos.mpr hj) : 0 < min r |q j|)
    have he := hεr.le.trans (min_le_left r |q j|)
    have he' := hεr.trans_le (min_le_right r |q j|)
    refine ⟨ε,hε,he.trans (min_le_left _ _), ?_, fun x hx ↦ havoid ε he x hx⟩
    intro α
    let A := translate (α+q) (cubePulse ε)
    let B := translate α (cubePulse ε)
    have hA : MemLp A 2 volume := translate_memLp _ (cubePulse_memLp ε 2)
    have hB : MemLp B 2 volume := translate_memLp _ (cubePulse_memLp ε 2)
    have hAA : ambiguity A q ω = 0 := by
      apply pulse_cross_zero
      rw [sub_self, sub_zero]
      exact fun H ↦ he'.not_ge (H j)
    have hBB : ambiguity B q ω = 0 := by
      apply pulse_cross_zero
      rw [sub_self, sub_zero]
      exact fun H ↦ he'.not_ge (H j)
    have hBA : crossAmbiguity B A q ω = 0 := by
      apply pulse_cross_zero
      intro H
      have Hj := H j
      have eq : (q-(α-(α+q))) j = 2*q j := by simp [PiLp.add_apply]; ring
      rw [eq, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)] at Hj
      linarith [abs_nonneg (q j)]
    have hAB : crossAmbiguity A B q ω ≠ 0 := by
      rw [crossAmbiguity_translate_translate (cubePulse_memLp ε 2) (cubePulse_memLp ε 2),
        show α+q-α = q by abel, sub_self, ← ambiguity, half_phase_fourierChar]
      exact mul_ne_zero (halfPhase_ne_zero _) hn
    rw [pairPulse, if_neg hq0]
    change ambiguity (A + B) q ω ≠ 0
    rw [ambiguity_add hA hB, hAA, hBB, hBA]
    simpa using hAB

private theorem integer_circle_zero (n : ℤ) : ((n : ℝ) : UnitAddCircle) = 0 := by
  rw [← zsmul_one, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]

private theorem guarded_difference {d : ℕ} {θ : Coord (d+1)} {s L ρ ε : ℝ}
    {α p t x : Coord (d+1)}
    (hα : GuardedStart θ s L ρ α) (hε : ε ≤ ρ) (hL : 0 ≤ L) (hρ : 0 ≤ ρ)
    (hp : p-α ∈ unitCube ε)
    (ht : t ∈ trainRegion (latticeSite θ) L ({0} ∪ band s (L+3*ρ)))
    (sign : Bool) (hx : x ∈ band (if sign then s else -s) ρ) :
    p-t ≠ x := by
  rintro rfl
  obtain ⟨a, ha, i, hi⟩ := ht
  obtain ⟨u,n,hn⟩ : ∃ (u : Bool) (n : ℤ),
      latticeSite θ i 0 = (n : ℝ) + (if u then θ 0 else 0) := by
    cases i with
    | inl j => exact ⟨false,j 0,by simp⟩
    | inr j => exact ⟨true,j 0,by simp [PiLp.add_apply]⟩
  obtain ⟨v,hv⟩ : ∃ v : Bool, |a 0-(if v then s else 0)| ≤ L+3*ρ := by
    rcases ha with ha | ha
    · have ha0 : a=0 := ha
      subst a
      exact ⟨false, by simp; linarith⟩
    · exact ⟨true, by simpa [firstAxis, PiLp.sub_apply, PiLp.smul_apply] using ha 0⟩
  have H := abs_le.mp (hx 0)
  simp only [PiLp.sub_apply, PiLp.smul_apply,
    show firstAxis (d+1) 0 = 1 from rfl, smul_eq_mul, mul_one] at H
  have H₁ := hp 0
  have H₂ := hi 0
  simp only [mem_Icc, PiLp.sub_apply, PiLp.add_apply] at H₁ H₂
  rw [hn] at H₂
  let c := (if u then θ 0 else 0) + (if v then s else 0) + (if sign then s else -s)
  have hdist : |α 0 - ((n : ℝ)+c)| ≤ 2*L+5*ρ := by
    have Hv := abs_le.mp hv
    dsimp [c]
    exact abs_le.mpr ⟨by linarith [H.1,H.2,H₁.1,H₁.2,H₂.1,H₂.2,Hv.1,Hv.2],
      by linarith [H.1,H.2,H₁.1,H₁.2,H₂.1,H₂.2,Hv.1,Hv.2]⟩
  have hquot := unitAddCircle_dist_le (α 0) ((n : ℝ)+c)
  rw [AddCircle.coe_add, integer_circle_zero, zero_add] at hquot
  exact (hα (u,v,sign)).not_ge (hquot.trans hdist)

theorem guarded_pair_cross_zero {d : ℕ} {θ : Coord (d+1)} {s L ρ ε : ℝ}
    {α q x ω : Coord (d+1)} {f : Coord (d+1) → ℂ}
    (ha : ∀ b, GuardedStart θ s L ρ (pairStart α q b))
    (hε : ε ≤ ρ) (hL : 0 ≤ L) (hρ : 0 ≤ ρ)
    (hf : Function.support f ⊆ trainRegion (latticeSite θ) L ({0} ∪ band s (L+3*ρ)))
    (hx : x ∈ band s ρ) :
    crossAmbiguity (pairPulse α q ε) f x ω = 0 ∧
      crossAmbiguity f (pairPulse α q ε) x ω = 0 := by
  constructor
  · apply selected_crossAmbiguity_zero_of_support (support_pairPulse α q ε) hf
    rintro p ⟨b,hb⟩ t ht
    exact guarded_difference (ha b) hε hL hρ hb ht true hx
  · apply selected_crossAmbiguity_zero_of_support hf (support_pairPulse α q ε)
    rintro t ht p ⟨b,hb⟩ hEq
    apply guarded_difference (ha b) hε hL hρ hb ht false (neg_mem_band hx)
    rw [← hEq, neg_sub]

theorem exists_outer_packets {d : ℕ} (θ : Coord (d+1)) {s L ρ : ℝ}
    (hρ : 0 < ρ) (hs : ρ < s) (hL : 0 < L) (hr : 32*(2*L+5*ρ) < 1)
    (z : ℕ → Coord (d+1) × Coord (d+1))
    (hz : ∀ n, (z n).1 ∉ band s ρ ∧ -(z n).1 ∉ band s ρ) :
    ∃ P : ℕ → Coord (d+1) → ℂ,
      (∀ n, MemLp (P n) 2 volume) ∧ (∀ n, ambiguity (P n) (z n).1 (z n).2 ≠ 0) ∧
      (∀ n m x ω, x ∈ band s ρ → crossAmbiguity (P n) (P m) x ω = 0) ∧
      ∀ n x ω, x ∈ band s ρ → ∀ f : Coord (d+1) → ℂ,
        Function.support f ⊆ trainRegion (latticeSite θ) L ({0} ∪ band s (L+3*ρ)) →
        crossAmbiguity (P n) f x ω = 0 ∧ crossAmbiguity f (P n) x ω = 0 := by
  classical
  let q (n : ℕ) := (z n).1
  let δ (n : ℕ) : ℝ := 2*|q n 0|+1
  let M (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, (δ k+s+2*ρ+1)
  have hM : Monotone M := by
    apply monotone_nat_of_le_succ
    intro n
    change M n ≤ ∑ k ∈ Finset.range (n+1), (δ k+s+2*ρ+1)
    rw [Finset.sum_range_succ]
    dsimp [δ]
    linarith [abs_nonneg (q n 0)]
  have hplace (n : ℕ) : ∃ a : Coord (d+1), ∀ b,
      M n < pairStart a (q n) b 0 ∧ pairStart a (q n) b 0 ≤ M n+δ n ∧
      GuardedStart θ s L ρ (pairStart a (q n) b) := by
    obtain ⟨r, hr₁, hr₂, hguard⟩ := exists_real_circle_placement
      (corridorCenter θ s) (2*L+5*ρ) (by norm_num; linarith) (by linarith)
      (q n 0) (M n+|q n 0|)
    let a : Coord (d+1) := r • firstAxis (d+1)
    refine ⟨a, ?_⟩
    have ha0 : a 0 = r := by change r * 1 = r; ring
    intro b
    cases b
    · change M n < a 0 ∧ a 0 ≤ M n+δ n ∧ GuardedStart θ s L ρ a
      rw [ha0]
      exact ⟨by linarith [abs_nonneg (q n 0)], by dsimp [δ]; linarith [abs_nonneg (q n 0)],
        fun i ↦ by simpa only [ha0] using (hguard i).1⟩
    · change M n < (a+q n) 0 ∧ (a+q n) 0 ≤ M n+δ n ∧ GuardedStart θ s L ρ (a+q n)
      simp only [PiLp.add_apply, ha0]
      exact ⟨by linarith [neg_abs_le (q n 0)], by dsimp [δ]; linarith [le_abs_self (q n 0)],
        fun i ↦ by simpa only [PiLp.add_apply, ha0] using (hguard i).2⟩
  choose a ha using hplace
  have hwidth (n : ℕ) := exists_pair_width hρ hs (ω := (z n).2) (hz n).1 (hz n).2
  choose ε hε hερ htest hsep using hwidth
  let P (n : ℕ) := pairPulse (a n) (q n) (ε n)
  refine ⟨P, fun n ↦ pairPulse_memLp _ _ _, fun n ↦ htest n (a n), ?_, ?_⟩
  · intro n m x ω hx
    apply selected_crossAmbiguity_zero_of_support (support_pairPulse _ _ _) (support_pairPulse _ _ _)
    rintro p ⟨b,hp⟩ t ⟨b',ht⟩ rfl
    rcases lt_trichotomy n m with hnm | rfl | hmn
    · have hbound := hM (show n+1 ≤ m by omega)
      change (∑ k ∈ Finset.range (n+1), (δ k+s+2*ρ+1)) ≤ M m at hbound
      rw [Finset.sum_range_succ] at hbound
      have H := abs_le.mp (hx 0)
      have H₁ := hp 0
      have H₂ := ht 0
      simp only [mem_Icc, PiLp.sub_apply] at H₁ H₂
      simp only [PiLp.sub_apply, PiLp.smul_apply,
        show firstAxis (d+1) 0 = 1 from rfl, smul_eq_mul, mul_one] at H
      linarith [H.1,H₁.2,H₂.1,(ha n b).2.1,(ha m b').1,hερ n]
    · apply hsep n (p-t) hx b b'
      have H := pulse_difference hp ht (le_rfl : ε n ≤ ε n) le_rfl
      convert H using 2
      cases b <;> cases b' <;> simp [pairStart] <;> abel
    · have hbound := hM (show m+1 ≤ n by omega)
      change (∑ k ∈ Finset.range (m+1), (δ k+s+2*ρ+1)) ≤ M n at hbound
      rw [Finset.sum_range_succ] at hbound
      have H := abs_le.mp (hx 0)
      have H₁ := hp 0
      have H₂ := ht 0
      simp only [mem_Icc, PiLp.sub_apply] at H₁ H₂
      simp only [PiLp.sub_apply, PiLp.smul_apply,
        show firstAxis (d+1) 0 = 1 from rfl, smul_eq_mul, mul_one] at H
      linarith [H.2,H₁.1,H₂.2,(ha n b).1,(ha m b').2.1,hερ m]
  · intro n x ω hx f hf
    exact guarded_pair_cross_zero (fun b ↦ (ha n b).2.2) (hερ n) hL.le hρ.le hf hx

end AmbiguityHoles.Local
