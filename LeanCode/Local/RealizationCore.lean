module

public import LeanCode.Local.InnerPackets
public import LeanCode.Local.OuterPackets
public import LeanCode.Local.RealizationBaire
public import LeanCode.Analysis.Continuity
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped BigOperators
namespace AmbiguityHoles.Local
open Analysis

private theorem trainRegion_delay {d : ℕ} {ι : Type*} {site : ι → Coord d} {L : ℝ}
    {A B : Set (Coord d)} {p q : Coord d}
    (hp : p ∈ trainRegion site L A) (hq : q ∈ trainRegion site L B) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ i j, coordBox L ((p-q)-((site i+a)-(site j+b))) := by
  obtain ⟨a,ha,i,hi⟩ := hp
  obtain ⟨b,hb,j,hj⟩ := hq
  refine ⟨a,ha,b,hb,i,j,?_⟩
  intro k
  have H := hi k
  have H' := hj k
  simp only [mem_Icc, PiLp.sub_apply, PiLp.add_apply] at H H' ⊢
  exact abs_le.mpr ⟨by linarith [H.1,H'.2], by linarith [H.2,H'.1]⟩

private theorem shiftedRegion_cross_zero {d : ℕ} {ι : Type*}
    {site : ι → Coord (d+1)} {σ s L ρ : ℝ} (G : TrainGeometry site σ s L ρ)
    {f g : Coord (d+1) → ℂ} {x ω : Coord (d+1)} (hx : x ∈ band s ρ)
    (hf : Function.support f ⊆ trainRegion site L (band s (L+3*ρ)))
    (hg : Function.support g ⊆ trainRegion site L (band s (L+3*ρ))) :
    crossAmbiguity f g x ω = 0 := by
  apply selected_crossAmbiguity_zero_of_support hf hg
  rintro p hp q hq rfl
  obtain ⟨a,ha,b,hb,i,j,hij⟩ := trainRegion_delay hp hq
  have hab : coordBox (2*(L+3*ρ)) (a-b) := by
    intro k
    have H := abs_le.mp (ha k)
    have H' := abs_le.mp (hb k)
    simp only [PiLp.sub_apply] at H H' ⊢
    exact abs_le.mpr ⟨by linarith [H.1,H'.2], by linarith [H.2,H'.1]⟩
  exact (train_no_overlap_same G (i := i) (j := j) (Or.inl rfl)
    (by simpa only [one_mul] using
      (show coordBox ρ (p - q - s • firstAxis (d + 1)) from hx)) hab) hij

private theorem referenceRegion_cross_zero {d : ℕ} {ι : Type*}
    {site : ι → Coord (d+1)} {σ s L ρ : ℝ} (G : TrainGeometry site σ s L ρ)
    {f g : Coord (d+1) → ℂ} {x ω : Coord (d+1)} (hx : x ∈ band s ρ)
    (hf : Function.support f ⊆ trainRegion site L {0})
    (hg : Function.support g ⊆ trainRegion site L (band s (L+3*ρ))) :
    crossAmbiguity f g x ω = 0 := by
  apply selected_crossAmbiguity_zero_of_support hf hg
  rintro p hp q hq rfl
  obtain ⟨a,ha,b,hb,i,j,hij⟩ := trainRegion_delay hp hq
  have ha0 : a=0 := ha
  subst a
  exact (by norm_num : (1 : ℝ) ≠ -1) (train_overlap_mixed G (e := 1) (Or.inl rfl)
    (by simpa only [one_mul] using
      (show coordBox ρ (p - q - s • firstAxis (d + 1)) from hx)) hb (by simpa only [add_zero] using hij)).2

private theorem trainRegion_mono {d : ℕ} {ι : Type*} {site : ι → Coord d} {L : ℝ}
    {S T : Set (Coord d)} (h : S ⊆ T) :
    trainRegion site L S ⊆ trainRegion site L T := by
  rintro t ⟨a,ha,i,hi⟩
  exact ⟨a,h ha,i,hi⟩

private theorem opposite_band_disjoint {d : ℕ} {s ρ : ℝ} (hs : ρ < s)
    {x : Coord (d+1)} (hx : x ∈ band s ρ) :
    -x ∉ band s ρ := by
  intro h
  have h₁ := abs_le.mp (hx 0)
  have h₂ := abs_le.mp (h 0)
  simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, firstAxis,
    smul_eq_mul, Fin.val_zero, ite_true, mul_one] at h₁ h₂
  linarith [h₁.1,h₂.1]

private theorem coordBox_of_mem_closedBall {d : ℕ} {x y : Coord d} {ρ : ℝ}
    (h : x ∈ Metric.closedBall y ρ) :
    coordBox ρ (x-y) := by
  intro i
  have hd : ‖x-y‖ ≤ ρ := by simpa only [Metric.mem_closedBall, dist_eq_norm] using h
  exact (Real.norm_eq_abs _ ▸ PiLp.norm_apply_le (x-y) i).trans hd

theorem localRealization_of_supply {d : ℕ} (θ : Coord (d+1)) {σ s L ρ : ℝ}
    (G : TrainGeometry (latticeSite θ) σ s L ρ) (hr : 32*(2*L+5*ρ) < 1)
    (w : ((Fin (d+1) → ℤ) ⊕ (Fin (d+1) → ℤ)) → ℂ) (hw : Summable fun i ↦ ‖w i‖^2)
    (gap : GapSupply (latticeSite θ) w ρ) :
    ∃ e : Coord (d+1), e ≠ 0 ∧ ∃ N : Set (Coord (d+1) × Coord (d+1)),
      IsOpen N ∧ (e,0) ∈ N ∧
        ∀ U : Set (Coord (d+1) × Coord (d+1)), IsOpen U →
          interior (closure U) = U → U ⊆ N →
          ∃ f : Coord (d+1) → ℂ, MemLp f 2 volume ∧
            openZeros f = U ∪ ((fun z ↦ -z) '' U) := by
  classical
  let E := Coord (d+1)
  let e : E := s • firstAxis (d+1)
  let N : Set (E × E) := Metric.ball e ρ ×ˢ Metric.ball 0 ρ
  have hs : ρ < s := by linarith [G.near,G.width,G.rho_pos]
  have hL : 0 < L := by linarith [G.width,G.rho_pos]
  have he : e ≠ 0 := by
    intro h
    have H := congrArg (fun x : E ↦ x 0) h
    change s*1=0 at H
    linarith [G.rho_pos]
  refine ⟨e,he,N,Metric.isOpen_ball.prod Metric.isOpen_ball,
    ⟨Metric.mem_ball_self G.rho_pos,Metric.mem_ball_self G.rho_pos⟩,?_⟩
  intro U hU hreg hUN
  let K := closure U
  let nH : (E × E) ≃ₜ (E × E) := Homeomorph.neg _
  let Ω := U ∪ nH '' U
  have hclosure : closure Ω = K ∪ nH '' K := by
    change closure (U ∪ nH '' U) = _
    rw [closure_union, ← nH.image_closure]
  have hKsub : K ⊆ Metric.closedBall e ρ ×ˢ Metric.closedBall (0:E) ρ :=
    closure_minimal (hUN.trans (Set.prod_mono Metric.ball_subset_closedBall Metric.ball_subset_closedBall))
      (Metric.isClosed_closedBall.prod Metric.isClosed_closedBall)
  have hK : IsCompact K := ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).of_isClosed_subset
    isClosed_closure hKsub
  have hKx (z : E × E) (hz : z ∈ K) : z.1 ∈ band s ρ :=
    coordBox_of_mem_closedBall (hKsub hz).1
  have hKω (z : E × E) (hz : z ∈ K) : coordBox ρ z.2 := by
    simpa only [sub_zero] using coordBox_of_mem_closedBall (hKsub hz).2
  have hdisj : Disjoint K (nH '' K) := by
    rw [Set.disjoint_left]
    rintro z hz ⟨u,hu,rfl⟩
    exact opposite_band_disjoint hs (hKx u hu) (hKx _ hz)
  have hΩ : interior (closure Ω) = Ω := by
    rw [hclosure, interior_union_of_disjoint_closure, hreg, ← nH.image_interior, hreg]
    have hKclosed : IsClosed K := isClosed_closure
    have hnKclosed : IsClosed (nH '' K) := nH.isClosedMap _ hKclosed
    simpa only [hKclosed.closure_eq, hnKclosed.closure_eq] using hdisj
  let X := (closure Ω)ᶜ
  have h0X : (0 : E × E) ∈ X := by
    rw [show X = (closure Ω)ᶜ from rfl,hclosure]
    intro h
    rcases h with h | ⟨z,hz,heq⟩
    · exact zero_not_mem_band hs G.rho_pos.le (hKx _ h)
    · have hez : z=0 := by simpa [nH] using heq
      subst z
      exact zero_not_mem_band hs G.rho_pos.le (hKx _ hz)
  letI : Nonempty X := ⟨⟨0,h0X⟩⟩
  obtain ⟨D,hD,hDense⟩ := exists_countable_dense X
  letI : Countable D := hD.to_subtype
  letI : Nonempty D := hDense.nonempty.to_subtype
  obtain ⟨enum,henum⟩ := exists_surjective_nat D
  let z (n : ℕ) : E × E := (enum n).1.1
  have hz (n : ℕ) : z n ∈ X := (enum n).1.2
  have hzdense : X ⊆ closure (range z) := by
    intro p hp
    apply closure_mono _ (continuous_subtype_val.range_subset_closure_image_dense hDense ⟨⟨p,hp⟩,rfl⟩)
    rintro q ⟨v,hv,rfl⟩
    obtain ⟨n,hn⟩ := henum ⟨v,hv⟩
    exact ⟨n, congrArg (fun y : D ↦ y.1.1) hn⟩
  let outer (n : ℕ) : E × E :=
    if (z n).1 ∈ band s ρ ∨ -(z n).1 ∈ band s ρ then 0 else z n
  have houter (n : ℕ) : (outer n).1 ∉ band s ρ ∧ -(outer n).1 ∉ band s ρ := by
    by_cases hh : (z n).1 ∈ band s ρ ∨ -(z n).1 ∈ band s ρ
    · simpa [outer,hh] using zero_not_mem_band (d := d) hs G.rho_pos.le
    · simpa only [outer,if_neg hh] using not_or.mp hh
  obtain ⟨P,hP,hPne,hPP,hPF⟩ := exists_outer_packets θ G.rho_pos hs hL hr outer houter
  let W := cubeTrain L (latticeSite θ) w
  have hwLp : MemLp W 2 volume :=
    cubeTrain_memLp (by simpa only [add_zero] using shifted_width_sep G 0) hw
  let Wl := hwLp.toLp W
  have hWsupport : Function.support W ⊆ trainRegion (latticeSite θ) L {0} := by
    intro t ht
    obtain ⟨i,hi⟩ := support_cubeTrain w ht
    exact ⟨0,rfl,i,by simpa only [add_zero] using hi⟩
  let I (f : E → ℂ) : Prop :=
    Function.support f ⊆ trainRegion (latticeSite θ) L (band s (L+3*ρ)) ∧
      ∀ z ∈ K, crossAmbiguity f W z.1 z.2 = 0
  let Pℓ (n : ℕ) := (hP n).toLp (P n)
  let V : Set (Lp ℂ 2 (volume : Measure E)) :=
    {v | ∃ f : E → ℂ, ∃ hf : MemLp f 2 volume, I f ∧ v = hf.toLp f} ∪ range Pℓ
  have hWVpos (p : E × E) (hp : p ∈ K) :
      ∀ v ∈ V, lpCross p.1 p.2 Wl v = 0 ∧ lpCross p.1 p.2 v Wl = 0 := by
    rintro v (⟨f,hf,hI,rfl⟩ | ⟨n,rfl⟩)
    · rw [lpCross_toLp p.1 p.2 hwLp hf, lpCross_toLp p.1 p.2 hf hwLp]
      exact ⟨referenceRegion_cross_zero G (hKx p hp) hWsupport hI.1, hI.2 p hp⟩
    · rw [lpCross_toLp p.1 p.2 hwLp (hP n), lpCross_toLp p.1 p.2 (hP n) hwLp]
      exact (hPF n p.1 p.2 (hKx p hp) W (hWsupport.trans (trainRegion_mono subset_union_left))).symm
  have hVVpos (p : E × E) (hp : p ∈ K) :
      ∀ v ∈ V, ∀ u ∈ V, lpCross p.1 p.2 v u = 0 := by
    rintro v (⟨f,hf,hI,rfl⟩ | ⟨n,rfl⟩) u (⟨g,hg,hJ,rfl⟩ | ⟨m,rfl⟩)
    · rw [lpCross_toLp p.1 p.2 hf hg]
      exact shiftedRegion_cross_zero G (hKx p hp) hI.1 hJ.1
    · rw [lpCross_toLp p.1 p.2 hf (hP m)]
      exact (hPF m p.1 p.2 (hKx p hp) f (hI.1.trans (trainRegion_mono subset_union_right))).2
    · rw [lpCross_toLp p.1 p.2 (hP n) hg]
      exact (hPF n p.1 p.2 (hKx p hp) g (hJ.1.trans (trainRegion_mono subset_union_right))).1
    · rw [lpCross_toLp p.1 p.2 (hP n) (hP m)]
      exact hPP n m p.1 p.2 (hKx p hp)
  have hWWpos (p : E × E) (hp : p ∈ K) : lpCross p.1 p.2 Wl Wl = 0 := by
    rw [lpCross_toLp p.1 p.2 hwLp hwLp]
    exact cross_reference_self G w (hKx p hp)
  have hstar (p : E × E) (u v : Lp ℂ 2 (volume : Measure E)) :
      lpCross (-p.1) (-p.2) u v = star (lpCross p.1 p.2 v u) :=
    crossAmbiguity_neg_neg (Lp.memLp u) (Lp.memLp v) p.1 p.2
  have hstar' (p : E × E) (u v : Lp ℂ 2 (volume : Measure E)) :
      lpCross p.1 p.2 u v = star (lpCross (-p).1 (-p).2 v u) := by
    have H := hstar (-p) u v
    rw [show -(-p).1 = p.1 from _root_.neg_neg _,
      show -(-p).2 = p.2 from _root_.neg_neg _] at H
    exact H
  have hreflect (p : E × E) (h : p ∈ Ω) : p ∈ K ∨ -p ∈ K := by
    rcases h with h | ⟨q,hq,rfl⟩
    · exact Or.inl (subset_closure h)
    · exact Or.inr (by simpa [nH] using (subset_closure hq : q ∈ K))
  have hWtest (p : E × E) (hpx : p.1 ∈ band s ρ) (hp : p ∉ K) :
      ∃ v ∈ V, lpCross p.1 p.2 (Wl+v) (Wl+v) ≠ 0 := by
    obtain ⟨f,hf,hsupp,hkill,halive⟩ := exists_inner_packet G w hw gap hK hKx hKω hpx hp
    refine ⟨hf.toLp f, Or.inl ⟨f,hf,⟨hsupp,hkill⟩,rfl⟩, ?_⟩
    simp only [lpCross_add_left,lpCross_add_right,Wl,lpCross_toLp]
    have h₁ := cross_reference_self (ω := p.2) G w hpx
    have h₂ := referenceRegion_cross_zero (ω := p.2) G hpx hWsupport hsupp
    have h₃ := shiftedRegion_cross_zero (ω := p.2) G hpx hsupp hsupp
    change crossAmbiguity W W p.1 p.2 = 0 at h₁
    simpa only [h₁,h₂,h₃,add_zero,zero_add] using halive
  refine realize_from_directions hΩ Wl V (fun x ω ↦ continuous_ambiguity_eval x ω)
    ?_ ?_ ?_ z hzdense ?_
  · intro p hp
    rcases hreflect p hp with h | h
    · exact hWWpos p h
    · rw [hstar' p Wl Wl, hWWpos (-p) h, star_zero]
  · intro p hp v hv
    rcases hreflect p hp with h | h
    · exact hWVpos p h v hv
    · constructor
      · rw [hstar' p Wl v, (hWVpos (-p) h v hv).2, star_zero]
      · rw [hstar' p v Wl, (hWVpos (-p) h v hv).1, star_zero]
  · intro p hp v hv u hu
    rcases hreflect p hp with h | h
    · exact hVVpos p h v hv u hu
    · rw [hstar' p v u, hVVpos (-p) h u hu v hv, star_zero]
  · intro n
    by_cases h : (z n).1 ∈ band s ρ
    · have hn : z n ∉ K := fun hKz ↦ hz n (by rw [hclosure]; exact Or.inl hKz)
      obtain ⟨v,hv,hnz⟩ := hWtest (z n) h hn
      exact ⟨v,Submodule.subset_span hv,hnz⟩
    by_cases h' : -(z n).1 ∈ band s ρ
    · have hn : -(z n) ∉ K := by
        intro hk
        apply hz n
        rw [hclosure]
        exact Or.inr ⟨-(z n),hk,by change -(-(z n)) = z n; exact _root_.neg_neg _⟩
      obtain ⟨v,hv,hnz⟩ := hWtest (-(z n)) h' hn
      refine ⟨v,Submodule.subset_span hv, ?_⟩
      rw [hstar' (z n) (Wl+v) (Wl+v)]
      exact fun hzero ↦ hnz (star_eq_zero.mp hzero)
    · have hsame : outer n = z n := if_neg (not_or.mpr ⟨h,h'⟩)
      have hnon : lpCross (z n).1 (z n).2 (Pℓ n) (Pℓ n) ≠ 0 := by
        rw [lpCross_toLp (z n).1 (z n).2 (hP n) (hP n), ← hsame]
        exact hPne n
      obtain ⟨t,ht⟩ := exists_add_direction_ne_zero (z n).1 (z n).2 Wl (Pℓ n) hnon
      exact ⟨t • Pℓ n, (Submodule.span ℝ V).smul_mem _ (Submodule.subset_span (Or.inr ⟨n,rfl⟩)), ht⟩

end AmbiguityHoles.Local
