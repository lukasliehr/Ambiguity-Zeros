module

public import LeanCode.Local.FourierPeriodization
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform BigOperators

namespace AmbiguityHoles

theorem summable_weighted_schwartz_lattice {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] (f : SchwartzMap E ℂ) (k : ℕ) :
    Summable (fun z : L ↦ (1 + ‖z‖) ^ k * ‖f z‖) := by
  let m := Module.finrank ℤ L + 1
  obtain ⟨C, hC, hdec⟩ := f.decay (k + m) 0
  have hsum := (ZLattice.summable_norm_rpow L (-(m : ℝ)) (by dsimp [m]; push_cast; linarith)).mul_left ((2 : ℝ) ^ k * C)
  refine hsum.of_norm_bounded_eventually ?_
  have hfinite : {z : L | ‖z‖ < 1}.Finite := by
    have hclosed : IsClosed (X := E) L :=
      @AddSubgroup.isClosed_of_discrete _ _ _ _ _ L.toAddSubgroup
        (inferInstanceAs (DiscreteTopology L))
    apply Set.Finite.subset
      ((Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
        (Metric.isBounded_closedBall (x := (0 : E)) (r := 1)) hclosed).preimage_embedding
        (.subtype _))
    intro z hz
    exact ⟨by simpa using hz.le, z.property⟩
  filter_upwards [hfinite.compl_mem_cofinite] with z hz
  have hz' : 1 ≤ ‖z‖ := le_of_not_gt hz
  have hpos : 0 < ‖z‖ := by linarith
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg hpos.le, Real.rpow_natCast,
    ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc
    (1 + ‖z‖) ^ k * ‖f z‖ * ‖z‖ ^ m
        ≤ (2 * ‖z‖) ^ k * ‖f z‖ * ‖z‖ ^ m := by gcongr; linarith
    _ = 2 ^ k * (‖z‖ ^ (k + m) * ‖f z‖) := by rw [mul_pow, pow_add]; ring
    _ ≤ 2 ^ k * C := by
      gcongr
      simpa using hdec (z : E)

end AmbiguityHoles

namespace AmbiguityHoles.Local

private theorem mFourier_neg_eq_character {d : ℕ} (n : Lattice d) (x : Coordinates d) :
    UnitAddTorus.mFourier (-n) (torusPoint x) = character (latticePoint n) x := by
  rw [character, ← Finset.sum_neg_distrib]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, torusPoint,
    Real.fourierChar_apply, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [fourier_coe_apply (T := 1)]
  simp only [Pi.neg_apply, Int.cast_neg, Complex.ofReal_one, div_one, latticePoint,
    Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_intCast]
  congr 1
  push_cast
  ring

private theorem rapid_schwartz_samples {d : ℕ} (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) :
    RapidCoefficients latticePoint (fun n ↦ f (WithLp.toLp 2 (latticePoint (-n)))) := by
  let E := EuclideanSpace ℝ (Fin d)
  let b : Module.Basis (Fin d) ℝ E := PiLp.basisFun 2 ℝ (Fin d)
  let L : Submodule ℤ E := Submodule.span ℤ (range b)
  letI : DiscreteTopology L := inferInstanceAs (DiscreteTopology (Submodule.span ℤ (range b)))
  let j (n : Lattice d) : L :=
    ⟨WithLp.toLp 2 (latticePoint (-n)),
      (b.mem_span_iff_repr_mem ℤ _).2 (fun i ↦ ⟨-n i, rfl⟩)⟩
  have hj : Function.Injective j := by
    intro n m h
    funext i
    have hi := congrArg (fun v : L ↦ (v.1 : E) i) h
    have hi' : (-n i : ℤ) = -m i := Int.cast_injective (α := ℝ) hi
    exact neg_injective hi'
  intro k
  have hsum := (summable_weighted_schwartz_lattice L f k).comp_injective hj
  refine hsum.of_nonneg_of_le (fun n ↦ by positivity) ?_
  intro n
  have hn : ‖latticePoint n‖ ≤ ‖(j n : E)‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro i
    simpa [j, latticePoint] using PiLp.norm_apply_le (j n : E) i
  change ‖f (j n : E)‖ * (1 + ‖latticePoint n‖) ^ k ≤
    (1 + ‖(j n : E)‖) ^ k * ‖f (j n : E)‖
  rw [mul_comm ‖f (j n : E)‖]
  gcongr

/-- A smooth compactly supported function inside one cell gives a periodic function
whose Fourier coefficients have summable moments of every order. -/
theorem exists_rapid_periodic_expansion {d : ℕ} (f : Coordinates d → ℂ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (hc : HasCompactSupport f) {a : Coordinates d}
    (hsupp : tsupport f ⊆ openCell a) (g : C(UnitAddTorus (Fin d), ℂ))
    (hg : ∀ x ∈ rightCell a, g (torusPoint x) = f x) :
    ∃ c : Lattice d → ℂ, RapidCoefficients latticePoint c ∧
      ∀ ω, g (torusPoint ω) = series latticePoint c ω := by
  let E := EuclideanSpace ℝ (Fin d)
  let e : E ≃L[ℝ] Coordinates d := PiLp.continuousLinearEquiv 2 ℝ _
  let F : SchwartzMap E ℂ :=
    (hc.comp_homeomorph e.toHomeomorph).toSchwartzMap (hf.comp e.contDiff)
  have hcoeff (n : Lattice d) :
      UnitAddTorus.mFourierCoeff g n = (𝓕 F : SchwartzMap E ℂ)
        (WithLp.toLp 2 (latticePoint n)) := by
    rw [UnitAddTorus.mFourierCoeff_eq_integral (a := a)]
    change (∫ x in rightCell a, UnitAddTorus.mFourier (-n) (torusPoint x) •
      g (torusPoint x)) = _
    simp_rw [mFourier_neg_eq_character]
    have hcell : MeasurableSet (rightCell a) :=
      MeasurableSet.univ_pi' fun _ ↦ measurableSet_Ioc
    rw [setIntegral_congr_fun (g := fun x ↦ character (latticePoint n) x • f x)
      hcell (fun x hx ↦ by rw [hg x hx])]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ ?_)]
    · have hF : ((𝓕 F : SchwartzMap E ℂ) : E → ℂ) = 𝓕 (F : E → ℂ) :=
        SchwartzMap.fourier_coe _
      rw [congrFun hF, Real.fourier_eq]
      let m := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
      have hm := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)
      rw [← hm.integral_comp m.measurableEmbedding]
      apply integral_congr_ae
      filter_upwards with x
      change character (latticePoint n) (m x) • f (m x) =
        Real.fourierChar (-(inner ℝ x (WithLp.toLp 2 (latticePoint n) : E))) • f (m x)
      rfl
    · have hxf : f x = 0 := by
        apply Function.notMem_support.mp
        exact fun h ↦ hx (openCell_subset_rightCell a (hsupp (subset_tsupport f h)))
      rw [hxf, smul_zero]
  let c : Lattice d → ℂ := fun n ↦ UnitAddTorus.mFourierCoeff g (-n)
  have hrapid : RapidCoefficients latticePoint c := by
    simpa only [c, hcoeff] using rapid_schwartz_samples (𝓕 F)
  refine ⟨c, hrapid, fun ω ↦ ?_⟩
  have hs : Summable (UnitAddTorus.mFourierCoeff g) := by
    apply (Equiv.neg (Lattice d)).summable_iff.mp
    exact hrapid.summable_norm.of_norm
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hs (torusPoint ω)
  have hneg := (Equiv.neg (Lattice d)).hasSum_iff.mpr h
  have hser : HasSum (fun n ↦ c n * character (latticePoint n) ω) (g (torusPoint ω)) := by
    simpa only [Function.comp_def, Equiv.neg_apply, c, mFourier_neg_eq_character,
      smul_eq_mul] using hneg
  exact hser.tsum_eq.symm

end AmbiguityHoles.Local
