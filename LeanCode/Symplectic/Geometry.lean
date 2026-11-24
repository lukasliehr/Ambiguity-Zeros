module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic.Abel

@[expose] public section

noncomputable section

namespace AmbiguityHoles.Symplectic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The frequency shear associated with a real symmetric chirp. -/
def shear (M : E →L[ℝ] E) : (E × E) ≃L[ℝ] (E × E) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun z ↦ (z.1, z.2 - M z.1)
      invFun := fun z ↦ (z.1, z.2 + M z.1)
      left_inv := by intro z; simp
      right_inv := by intro z; simp
      map_add' := by intro z w; ext <;> simp <;> abel
      map_smul' := by intro c z; ext <;> simp [smul_sub] }

@[simp] theorem shear_apply (M : E →L[ℝ] E) (z : E × E) :
    shear M z = (z.1, z.2 - M z.1) := rfl

/-- The quarter turn on phase space associated with the Fourier transform. -/
def quarterTurn : (E × E) ≃L[ℝ] (E × E) :=
  (ContinuousLinearEquiv.prodComm ℝ E E).trans
    ((ContinuousLinearEquiv.neg ℝ).prodCongr (ContinuousLinearEquiv.refl ℝ E))

@[simp] theorem quarterTurn_apply (z : E × E) : quarterTurn z = (-z.2, z.1) := rfl

theorem adjoint_inv_apply (B : E ≃L[ℝ] E) (y : E) :
    B.toContinuousLinearMap.adjoint (B.symm.toContinuousLinearMap.adjoint y) = y := by
  apply ext_inner_right ℝ
  intro x
  simp only [ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ y (B.symm (B x)) = inner ℝ y x
  rw [B.symm_apply_apply]

/-- The phase-space dilation associated with a change of signal coordinates. -/
def phaseDilation (B : E ≃L[ℝ] E) : (E × E) ≃L[ℝ] (E × E) :=
  B.prodCongr <|
    { toLinearEquiv :=
        { B.symm.toContinuousLinearMap.adjoint.toLinearMap with
          invFun := B.toContinuousLinearMap.adjoint
          left_inv := adjoint_inv_apply B
          right_inv := adjoint_inv_apply B.symm }
      continuous_toFun := B.symm.toContinuousLinearMap.adjoint.continuous
      continuous_invFun := B.toContinuousLinearMap.adjoint.continuous }

@[simp] theorem phaseDilation_apply (B : E ≃L[ℝ] E) (z : E × E) :
    phaseDilation B z = (B z.1, B.symm.toContinuousLinearMap.adjoint z.2) := rfl

/-- Scale the first nonzero vector to the norm of the second, then reflect
through the perpendicular bisector subspace. -/
theorem exists_dilation {x e : E} (hx : x ≠ 0) (he : e ≠ 0) :
    ∃ B : E ≃L[ℝ] E, B x = e := by
  let c : ℝ := ‖e‖ / ‖x‖
  have hc : 0 < c := div_pos (norm_pos_iff.mpr he) (norm_pos_iff.mpr hx)
  have hnorm : ‖c • x‖ = ‖e‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx)]
  let B₁ := (LinearEquiv.smulOfNeZero ℝ E c hc.ne').toContinuousLinearEquiv
  let B₂ := ((ℝ ∙ (c • x - e))ᗮ.reflection).toContinuousLinearEquiv
  exact ⟨B₁.trans B₂, Submodule.reflection_sub hnorm⟩

end AmbiguityHoles.Symplectic
