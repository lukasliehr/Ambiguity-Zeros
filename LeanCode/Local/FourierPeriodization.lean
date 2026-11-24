module

public import LeanCode.Local.Fourier

@[expose] public section

open Set Filter Topology

namespace AmbiguityHoles.Local

noncomputable section

def torusPoint {d : ℕ} (x : Coordinates d) : UnitAddTorus (Fin d) :=
  fun i => (x i : UnitAddCircle)

def openCell {d : ℕ} (a : Coordinates d) : Set (Coordinates d) :=
  {x | ∀ i, x i ∈ Ioo (a i) (a i + 1)}

def rightCell {d : ℕ} (a : Coordinates d) : Set (Coordinates d) :=
  {x | ∀ i, x i ∈ Ioc (a i) (a i + 1)}

theorem isOpen_openCell {d : ℕ} (a : Coordinates d) : IsOpen (openCell a) := by
  have h := isOpen_iInter_of_finite
    (fun i : Fin d => isOpen_Ioo.preimage (continuous_apply i) :
      ∀ i : Fin d, IsOpen ((fun x : Coordinates d => x i) ⁻¹' Ioo (a i) (a i + 1)))
  have heq : openCell a =
      ⋂ i : Fin d, (fun x : Coordinates d => x i) ⁻¹' Ioo (a i) (a i + 1) := by
    ext x
    simp [openCell]
  rw [heq]
  exact h

theorem openCell_subset_rightCell {d : ℕ} (a : Coordinates d) :
    openCell a ⊆ rightCell a :=
  fun _ hx i => ⟨(hx i).1, (hx i).2.le⟩

theorem continuous_torusPoint {d : ℕ} : Continuous (torusPoint (d := d)) :=
  continuous_pi fun i => (AddCircle.continuous_mk' 1).comp (continuous_apply i)

theorem isOpenMap_torusPoint {d : ℕ} : IsOpenMap (torusPoint (d := d)) :=
  IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe)
    (Filter.Eventually.of_forall fun _ => QuotientAddGroup.mk_surjective)

def torusRepresentative {d : ℕ} (a : Coordinates d)
    (t : UnitAddTorus (Fin d)) : Coordinates d :=
  fun i => (AddCircle.equivIoc 1 (a i) (t i)).1

theorem torusRepresentative_mem {d : ℕ} (a : Coordinates d)
    (t : UnitAddTorus (Fin d)) : torusRepresentative a t ∈ rightCell a :=
  fun i => (AddCircle.equivIoc 1 (a i) (t i)).2

@[simp] theorem torusPoint_representative {d : ℕ} (a : Coordinates d)
    (t : UnitAddTorus (Fin d)) : torusPoint (torusRepresentative a t) = t := by
  funext i
  exact (AddCircle.equivIoc 1 (a i)).symm_apply_apply (t i)

theorem torusRepresentative_torusPoint {d : ℕ} {a x : Coordinates d}
    (hx : x ∈ rightCell a) : torusRepresentative a (torusPoint x) = x := by
  funext i
  exact congrArg Subtype.val ((AddCircle.equivIoc 1 (a i)).apply_symm_apply ⟨x i, hx i⟩)

theorem exists_torus_periodization {d : ℕ} {f : Coordinates d → ℂ}
    (hf : Continuous f) (hcompact : HasCompactSupport f) {a : Coordinates d}
    (hsupp : tsupport f ⊆ openCell a) :
    ∃ g : C(UnitAddTorus (Fin d), ℂ), ∀ x ∈ rightCell a, g (torusPoint x) = f x := by
  let g := fun t => f (torusRepresentative a t)
  have hagree (x : Coordinates d) (hx : x ∈ rightCell a) : g (torusPoint x) = f x := by
    simp only [g, torusRepresentative_torusPoint hx]
  let q : openCell a → UnitAddTorus (Fin d) := fun x => torusPoint x.1
  have hq : IsOpenEmbedding q := by
    apply IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact continuous_torusPoint.comp continuous_subtype_val
    · intro x y hxy
      apply Subtype.ext
      have h := congrArg (torusRepresentative a) hxy
      rwa [torusRepresentative_torusPoint (openCell_subset_rightCell a x.2),
        torusRepresentative_torusPoint (openCell_subset_rightCell a y.2)] at h
    · exact isOpenMap_torusPoint.comp (isOpen_openCell a).isOpenMap_subtype_val
  refine ⟨⟨g, continuous_iff_continuousAt.mpr ?_⟩, hagree⟩
  intro t
  by_cases ht : t ∈ torusPoint '' tsupport f
  · obtain ⟨x, hx, rfl⟩ := ht
    let z : openCell a := ⟨x, hsupp hx⟩
    change ContinuousAt g (q z)
    apply (hq.continuousAt_iff).mp
    have heq : g ∘ q = fun w : openCell a => f w.1 :=
      funext fun w => hagree w.1 (openCell_subset_rightCell a w.2)
    rw [heq]
    exact (hf.comp continuous_subtype_val).continuousAt
  · have hclosed : IsClosed (torusPoint '' tsupport f) :=
      (hcompact.image continuous_torusPoint).isClosed
    apply (continuousAt_const : ContinuousAt (fun _ : UnitAddTorus (Fin d) => (0 : ℂ)) t).congr
    filter_upwards [hclosed.isOpen_compl.mem_nhds ht] with u hu
    symm
    apply Function.notMem_support.mp
    intro h
    exact hu ⟨torusRepresentative a u, subset_tsupport f h, torusPoint_representative a u⟩

end
end AmbiguityHoles.Local
