import IntegrationSection6.GammaSchemaRowValues
import IntegrationSection6.GammaAdmissibilitySchemata

/-! The tuple volume-image formula is exactly the image of the actual
row volume value at every valid row. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

theorem GammaFiniteRVSchema.rowValue_image_iff (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (hz : F.valid z) (y : Fin k → RV (M := M)) :
    (∃ x ∈ F.rowDomain z, F.rowValue z x = y) ↔
      Fin.append z (fun j => (y j).val) ∈ tupleVolumeImage F.volume := by
  rw [tupleVolumeImage_append_iff]
  constructor
  · rintro ⟨x,hx,hy⟩
    exact ⟨fun j => (x j).val,(F.rowValue_graph z hz x hx y).mpr hy⟩
  · rintro ⟨x,hx⟩
    have hxs (j : Fin a) : iRV (x j) := by
      simpa only [Fin.append_left,Fin.append_right,sortEval,iRV] using
        F.volume_definable.proper _ hx (Fin.castAdd k (Fin.natAdd p j))
    let xt : Fin a → RV (M := M) := fun j => ⟨x j,hxs j⟩
    have hD : xt ∈ F.rowDomain z := hz.2.2.1 x _ hx
    exact ⟨xt,hD,(F.rowValue_graph z hz xt hD y).mp hx⟩

theorem GammaFiniteAdmissibilitySchema.rowValue_nonzero (F : GammaFiniteAdmissibilitySchema B p a k sp)
    (z : Fin p → M) (hz : F.valid z) (x : Fin a → RV (M := M)) (hx : x ∈ F.object.rowDomain z) :
    (F.object.rowValue z x F.coordinate).val ≠ iRVZero :=
  hz.2.1 _ ((F.object.rowValue_image_iff z hz.1 _).mp ⟨x,hx,rfl⟩)

theorem GammaFiniteAdmissibilitySchema.rowValue_finite_slices (F : GammaFiniteAdmissibilitySchema B p a k sp)
    (z : Fin p → M) (hz : F.valid z) (t : Fin k → RV (M := M)) :
    {r : Fin k → RV (M := M) | (∃ x ∈ F.object.rowDomain z, F.object.rowValue z x = r) ∧
      ∀ j, j ≠ F.coordinate → r j = t j}.Finite := by
  have ht : ∀ j, sortEval SortTag.rv (t j).val := fun j => (t j).property
  have hf := (hz.2.2 (fun j => (t j).val) ht).1
  apply hf.of_injOn (f := fun r : Fin k → RV (M := M) => fun j => (r j).val)
  · rintro r ⟨hr,he⟩
    exact ⟨(F.object.rowValue_image_iff z hz.1 r).mp hr,fun j hj => congrArg Subtype.val (he j hj)⟩
  · intro r hr r' hr' he
    funext j
    exact Subtype.ext (congrFun he j)

end IntegrationInACVF.Section6
