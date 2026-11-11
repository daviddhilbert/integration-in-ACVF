import IntegrationSection3ACVF.TranslationSyntax
import IntegrationSection3ACVF.VFErrorSyntax
import IntegrationSection3ACVF.RVLeadingDifference

/-! Actual translated VF errors, their real-base partial graphs, and the
strict-value versus pair-value estimates used in RV linearity. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.TranslatedErrorGeometry

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def transformed (a c fe : M) (f : M → M) (x : M) : M :=
  VFErrorSyntax.fieldError c fe x (f (TranslationSyntax.input a x))

theorem transformed_vf (a c fe x : VFType (M := M)) {D : Set M} (f : M → M)
    (hfVF : ∀ z ∈ D, iVF (f z)) (hx : (a+x).val ∈ D) :
    let fx : VFType (M := M) := ⟨f (a+x).val,hfVF _ hx⟩
    transformed a.val c.val fe.val f x.val = (fx-fe-c*x).val := by
  unfold transformed
  rw [TranslationSyntax.input_vf a x]
  exact VFErrorSyntax.fieldError_vf c fe x ⟨f (a+x).val,hfVF _ hx⟩

theorem graph_definable (S : Set M) (a c fe : M)
    (ha : a ∈ S) (hc : c ∈ S) (hfe : fe ∈ S) (h0 : iVFZero ∈ S)
    {D : Set M} (f : M → M)
    (hf : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
      (IntegrationInACVF.Section3.ImaginaryBaseImages.graphOn D f)) :
    @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
      (IntegrationInACVF.Section3.ImaginaryBaseImages.graphOn (TranslationSyntax.domain D a)
        (transformed a c fe f)) := by
  exact RealGraphOperations.postcompose S (fun x => f (TranslationSyntax.input a x))
    (fun x y => VFErrorSyntax.fieldError c fe x y)
    (TranslationSyntax.graph_definable S a ha f hf)
    (VFErrorSyntax.fieldError_definable S c fe hc hfe h0)

theorem strict_value (c fe x fx : VFType (M := M))
    (hc : c ≠ 0) (hx : x ≠ 0)
    (hRV : CanonicalRV.encodedRv (fx-fe) = CanonicalRV.encodedRv (c*x)) :
    Values.vfValueHom c * Values.vfValueHom x <
      Values.vfValueHom (fx-fe-c*x) := by
  simpa only [map_mul] using RVErrorComparison.error_value_gt (fx-fe) (c*x)
    (mul_ne_zero hc hx) hRV

theorem pair_value (c fe x y fx fy : VFType (M := M))
    (hc : c ≠ 0) (hxy : y ≠ x)
    (hValue : Values.vfValueHom (fy-fx) = Values.vfValueHom (c*(y-x)))
    (hRV : CanonicalRV.encodedRv (fy-fx) ≠ CanonicalRV.encodedRv (c*(y-x))) :
    Values.vfValueHom ((fy-fe-c*y)-(fx-fe-c*x)) =
      Values.vfValueHom c * Values.vfValueHom (y-x) := by
  have he : (fy-fe-c*y)-(fx-fe-c*x) = (fy-fx)-c*(y-x) := by ring
  rw [he]
  simpa only [map_mul] using RVLeadingDifference.value_sub (fy-fx) (c*(y-x))
    (mul_ne_zero hc (sub_ne_zero.mpr hxy)) hValue hRV

end IntegrationInACVF.Section3ACVF.TranslatedErrorGeometry
