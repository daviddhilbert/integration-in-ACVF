module

public import Integration7.VolumeClassCoordinatePermutations
public import Integration7.VolumeClassDegreeReindexing

@[expose] public section

/-! The explicit volume-coordinate and arithmetic degree
identifications preserve actual coproduct addition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k a b : ℕ}

def positiveVolumeClassPermutationAddEquiv
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (e : Equiv.Perm (Fin (k+1))) :
    PositiveVolumeBlowupClasses hc C k ≃+ PositiveVolumeBlowupClasses hc C k where
  toEquiv := positiveVolumeClassPermutationEquiv hc C e
  map_add' a b := Quotient.inductionOn₂ a b (fun U V => by
    let P := (U.coprod V).permuteVolume e
    let Q := (U.permuteVolume e).coprod (V.permuteVolume e)
    let f : Map P.underlying.obj.domain Q.underlying.obj.domain := Map.id _
    have hCoord : ∀ u, Q.underlying.obj.value (f u)=P.underlying.obj.value u := by
      intro u
      rcases volumeCoprod_cases U V u with ⟨r,rfl⟩ | ⟨r,rfl⟩
      · have hMap : f (rvCoprodLeftMap U.underlying.obj V.underlying.obj r)=
            rvCoprodLeftMap (U.permuteVolume e).underlying.obj (V.permuteVolume e).underlying.obj r := Subtype.ext rfl
        change Q.underlying.obj.value (f (rvCoprodLeftMap U.underlying.obj V.underlying.obj r))=
          (U.coprod V).underlying.obj.value (rvCoprodLeftMap U.underlying.obj V.underlying.obj r) ∘ e
        have hNew := rvCoprod_value_left (U.permuteVolume e).underlying.obj (V.permuteVolume e).underlying.obj r
        have hOld := rvCoprod_value_left U.underlying.obj V.underlying.obj r
        exact (congrArg Q.underlying.obj.value hMap).trans
          (hNew.trans (congrArg (fun t => t ∘ e) hOld.symm))
      · have hMap : f (rvCoprodRightMap U.underlying.obj V.underlying.obj r)=
            rvCoprodRightMap (U.permuteVolume e).underlying.obj (V.permuteVolume e).underlying.obj r := Subtype.ext rfl
        change Q.underlying.obj.value (f (rvCoprodRightMap U.underlying.obj V.underlying.obj r))=
          (U.coprod V).underlying.obj.value (rvCoprodRightMap U.underlying.obj V.underlying.obj r) ∘ e
        have hNew := rvCoprod_value_right (U.permuteVolume e).underlying.obj (V.permuteVolume e).underlying.obj r
        have hOld := rvCoprod_value_right U.underlying.obj V.underlying.obj r
        exact (congrArg Q.underlying.obj.value hMap).trans
          (hNew.trans (congrArg (fun t => t ∘ e) hOld.symm))
    exact positiveVolumeBlowupClass_iso hc C (RVVolumeIso.of_preserving_coordinates_full hc C
      (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f Function.bijective_id hCoord)) hCoord (fun _ => rfl)))

def positiveVolumeClassDegreeReindexAddEquiv
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (h : a=b) :
    PositiveVolumeBlowupClasses hc C b ≃+ PositiveVolumeBlowupClasses hc C a where
  toEquiv := positiveVolumeClassDegreeReindexEquiv hc C h
  map_add' x y := by
    cases h
    have hSum := eq_of_heq (positive_volume_class_reindex_degree_heq hc C rfl (x+y))
    have hx := eq_of_heq (positive_volume_class_reindex_degree_heq hc C rfl x)
    have hy := eq_of_heq (positive_volume_class_reindex_degree_heq hc C rfl y)
    exact hSum.trans (congrArg₂ (fun u v => u+v) hx.symm hy.symm)

end IntegrationInACVF.Section7
