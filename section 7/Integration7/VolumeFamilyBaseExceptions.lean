import Integration7.AERVVolumeFunctions
import Integration7.SelectedFamilyCofullLifts
import Section4.RVIsoTools

/-! Removing a genuine definable exceptional base set leaves the same
almost-everywhere RV-volume function and the same full VF volume class. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k : ℕ}

def SelectedVFVolumeFamily.outsideBase (F : SelectedVFVolumeFamily C n a k)
    (E : DefSet (rawVFSpace (M := M) n) (C.base : Set M)) : SelectedVFVolumeFamily C n a k :=
  F.restrict (F.domain.sdiff (definableMapPreimage
    (Map.fst (rawVFSpace (M := M) n) (rawRVSpace a) (C.base : Set M) F.domain) E)) Set.sdiff_subset

def selectedFamilyOutsideBaseRowIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (F : SelectedVFVolumeFamily C n a k)
    (E : DefSet (rawVFSpace (M := M) n) (C.base : Set M))
    (x : (rawVFSpace (M := M) n).Carrier) (hx : x ∉ E.carrier) :
    RVVolumeIso ((F.outsideBase E).rowInContext x) (F.rowInContext x) := by
  let U := (F.outsideBase E).rowInContext x
  let V := F.rowInContext x
  let P := Map.fst (rawVFSpace (M := M) n) (rawRVSpace a) (C.base : Set M) F.domain
  let f : Map U.underlying.obj.domain V.underlying.obj.domain := Map.inclusion (fun r hr => hr.1)
  have hf : Function.Bijective f := by
    constructor
    · intro p q he
      have h := congrArg Subtype.val he
      exact Subtype.ext h
    · intro p
      refine ⟨⟨p.val,?_⟩,rfl⟩
      change (x,p.val) ∈ F.domain.carrier ∧ (x,p.val) ∉ (definableMapPreimage P E).carrier
      refine ⟨p.property,?_⟩
      intro hp
      exact hx ((mem_definableMapPreimage P E ⟨(x,p.val),p.property⟩).mp hp)
  have hcoord : ∀ p, V.underlying.obj.value (f p) = U.underlying.obj.value p := fun _ => rfl
  let e := rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection
    (U := U.underlying.obj) (V := V.underlying.obj) f hf hcoord)
  exact RVVolumeIso.of_preserving_coordinates_full hc (vfParameterVolumeContext C x) e hcoord (fun _ => rfl)

theorem selected_family_outside_base_difference_supported
    (F : SelectedVFVolumeFamily C n a k)
    (E : DefSet (rawVFSpace (M := M) n) (C.base : Set M))
    (p : F.domain.sdiff (F.outsideBase E).domain) : p.val.1 ∈ E.carrier := by
  let P := Map.fst (rawVFSpace (M := M) n) (rawRVSpace a) (C.base : Set M) F.domain
  by_contra hx
  apply p.property.2
  refine ⟨p.property.1,?_⟩
  intro hp
  exact hx ((mem_definableMapPreimage P E ⟨p.val,p.property.1⟩).mp hp)

theorem ae_volume_family_outside_base
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : SelectedVFVolumeFamily C (n+1) a k)
    (E : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (hE : vfDim (rawRVSpace (M := M) 1) E < n+1) :
    AERVVolumeFunctionEquivalent hc C ⟨a,F⟩ ⟨a,F.outsideBase E⟩ :=
  ⟨E,hE,fun x hx => (positiveVolumeBlowupClass_iso hc (vfParameterVolumeContext C x)
    (selectedFamilyOutsideBaseRowIso hc F E x hx)).symm⟩

theorem full_volume_lift_class_outside_base
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : SelectedVFVolumeFamily C n a k)
    (E : DefSet (rawVFSpace (M := M) n) (C.base : Set M))
    (hE : vfDim (rawRVSpace (M := M) 1) E < n) :
    positiveVFVolumeIsoClass hc C F.fullLift = positiveVFVolumeIsoClass hc C (F.outsideBase E).fullLift :=
  selected_family_full_lift_class_remove_small_base hc C F (F.outsideBase E).domain
    Set.sdiff_subset E hE (selected_family_outside_base_difference_supported F E)

end IntegrationInACVF.Section7
