module

public import Integration7.SelectedFamilyRestrictions
public import Integration7.DefinableMapPreimages
public import Integration7.SelectedVolumeRowContexts
public import Integration7.VolumeRelabeling
public import Integration7.IndexedVolumeEmpty

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Restriction to a definable VF base set retains the actual row on
that set and has the empty volume row outside it. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k : ℕ}

def SelectedVFVolumeFamily.onBase (F : SelectedVFVolumeFamily C n a k)
    (X : DefSet (rawVFSpace (M := M) n) (C.base : Set M)) : SelectedVFVolumeFamily C n a k :=
  F.restrict (definableMapPreimage (Map.fst (rawVFSpace (M := M) n) (rawRVSpace a) (C.base : Set M) F.domain) X)
    (definableMapPreimage_subset _ _)

theorem selected_volume_family_on_base_mem (F : SelectedVFVolumeFamily C n a k)
    (X : DefSet (rawVFSpace (M := M) n) (C.base : Set M))
    (q : (rawMixedSpace (M := M) n a).Carrier) :
    q ∈ (F.onBase X).domain.carrier ↔ q ∈ F.domain.carrier ∧ q.1 ∈ X.carrier := by
  constructor
  · rintro ⟨p,hp,hX⟩
    exact ⟨hp ▸ p.property,congrArg Prod.fst hp ▸ hX⟩
  · rintro ⟨hq,hX⟩
    exact ⟨⟨q,hq⟩,rfl,hX⟩

theorem selected_volume_family_on_base_supported (F : SelectedVFVolumeFamily C n a k)
    (X : DefSet (rawVFSpace (M := M) n) (C.base : Set M)) :
    ∀ q : (F.onBase X).domain, q.val.1 ∈ X.carrier :=
  fun q => ((selected_volume_family_on_base_mem F X q.val).mp q.property).2

def selectedVolumeOnBaseRowIso (hc : CanonicalStructure.IsCanonical (M := M))
    (F : SelectedVFVolumeFamily C n a k) (X : DefSet (rawVFSpace (M := M) n) (C.base : Set M))
    (x : Fin n → VFType (M := M)) (hx : x ∈ X.carrier) :
    RVVolumeIso ((F.onBase X).rowInContext x) (F.rowInContext x) := by
  let U := (F.onBase X).rowInContext x
  let V := F.rowInContext x
  have hUV : U.underlying.obj.domain.carrier = V.underlying.obj.domain.carrier := by
    ext r
    change (x,r) ∈ (F.onBase X).domain.carrier ↔ (x,r) ∈ F.domain.carrier
    rw [selected_volume_family_on_base_mem]
    exact and_iff_left hx
  exact RVVolumeIso.of_preserving_coordinates_full hc (vfParameterVolumeContext C x)
    (rvFiniteIsoOfAmbient (rvIsoOfCarrierEq U.underlying.obj.domain V.underlying.obj.domain
      U.underlying.obj.volume V.underlying.obj.volume hUV (fun _ => rfl)))
    (fun _ => rfl) (fun _ => rfl)

theorem selected_volume_on_base_row_class_inside
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : SelectedVFVolumeFamily C n a k) (X : DefSet (rawVFSpace (M := M) n) (C.base : Set M))
    (x : Fin n → VFType (M := M)) (hx : x ∈ X.carrier) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((F.onBase X).rowInContext x) =
      positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) (F.rowInContext x) :=
  positiveVolumeBlowupClass_iso hc _ (selectedVolumeOnBaseRowIso hc F X x hx)

theorem selected_volume_on_base_row_class_outside
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : SelectedVFVolumeFamily C n a k) (X : DefSet (rawVFSpace (M := M) n) (C.base : Set M))
    (x : Fin n → VFType (M := M)) (hx : x ∉ X.carrier) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((F.onBase X).rowInContext x) = 0 := by
  apply positiveVolumeBlowupClass_iso hc (vfParameterVolumeContext C x)
  apply RVVolumeIso.of_empty hc (vfParameterVolumeContext C x) _ _ _ rfl
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro r hr
  exact hx (((selected_volume_family_on_base_mem F X (x,r)).mp hr).2)
end IntegrationInACVF.Section7
