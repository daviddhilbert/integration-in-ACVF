import Integration7.DefinableVFVolumeFamilies
import Integration7.FixedVFLabelTags
import Integration7.VolumeFormGluing

/-! Definable tagged disjoint unions of volume families, with the VF
tuple fixed and the coordinate/density maps glued literally on each
summand. Finiteness is verified separately for the full family object. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b k : ℕ}

def volumeFamilyCoprodDomain (F : DefinableVFVolumeFamily C n a k) (G : DefinableVFVolumeFamily C n b k) :
    DefSet (rawMixedSpace (M := M) n (1+(a+b))) (C.base : Set M) :=
  (fixedVFLeftTagMap F.domain b).image.union (fixedVFRightTagMap G.domain a).image

def volumeFamilyCoprodVolumeMap (F : DefinableVFVolumeFamily C n a k) (G : DefinableVFVolumeFamily C n b k) :
    Map (volumeFamilyCoprodDomain F G) (DefSet.univ (rawRVSpace (M := M) (k+1)) (C.base : Set M)) :=
  (F.volume.comp (fixedVFUntagLeft F.domain b)).union (G.volume.comp (fixedVFUntagRight G.domain a))

def volumeFamilyCoprodForm (F : DefinableVFVolumeFamily C n a k) (G : DefinableVFVolumeFamily C n b k) :
    VolumeForm (volumeFamilyCoprodDomain F G) :=
  (F.form.pullback (fixedVFUntagLeft F.domain b)).union (G.form.pullback (fixedVFUntagRight G.domain a))

def volumeFamilyCoprodLeftMap (F : DefinableVFVolumeFamily C n a k) (G : DefinableVFVolumeFamily C n b k) :
    Map F.domain (volumeFamilyCoprodDomain F G) :=
  (Map.inclusion (show (fixedVFLeftTagMap F.domain b).image.carrier ⊆
    (volumeFamilyCoprodDomain F G).carrier from fun _ h => Or.inl h)).comp (fixedVFLeftTagMap F.domain b).toImage

def volumeFamilyCoprodRightMap (F : DefinableVFVolumeFamily C n a k) (G : DefinableVFVolumeFamily C n b k) :
    Map G.domain (volumeFamilyCoprodDomain F G) :=
  (Map.inclusion (show (fixedVFRightTagMap G.domain a).image.carrier ⊆
    (volumeFamilyCoprodDomain F G).carrier from fun _ h => Or.inr h)).comp (fixedVFRightTagMap G.domain a).toImage

theorem volume_family_coprod_volume_left (F : DefinableVFVolumeFamily C n a k) (G : DefinableVFVolumeFamily C n b k)
    (u : F.domain) : volumeFamilyCoprodVolumeMap F G (volumeFamilyCoprodLeftMap F G u) = F.volume u := by
  change ((F.volume.comp (fixedVFUntagLeft F.domain b)).union
    (G.volume.comp (fixedVFUntagRight G.domain a)))
      ⟨((fixedVFLeftTagMap F.domain b).toImage u).val,Or.inl ((fixedVFLeftTagMap F.domain b).toImage u).property⟩ = _
  rw [Map.union_on_left]
  exact congrArg F.volume (Map.inverse_apply _ _ u)

theorem volume_family_coprod_volume_right (F : DefinableVFVolumeFamily C n a k) (G : DefinableVFVolumeFamily C n b k)
    (u : G.domain) : volumeFamilyCoprodVolumeMap F G (volumeFamilyCoprodRightMap F G u) = G.volume u := by
  change ((F.volume.comp (fixedVFUntagLeft F.domain b)).union
    (G.volume.comp (fixedVFUntagRight G.domain a)))
      ⟨((fixedVFRightTagMap G.domain a).toImage u).val,Or.inr ((fixedVFRightTagMap G.domain a).toImage u).property⟩ = _
  rw [Map.union_on_right _ _ (fixed_vf_tagged_images_disjoint F.domain G.domain)]
  exact congrArg G.volume (Map.inverse_apply _ _ u)

theorem volume_family_coprod_density_left (F : DefinableVFVolumeFamily C n a k) (G : DefinableVFVolumeFamily C n b k)
    (u : F.domain) : (volumeFamilyCoprodForm F G).value (volumeFamilyCoprodLeftMap F G u) = F.form.value u := by
  change (((F.form.map.comp (fixedVFUntagLeft F.domain b)).union
    (G.form.map.comp (fixedVFUntagRight G.domain a)))
      ⟨((fixedVFLeftTagMap F.domain b).toImage u).val,Or.inl ((fixedVFLeftTagMap F.domain b).toImage u).property⟩).val 0 = _
  rw [Map.union_on_left]
  exact congrArg F.form.value (Map.inverse_apply _ _ u)

theorem volume_family_coprod_density_right (F : DefinableVFVolumeFamily C n a k) (G : DefinableVFVolumeFamily C n b k)
    (u : G.domain) : (volumeFamilyCoprodForm F G).value (volumeFamilyCoprodRightMap F G u) = G.form.value u := by
  change (((F.form.map.comp (fixedVFUntagLeft F.domain b)).union
    (G.form.map.comp (fixedVFUntagRight G.domain a)))
      ⟨((fixedVFRightTagMap G.domain a).toImage u).val,Or.inr ((fixedVFRightTagMap G.domain a).toImage u).property⟩).val 0 = _
  rw [Map.union_on_right _ _ (fixed_vf_tagged_images_disjoint F.domain G.domain)]
  exact congrArg G.form.value (Map.inverse_apply _ _ u)

end IntegrationInACVF.Section7
