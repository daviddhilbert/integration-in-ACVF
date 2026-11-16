module

public import Integration7.SelectedTailLiftMaps
public import Integration7.MixedDomainVolumeProducts
public import Integration7.MixedJacobianRestriction
public import Integration7.GradedVolumeProducts

@[expose] public section

/-! Realizing selected RV coordinates by fixed VF tails preserves the
volume equation of an actual label-preserving mixed map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a d : ℕ}

theorem selected_tail_product_volume_value
    (A : DefSet (rawMixedSpace (M := M) n a) S) (ω : VolumeForm A)
    (ρ : Fin d → Fin a) (p : selectedRVVFTailLift A ρ) :
    (mixedDomainProductVolumeForm ω
      (VolumeForm.one (DefSet.univ (rawMixedSpace (M := M) d 0) S))).value
        (selectedTailProductInclusion A ρ p) =
      ω.value (selectedRVVFTailProjection A ρ p) := by
  change (ω.prod (VolumeForm.one _)).value
    (mixedUnpack A _ (selectedTailProductInclusion A ρ p)) = _
  rw [selected_tail_product_unpack]
  change ω.value (selectedRVVFTailProjection A ρ p) * 1 = _
  exact mul_one _

theorem preserves_vf_volume_selected_tail
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hd : 0 < d)
    {A B : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    (f : Map A B) (hLabels : ∀ p : A, (f p).val.2 = p.val.2)
    (ω : VolumeForm A) (π : VolumeForm B) (ρ : Fin d → Fin a)
    (hf : PreservesVFVolume ω π f) :
    PreservesVFVolume (ω.pullback (selectedRVVFTailProjection A ρ))
      (π.pullback (selectedRVVFTailProjection B ρ)) (selectedTailLiftMap f hLabels ρ) := by
  let R := DefSet.univ (rawMixedSpace (M := M) d 0) (C.base : Set M)
  let η := VolumeForm.one R
  have hId : PreservesVFVolume η η (Map.id R) := by
    apply (vfJacobianOne_of_preservesVF hc C hd (Map.id R) (fun _ => rfl)).mono
    intro p h
    refine ⟨1,h,?_⟩
    rw [RVOperations.rv_one,mul_one]
    rfl
  have hProd := preserves_vf_volume_mixed_product hc C ω η π η f (Map.id R) hf hId
  let g := selectedTailLiftMap f hLabels ρ
  let F := mixedDomainProductMap f (Map.id R)
  have hSub : (selectedRVVFTailLift A ρ).carrier ⊆ (mixedProductDomain A R).carrier := by
    intro p hp
    exact (selectedTailProductInclusion A ρ ⟨p,hp⟩).property
  have hMap (p : selectedRVVFTailLift A ρ) :
      F ⟨p.val,hSub p.property⟩ = selectedTailProductInclusion B ρ (g p) :=
    Subtype.ext rfl
  apply preservesVFVolume_of_restriction hc C (by omega) hSub F g
    (fun _ => rfl) (mixedDomainProductVolumeForm ω η) (mixedDomainProductVolumeForm π η)
    (ω.pullback (selectedRVVFTailProjection A ρ)) (π.pullback (selectedRVVFTailProjection B ρ))
    (fun p => selected_tail_product_volume_value A ω ρ p) ?_ hProd
  intro p
  rw [hMap]
  exact selected_tail_product_volume_value B π ρ (g p)

end IntegrationInACVF.Section7
