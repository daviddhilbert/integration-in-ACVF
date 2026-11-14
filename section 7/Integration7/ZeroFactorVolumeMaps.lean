import Integration7.EssentialZeroProducts
import Integration7.RVJacobianRestriction
import Section4.ProductBijections

/-! Products of actual positive volume isomorphisms with ordinary
degree-zero RV isomorphisms. The latter carry no density or Jacobian premise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section7 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}
variable {U V : PositiveRVVolumeObject (M := M) S k} {Z T : RVFiniteObject (M := M) S 0}

def RVVolumeIso.zeroProductMap (f : RVVolumeIso U V) (g : Z ≅ T) :
    Map (U.prod_zero Z).essential.obj.domain (V.prod_zero T).essential.obj.domain :=
  (zeroProductEssentialInverseChart V T).comp
    ((Map.prodMap (finiteIsoMap f.iso) (finiteIsoMap g)).comp (zeroProductEssentialChart U Z))

theorem RVVolumeIso.zeroProductMap_bijective (f : RVVolumeIso U V) (g : Z ≅ T) :
    Function.Bijective (f.zeroProductMap g) := by
  have hI : Function.Bijective (zeroProductEssentialInverseChart V T) :=
    ⟨Function.LeftInverse.injective (zeroProductEssentialChart_inverse V T),
      Function.RightInverse.surjective (zeroProductEssentialInverseChart_chart V T)⟩
  exact hI.comp ((Map.prodMap_bijective _ _ (finiteIsoMap_bijective f.iso)
    (finiteIsoMap_bijective g)).comp (zeroProductEssentialChart_bijective U Z))

theorem RVVolumeIso.zeroProductMap_chart (f : RVVolumeIso U V) (g : Z ≅ T)
    (x : (U.prod_zero Z).essential.obj.domain) :
    zeroProductEssentialChart V T (f.zeroProductMap g x) =
      Map.prodMap (finiteIsoMap f.iso) (finiteIsoMap g) (zeroProductEssentialChart U Z x) :=
  zeroProductEssentialChart_inverse V T _

theorem RVVolumeIso.zeroProductMap_coordinates (f : RVVolumeIso U V) (g : Z ≅ T)
    (x : (U.prod_zero Z).essential.obj.domain) :
    (V.prod_zero T).essential.obj.value (f.zeroProductMap g x) =
      V.essential.obj.value (finiteIsoMap f.iso (Map.prodFst _ _ (zeroProductEssentialChart U Z x))) := by
  rw [zeroProductEssentialChart_coordinates,f.zeroProductMap_chart g]
  rfl

theorem RVVolumeIso.zeroProductMap_density (f : RVVolumeIso U V) (g : Z ≅ T)
    (x : (U.prod_zero Z).essential.obj.domain) :
    (V.prod_zero T).essentialForm.value (f.zeroProductMap g x) =
      V.essentialForm.value (finiteIsoMap f.iso (Map.prodFst _ _ (zeroProductEssentialChart U Z x))) := by
  rw [zeroProductEssentialChart_density,f.zeroProductMap_chart g]
  rfl

def RVVolumeIso.zeroProductUnderlying (f : RVVolumeIso U V) (g : Z ≅ T) :
    (U.prod_zero Z).essential ≅ (V.prod_zero T).essential :=
  finiteIsoOfNondegenerateBijection (f.zeroProductMap g) (f.zeroProductMap_bijective g)
    (U.prod_zero Z).essential_nonzero (V.prod_zero T).essential_nonzero

@[simp] theorem RVVolumeIso.zeroProductUnderlying_apply (f : RVVolumeIso U V) (g : Z ≅ T)
    (x : (U.prod_zero Z).essential.obj.domain) :
    finiteIsoMap (f.zeroProductUnderlying g) x = f.zeroProductMap g x := rfl

theorem RVVolumeIso.zeroProductMap_volumeRatio (f : RVVolumeIso U V) (g : Z ≅ T)
    (x : (U.prod_zero Z).essential.obj.domain) :
    volumeRatio (U.prod_zero Z) (V.prod_zero T) (f.zeroProductUnderlying g) x =
      volumeRatio U V f.iso (Map.prodFst _ _ (zeroProductEssentialChart U Z x)) := by
  unfold volumeRatio
  rw [f.zeroProductUnderlying_apply g,zeroProductEssentialChart_density,f.zeroProductMap_density g]

theorem RVVolumeIso.zeroProductCorrespondence_subset (f : RVVolumeIso U V) (g : Z ≅ T) :
    (volumeCorrespondence (f.zeroProductMap g)).carrier ⊆
      (volumeCorrespondence (finiteIsoMap f.iso)).carrier := by
  rintro z ⟨x,rfl⟩
  refine ⟨Map.prodFst _ _ (zeroProductEssentialChart U Z x),?_⟩
  symm
  change productTuple ((U.prod_zero Z).essential.obj.value x)
    ((V.prod_zero T).essential.obj.value (f.zeroProductMap g x)) = _
  rw [zeroProductEssentialChart_coordinates,f.zeroProductMap_coordinates g]

end IntegrationInACVF.Section7
