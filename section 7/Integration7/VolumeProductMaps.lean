import Integration7.EssentialVolumeProducts
import Integration7.PolynomialTangentCoordinatePairs
import Section4.RVProductSymmetry

/-! The actual product map of two positive volume isomorphisms, using
the essential charts. Its volume equations are checked separately. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section7 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m : ℕ}
variable {U U' : PositiveRVVolumeObject (M := M) S n} {V V' : PositiveRVVolumeObject (M := M) S m}

def RVVolumeIso.productMap (f : RVVolumeIso U U') (g : RVVolumeIso V V') :
    Map (U.prod V).essential.obj.domain (U'.prod V').essential.obj.domain :=
  (productEssentialInverseChart U' V').comp
    ((Map.prodMap (finiteIsoMap f.iso) (finiteIsoMap g.iso)).comp (productEssentialChart U V))

theorem RVVolumeIso.productMap_bijective (f : RVVolumeIso U U') (g : RVVolumeIso V V') :
    Function.Bijective (f.productMap g) := by
  have hI : Function.Bijective (productEssentialInverseChart U' V') :=
    ⟨Function.LeftInverse.injective (productEssentialChart_inverse U' V'),
      Function.RightInverse.surjective (productEssentialInverseChart_chart U' V')⟩
  exact hI.comp ((Map.prodMap_bijective _ _ (finiteIsoMap_bijective f.iso)
    (finiteIsoMap_bijective g.iso)).comp (productEssentialChart_bijective U V))

theorem RVVolumeIso.productMap_chart (f : RVVolumeIso U U') (g : RVVolumeIso V V')
    (w : (U.prod V).essential.obj.domain) :
    productEssentialChart U' V' (f.productMap g w) =
      Map.prodMap (finiteIsoMap f.iso) (finiteIsoMap g.iso) (productEssentialChart U V w) :=
  productEssentialChart_inverse U' V' _

theorem RVVolumeIso.productMap_coordinates (f : RVVolumeIso U U') (g : RVVolumeIso V V')
    (w : (U.prod V).essential.obj.domain) :
    (U'.prod V').essential.obj.value (f.productMap g w) = Fin.append
      (U'.essential.obj.value (finiteIsoMap f.iso (Map.prodFst _ _ (productEssentialChart U V w))))
      (V'.essential.obj.value (finiteIsoMap g.iso (Map.prodSnd _ _ (productEssentialChart U V w)))) := by
  rw [productEssentialChart_coordinates, f.productMap_chart g]
  rfl

theorem RVVolumeIso.productMap_density (f : RVVolumeIso U U') (g : RVVolumeIso V V')
    (w : (U.prod V).essential.obj.domain) :
    (U'.prod V').essentialForm.value (f.productMap g w) =
      U'.essentialForm.value (finiteIsoMap f.iso (Map.prodFst _ _ (productEssentialChart U V w))) *
      V'.essentialForm.value (finiteIsoMap g.iso (Map.prodSnd _ _ (productEssentialChart U V w))) := by
  rw [productEssentialChart_density, f.productMap_chart g]
  rfl

def RVVolumeIso.productUnderlying (f : RVVolumeIso U U') (g : RVVolumeIso V V') :
    (U.prod V).essential ≅ (U'.prod V').essential :=
  finiteIsoOfNondegenerateBijection (f.productMap g) (f.productMap_bijective g)
    (U.prod V).essential_nonzero (U'.prod V').essential_nonzero

@[simp] theorem RVVolumeIso.productUnderlying_apply (f : RVVolumeIso U U') (g : RVVolumeIso V V')
    (w : (U.prod V).essential.obj.domain) :
    finiteIsoMap (f.productUnderlying g) w = f.productMap g w := rfl

theorem RVVolumeIso.productMap_volumeRatio (f : RVVolumeIso U U') (g : RVVolumeIso V V')
    (w : (U.prod V).essential.obj.domain) :
    volumeRatio (U.prod V) (U'.prod V') (f.productUnderlying g) w =
      volumeRatio U U' f.iso (Map.prodFst _ _ (productEssentialChart U V w)) *
      volumeRatio V V' g.iso (Map.prodSnd _ _ (productEssentialChart U V w)) := by
  unfold volumeRatio
  rw [productUnderlying_apply, productEssentialChart_density, productMap_density]
  exact (div_mul_div_comm _ _ _ _).symm

theorem RVVolumeIso.productCorrespondence_left (f : RVVolumeIso U U') (g : RVVolumeIso V V') :
    ∀ z ∈ (volumeCorrespondence (f.productMap g)).carrier,
      z ∘ coordinatePairIndex (Fin.castAdd (m + 1)) ∈ (volumeCorrespondence (finiteIsoMap f.iso)).carrier := by
  rintro z ⟨w, rfl⟩
  refine ⟨Map.prodFst _ _ (productEssentialChart U V w), ?_⟩
  rw [productTuple_comp_coordinatePairIndex, productEssentialChart_coordinates, productMap_coordinates]
  apply productTuple_ext <;> intro i <;>
    simp only [productTuple_left, productTuple_right, Function.comp_apply, Fin.append_left]

theorem RVVolumeIso.productCorrespondence_right (f : RVVolumeIso U U') (g : RVVolumeIso V V') :
    ∀ z ∈ (volumeCorrespondence (f.productMap g)).carrier,
      z ∘ coordinatePairIndex (Fin.natAdd (n + 1)) ∈ (volumeCorrespondence (finiteIsoMap g.iso)).carrier := by
  rintro z ⟨w, rfl⟩
  refine ⟨Map.prodSnd _ _ (productEssentialChart U V w), ?_⟩
  rw [productTuple_comp_coordinatePairIndex, productEssentialChart_coordinates, productMap_coordinates]
  apply productTuple_ext <;> intro i <;>
    simp only [productTuple_left, productTuple_right, Function.comp_apply, Fin.append_right]

end IntegrationInACVF.Section7
