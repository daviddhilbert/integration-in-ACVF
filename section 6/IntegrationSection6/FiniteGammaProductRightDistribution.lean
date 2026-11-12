import IntegrationSection6.FiniteGammaProductHoms
import IntegrationSection6.FiniteGammaCoproductGluing
import IntegrationSection6.PackedProductEquivalence
import IntegrationSection6.ProductMapCoordinates
import IntegrationSection6.ProductVolumeTransport
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum

/-! Distribution uses the actual tagged coproduct and cartesian product.
Both component maps have full original-Gamma graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k l : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaProductRightDistribInl (U V : GammaObjectAt B S k) (R : GammaObjectAt B S l) :
    gammaProductAt R U ⟶ gammaProductAt R (gammaCoprodAt U V) :=
  gammaProductHomAt (𝟙 R) (gammaCoprodInlAt U V)

def gammaProductRightDistribInr (U V : GammaObjectAt B S k) (R : GammaObjectAt B S l) :
    gammaProductAt R V ⟶ gammaProductAt R (gammaCoprodAt U V) :=
  gammaProductHomAt (𝟙 R) (gammaCoprodInrAt U V)

theorem gammaProductRightDistrib_sum_bijective (U V : GammaObjectAt B S k) (R : GammaObjectAt B S l) :
    Function.Bijective (Sum.elim (homAtMap (gammaProductRightDistribInl U V R).hom)
      (homAtMap (gammaProductRightDistribInr U V R).hom)) := by
  let EU := @packedProductEquiv M N S _ _ (rvObjectDomain R.object.obj) (rvObjectDomain U.object.obj)
  let EV := @packedProductEquiv M N S _ _ (rvObjectDomain R.object.obj) (rvObjectDomain V.object.obj)
  let ET := @packedProductEquiv M N S _ _ (rvObjectDomain R.object.obj) (rvObjectDomain (gammaCoprodAt U V).object.obj)
  let EC := Equiv.ofBijective (coprodSumMap U V) (coprodSumMap_bijective U V)
  let E := ((Equiv.sumCongr EU.symm EV.symm).trans (Equiv.prodSumDistrib _ _ _).symm).trans
    ((Equiv.prodCongr (Equiv.refl _) EC).trans ET)
  have he : (fun z => E z) = Sum.elim (homAtMap (gammaProductRightDistribInl U V R).hom)
      (homAtMap (gammaProductRightDistribInr U V R).hom) := by
    funext z
    cases z with
    | inl x =>
      obtain ⟨r,u,rfl⟩ := @exists_rvPackPair M N S _ _ (rvObjectDomain R.object.obj) (rvObjectDomain U.object.obj) x
      have hx : EU.symm (@rvPackPair M N S _ _ (rvObjectDomain R.object.obj) (rvObjectDomain U.object.obj) r u) = (r,u) := EU.symm_apply_apply (r,u)
      change ET ((EU.symm _).1,EC (Sum.inl (EU.symm _).2)) = _
      rw [hx]
      apply Subtype.ext
      exact (@rvProductMap_pair_labels M N S l k R.object.obj R.object.obj U.object.obj (gammaCoprodAt U V).object.obj
        (@SpecialTransformations.DefinableGeometry.Map.id LRV M N _ S (rvObjectDomain R.object.obj))
        (@rvCoprodLeftMap M N hN S k U.object.obj V.object.obj) r u).symm
    | inr x =>
      obtain ⟨r,v,rfl⟩ := @exists_rvPackPair M N S _ _ (rvObjectDomain R.object.obj) (rvObjectDomain V.object.obj) x
      have hx : EV.symm (@rvPackPair M N S _ _ (rvObjectDomain R.object.obj) (rvObjectDomain V.object.obj) r v) = (r,v) := EV.symm_apply_apply (r,v)
      change ET ((EV.symm _).1,EC (Sum.inr (EV.symm _).2)) = _
      rw [hx]
      apply Subtype.ext
      exact (@rvProductMap_pair_labels M N S l k R.object.obj R.object.obj V.object.obj (gammaCoprodAt U V).object.obj
        (@SpecialTransformations.DefinableGeometry.Map.id LRV M N _ S (rvObjectDomain R.object.obj))
        (@rvCoprodRightMap M N hN S k U.object.obj V.object.obj) r v).symm
  rw [← he]
  exact E.bijective

def gammaProductRightDistribIsoAt (U V : GammaObjectAt B S k) (R : GammaObjectAt B S l) :
    GammaIsoAt (gammaProductAt R (gammaCoprodAt U V)) (gammaCoprodAt (gammaProductAt R U) (gammaProductAt R V)) := by
  apply GammaIsoAt.symm
  apply gammaCoprodIsoOfSum (gammaProductRightDistribInl U V R) (gammaProductRightDistribInr U V R)
    (gammaProductRightDistrib_sum_bijective U V R)
  · intro x
    apply congrArg (@rvWeight M N (l+k))
    exact (@rvProductMap_volume_of_volume M N S l k R.object.obj R.object.obj U.object.obj (gammaCoprodAt U V).object.obj
      (@SpecialTransformations.DefinableGeometry.Map.id LRV M N _ S (rvObjectDomain R.object.obj))
      (@rvCoprodLeftMap M N hN S k U.object.obj V.object.obj)
      (fun _ => rfl) (@rvCoprod_value_left M N hN S k U.object.obj V.object.obj) x).symm
  · intro x
    apply congrArg (@rvWeight M N (l+k))
    exact (@rvProductMap_volume_of_volume M N S l k R.object.obj R.object.obj V.object.obj (gammaCoprodAt U V).object.obj
      (@SpecialTransformations.DefinableGeometry.Map.id LRV M N _ S (rvObjectDomain R.object.obj))
      (@rvCoprodRightMap M N hN S k U.object.obj V.object.obj)
      (fun _ => rfl) (@rvCoprod_value_right M N hN S k U.object.obj V.object.obj) x).symm

end IntegrationInACVF.Section6.FiniteRV
