import IntegrationSection6.FiniteGammaProductHoms
import IntegrationSection6.FiniteGammaCoproductGluing
import IntegrationSection6.PackedProductEquivalence
import IntegrationSection6.ProductMapCoordinates
import IntegrationSection6.ProductVolumeTransport
import Mathlib.Logic.Equiv.Prod

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

def gammaProductDistribInl (U V : GammaObjectAt B S k) (R : GammaObjectAt B S l) :
    gammaProductAt U R ⟶ gammaProductAt (gammaCoprodAt U V) R :=
  gammaProductHomAt (gammaCoprodInlAt U V) (𝟙 R)

def gammaProductDistribInr (U V : GammaObjectAt B S k) (R : GammaObjectAt B S l) :
    gammaProductAt V R ⟶ gammaProductAt (gammaCoprodAt U V) R :=
  gammaProductHomAt (gammaCoprodInrAt U V) (𝟙 R)

theorem gammaProductDistrib_sum_bijective (U V : GammaObjectAt B S k) (R : GammaObjectAt B S l) :
    Function.Bijective (Sum.elim (homAtMap (gammaProductDistribInl U V R).hom)
      (homAtMap (gammaProductDistribInr U V R).hom)) := by
  let EU := @packedProductEquiv M N S _ _ (rvObjectDomain U.object.obj) (rvObjectDomain R.object.obj)
  let EV := @packedProductEquiv M N S _ _ (rvObjectDomain V.object.obj) (rvObjectDomain R.object.obj)
  let ET := @packedProductEquiv M N S _ _ (rvObjectDomain (gammaCoprodAt U V).object.obj) (rvObjectDomain R.object.obj)
  let EC := Equiv.ofBijective (coprodSumMap U V) (coprodSumMap_bijective U V)
  let E := ((Equiv.sumCongr EU.symm EV.symm).trans (Equiv.sumProdDistrib _ _ _).symm).trans
    ((Equiv.prodCongr EC (Equiv.refl _)).trans ET)
  have he : (fun z => E z) = Sum.elim (homAtMap (gammaProductDistribInl U V R).hom)
      (homAtMap (gammaProductDistribInr U V R).hom) := by
    funext z
    cases z with
    | inl x =>
      obtain ⟨u,r,rfl⟩ := @exists_rvPackPair M N S _ _ (rvObjectDomain U.object.obj) (rvObjectDomain R.object.obj) x
      have hx : EU.symm (@rvPackPair M N S _ _ (rvObjectDomain U.object.obj) (rvObjectDomain R.object.obj) u r) = (u,r) := EU.symm_apply_apply (u,r)
      change ET (EC (Sum.inl (EU.symm _).1),(EU.symm _).2) = _
      rw [hx]
      apply Subtype.ext
      exact (@rvProductMap_pair_labels M N S k l U.object.obj (gammaCoprodAt U V).object.obj R.object.obj R.object.obj
        (@rvCoprodLeftMap M N hN S k U.object.obj V.object.obj)
        (@SpecialTransformations.DefinableGeometry.Map.id LRV M N _ S (rvObjectDomain R.object.obj)) u r).symm
    | inr x =>
      obtain ⟨v,r,rfl⟩ := @exists_rvPackPair M N S _ _ (rvObjectDomain V.object.obj) (rvObjectDomain R.object.obj) x
      have hx : EV.symm (@rvPackPair M N S _ _ (rvObjectDomain V.object.obj) (rvObjectDomain R.object.obj) v r) = (v,r) := EV.symm_apply_apply (v,r)
      change ET (EC (Sum.inr (EV.symm _).1),(EV.symm _).2) = _
      rw [hx]
      apply Subtype.ext
      exact (@rvProductMap_pair_labels M N S k l V.object.obj (gammaCoprodAt U V).object.obj R.object.obj R.object.obj
        (@rvCoprodRightMap M N hN S k U.object.obj V.object.obj)
        (@SpecialTransformations.DefinableGeometry.Map.id LRV M N _ S (rvObjectDomain R.object.obj)) v r).symm
  rw [← he]
  exact E.bijective

def gammaProductLeftDistribIsoAt (U V : GammaObjectAt B S k) (R : GammaObjectAt B S l) :
    GammaIsoAt (gammaProductAt (gammaCoprodAt U V) R) (gammaCoprodAt (gammaProductAt U R) (gammaProductAt V R)) := by
  apply GammaIsoAt.symm
  apply gammaCoprodIsoOfSum (gammaProductDistribInl U V R) (gammaProductDistribInr U V R)
    (gammaProductDistrib_sum_bijective U V R)
  · intro x
    apply congrArg (@rvWeight M N (k+l))
    exact (@rvProductMap_volume_of_volume M N S k l U.object.obj (gammaCoprodAt U V).object.obj R.object.obj R.object.obj
      (@rvCoprodLeftMap M N hN S k U.object.obj V.object.obj)
      (@SpecialTransformations.DefinableGeometry.Map.id LRV M N _ S (rvObjectDomain R.object.obj))
      (@rvCoprod_value_left M N hN S k U.object.obj V.object.obj) (fun _ => rfl) x).symm
  · intro x
    apply congrArg (@rvWeight M N (k+l))
    exact (@rvProductMap_volume_of_volume M N S k l V.object.obj (gammaCoprodAt U V).object.obj R.object.obj R.object.obj
      (@rvCoprodRightMap M N hN S k U.object.obj V.object.obj)
      (@SpecialTransformations.DefinableGeometry.Map.id LRV M N _ S (rvObjectDomain R.object.obj))
      (@rvCoprod_value_right M N hN S k U.object.obj V.object.obj) (fun _ => rfl) x).symm

end IntegrationInACVF.Section6.FiniteRV
