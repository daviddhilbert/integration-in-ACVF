import IntegrationSection6.FiniteGammaProductAdmissibility
import IntegrationSection6.FiniteGammaElementaryAt
import IntegrationSection6.FiniteGammaFormulaIsos
import IntegrationSection6.ElementaryProductCoordinates

/-! The elementary-product comparison is a genuine finite Gamma RV
isomorphism with an explicit global coordinate permutation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k l : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaElementaryProductIsoAt {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (U : GammaObjectAt B S k) (V : GammaObjectAt B S l) (i : Fin k)
    (h : GammaAdmissible U.toGamma.toGammaRVObject i) :
    GammaIsoAt
      (gammaElementaryAt hκ hs h00 hsmall (gammaProductAt U V) (Fin.castAdd l i) (gammaAdmissible_product h V))
      (gammaProductAt (gammaElementaryAt hκ hs h00 hsmall U i h) V) := by
  let a := rvObjectArity U.object.obj
  let b := rvObjectArity V.object.obj
  let G := @selectRVTuple M N B.real ((a+b)+1) ((a+1)+b) (elementaryProductIndex a b)
    (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N ((a+b)+1)) B.real)
  exact GammaIsoAt.ofAmbientFormula
    (@elementaryProductIso M N hN S k l U.object.obj V.object.obj i) G
    (fun x => @elementaryProductMap_labels M N hN S k l U.object.obj V.object.obj i x)

end IntegrationInACVF.Section6.FiniteRV
