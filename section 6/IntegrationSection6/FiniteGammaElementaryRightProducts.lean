import IntegrationSection6.FiniteGammaLeftProductAdmissibility
import IntegrationSection6.FiniteGammaElementaryAt
import IntegrationSection6.FiniteGammaFormulaIsos
import IntegrationSection6.ElementaryRightProductCoordinates

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

def gammaElementaryRightProductIsoAt {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (R : GammaObjectAt B S l) (U : GammaObjectAt B S k) (i : Fin k)
    (h : GammaAdmissible U.toGamma.toGammaRVObject i) :
    GammaIsoAt
      (gammaElementaryAt hκ hs h00 hsmall (gammaProductAt R U) (Fin.natAdd l i) (gammaAdmissible_product_left h R))
      (gammaProductAt R (gammaElementaryAt hκ hs h00 hsmall U i h)) := by
  let a := rvObjectArity R.object.obj
  let b := rvObjectArity U.object.obj
  let G := @selectRVTuple M N B.real ((a+b)+1) (a+(b+1)) (elementaryRightProductIndex a b)
    (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N ((a+b)+1)) B.real)
  exact GammaIsoAt.ofAmbientFormula
    (@elementaryRightProductIso M N hN S k l R.object.obj U.object.obj i) G
    (fun x => @elementaryRightProductMap_labels M N hN S k l R.object.obj U.object.obj i x)

end IntegrationInACVF.Section6.FiniteRV
