import IntegrationSection6.FiniteGammaProducts
import IntegrationSection6.FiniteGammaVolumeReindexing
import IntegrationSection6.ProductStructuralCoordinates

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k l j : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

def gammaProductCommReindexedIsoAt (U : GammaObjectAt B S k) (V : GammaObjectAt B S l) :
    GammaIsoAt (gammaProductAt U V) ((gammaProductAt V U).reindexVolume finAddFlip) :=
  GammaIsoAt.ofAmbientFormula (@rvProductCommReindexedIso M N S k l U.object.obj V.object.obj)
    (@selectRVTuple M N B.real (rvObjectArity U.object.obj+rvObjectArity V.object.obj)
      (rvObjectArity V.object.obj+rvObjectArity U.object.obj)
      (finAddFlip : Fin (rvObjectArity U.object.obj+rvObjectArity V.object.obj) ≃ Fin (rvObjectArity V.object.obj+rvObjectArity U.object.obj)).symm
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N
        (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj+rvObjectArity V.object.obj)) B.real))
    (fun x => @rvProductSwapMap_labels M N S k l U.object.obj V.object.obj x)

def gammaProductAssocReindexedIsoAt (U : GammaObjectAt B S k) (V : GammaObjectAt B S l) (W : GammaObjectAt B S j) :
    GammaIsoAt (gammaProductAt (gammaProductAt U V) W)
      ((gammaProductAt U (gammaProductAt V W)).reindexVolume (finCongr (Nat.add_assoc k l j))) :=
  GammaIsoAt.ofAmbientFormula (@rvProductAssocReindexedIso M N S k l j U.object.obj V.object.obj W.object.obj)
    (@selectRVTuple M N B.real ((rvObjectArity U.object.obj+rvObjectArity V.object.obj)+rvObjectArity W.object.obj)
      (rvObjectArity U.object.obj+(rvObjectArity V.object.obj+rvObjectArity W.object.obj))
      (Fin.cast (Nat.add_assoc (rvObjectArity U.object.obj) (rvObjectArity V.object.obj) (rvObjectArity W.object.obj)).symm)
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N
        (@SpecialTransformations.Section4.rawRVSpace M N ((rvObjectArity U.object.obj+rvObjectArity V.object.obj)+rvObjectArity W.object.obj)) B.real))
    (fun x => @rvProductAssocMap_labels M N S k l j U.object.obj V.object.obj W.object.obj x)

end IntegrationInACVF.Section6.FiniteRV
