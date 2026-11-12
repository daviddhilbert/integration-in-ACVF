import IntegrationSection6.GammaWeightedDegreeIsomorphisms
import IntegrationSection6.FiniteGammaProducts
import IntegrationSection6.GammaCompressionIsomorphisms
import IntegrationSection6.FiniteGammaAmbientIsos
import Section4.RVPaddingSplit
import IntegrationSection6.GammaWeightStrata
import Section4.RVFinitePadding
import IntegrationSection6.FiniteGammaIsoLaws

/-! Original-Gamma RV[k] data at a fixed internal real presentation.
The parameter set S describes codes only; every domain and volume graph
is still certified over the original Base B. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaWeightedPadProductLeftAt {k l : ℕ} (U : GammaObjectAt B S k) (V : GammaObjectAt B S l) :
    GammaWeightedIsoAt (gammaProductAt (gammaPadAt U) V) (gammaProductAt U V) := by
  let A := gammaProductAt (gammaPadAt U) V
  let C := gammaProductAt U V
  let F := @SpecialTransformations.DefinableGeometry.Map.id LRV M N _ S (rvObjectDomain A.object.obj)
  let Uo := U.object.obj
  let Vo := V.object.obj
  have hw (x : rvObjectDomain A.object.obj) :
      @rvWeight M N ((k+1)+l) (@RVObject.value M N S ((k+1)+l) A.object.obj x) =
      @rvWeight M N (k+l) (@RVObject.value M N S (k+l) C.object.obj (F x)) := by
    letI : LRV.Structure M := N
    letI : M ⊨ Axioms.ACVF := hN
    obtain ⟨u,v,rfl⟩ := exists_rvPackPair Uo.domain Vo.domain x
    change rvWeight ((rvProductObject (rvPadObject Uo) Vo).value (rvPackPair Uo.domain Vo.domain u v)) =
      rvWeight ((rvProductObject Uo Vo).value (rvPackPair Uo.domain Vo.domain u v))
    have hm : rvWeight (rvAppend ((rvPadObject Uo).value u) (Vo.value v)) = rvWeight (rvAppend (Uo.value u) (Vo.value v)) := by
      rw [rvWeight_append,rvWeight_append,rvPadObject_value,rvWeight_padRV]
    exact (congrArg rvWeight (rvProductObject_value_pair (rvPadObject Uo) Vo u v)).trans
      (hm.trans (congrArg rvWeight (rvProductObject_value_pair Uo Vo u v)).symm)
  exact {
    map := F
    bijective := Function.bijective_id
    graph := (gammaIsoRefl A.toGamma).graph
    weight := hw }

def gammaWeightedPadProductRightAt {k l : ℕ} (U : GammaObjectAt B S k) (V : GammaObjectAt B S l) :
    GammaWeightedIsoAt (gammaProductAt U (gammaPadAt V)) (gammaProductAt U V) := by
  let A := gammaProductAt U (gammaPadAt V)
  let C := gammaProductAt U V
  let F := @SpecialTransformations.DefinableGeometry.Map.id LRV M N _ S (rvObjectDomain A.object.obj)
  let Uo := U.object.obj
  let Vo := V.object.obj
  have hw (x : rvObjectDomain A.object.obj) :
      @rvWeight M N (k+(l+1)) (@RVObject.value M N S (k+(l+1)) A.object.obj x) =
      @rvWeight M N (k+l) (@RVObject.value M N S (k+l) C.object.obj (F x)) := by
    letI : LRV.Structure M := N
    letI : M ⊨ Axioms.ACVF := hN
    obtain ⟨u,v,rfl⟩ := exists_rvPackPair Uo.domain Vo.domain x
    change rvWeight ((rvProductObject Uo (rvPadObject Vo)).value (rvPackPair Uo.domain Vo.domain u v)) =
      rvWeight ((rvProductObject Uo Vo).value (rvPackPair Uo.domain Vo.domain u v))
    have hm : rvWeight (rvAppend (Uo.value u) ((rvPadObject Vo).value v)) = rvWeight (rvAppend (Uo.value u) (Vo.value v)) := by
      rw [rvWeight_append,rvWeight_append,rvPadObject_value,rvWeight_padRV]
    exact (congrArg rvWeight (rvProductObject_value_pair Uo (rvPadObject Vo) u v)).trans
      (hm.trans (congrArg rvWeight (rvProductObject_value_pair Uo Vo u v)).symm)
  exact {
    map := F
    bijective := Function.bijective_id
    graph := (gammaIsoRefl A.toGamma).graph
    weight := hw }

end IntegrationInACVF.Section6.FiniteRV
