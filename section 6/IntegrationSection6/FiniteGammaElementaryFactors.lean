import IntegrationSection6.FiniteGammaVolumeDeletion
import IntegrationSection6.FiniteGammaBasicFactors
import IntegrationSection6.FiniteGammaProducts
import IntegrationSection6.FiniteGammaFormulaIsos
import IntegrationSection6.FiniteGammaElementaryAt
import IntegrationSection6.SingletonProductCoordinates
import IntegrationSection6.VolumeDeletionWeights

/-! An admissible coordinate can be deleted without leaving RV[k-1].
The original object and its elementary blowup then factor, up to genuine
Gamma finite isomorphism, through the same deleted-coordinate object and
the two degree-one basic factors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)

def gammaAdmissibleFactorOne (U : GammaObjectAt B S (n+1)) (i : Fin (n+1))
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject i) :
    GammaIsoAt U (gammaProductAt (gammaDeleteVolumeAt hκ hs h00 hsmall U i hAd) (gammaOneAt U.real_contains)) := by
  let V := gammaDeleteVolumeAt hκ hs h00 hsmall U i hAd
  let R := gammaOneAt U.real_contains
  let T := gammaProductAt V R
  let F := @rvSingletonProductMap M N S (rvObjectArity U.object.obj) (rvObjectDomain U.object.obj)
  have hF := @rvSingletonProductMap_bijective M N S (rvObjectArity U.object.obj) (rvObjectDomain U.object.obj)
  have hΓ := gamma_rv_graph_of_global_formula F
    (@SpecialTransformations.DefinableGeometry.Map.id LRV M N _ B.real
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N
        (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) B.real)) U.domain_graph (fun _ => rfl)
  have hOrd := hAd.ordinary hκ hs h00 hsmall
  have hw (u : rvObjectDomain U.object.obj) :
      @rvWeight M N (n+1) (@RVObject.value M N S (n+1) U.object.obj u) =
      @rvWeight M N (n+1) (@RVObject.value M N S (n+1) T.object.obj (F u)) := by
    let A := U.object.obj
    let D := V.object.obj
    let Q := R.object.obj
    letI := N
    letI := hN
    change rvWeight (A.value u) = rvWeight ((rvProductObject D Q).value (F u))
    rw [rvSingletonProductMap_pair]
    change rvWeight (A.value u) = rvWeight ((rvProductObject D Q).value
      (rvPackPair D.domain Q.domain u ⟨Fin.elim0,Set.mem_univ _⟩))
    rw [rvProductObject_value_pair,rvWeight_append]
    change rvWeight (A.value u) = rvWeight (fun j => A.value u (i.succAbove j)) +
      rvWeight (fun _ : Fin 1 => (1 : CanonicalRV.RVSort M))
    rw [rvWeight_one_tuple]
    exact rvWeight_delete_nonzero (A.value u) i (hOrd.nonzero u)
  exact { iso := @isoOfDefinableBijection M N S (n+1) U.object T.object F hF hw, graph := hΓ }

def gammaAdmissibleFactorPositive (U : GammaObjectAt B S (n+1)) (i : Fin (n+1))
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject i) :
    GammaIsoAt (gammaElementaryAt hκ hs h00 hsmall U i hAd)
      (gammaProductAt (gammaDeleteVolumeAt hκ hs h00 hsmall U i hAd) (gammaPositiveAt U.real_contains)) := by
  let E := gammaElementaryAt hκ hs h00 hsmall U i hAd
  let V := gammaDeleteVolumeAt hκ hs h00 hsmall U i hAd
  let R := gammaPositiveAt U.real_contains
  let T := gammaProductAt V R
  let F := @SpecialTransformations.DefinableGeometry.Map.id LRV M N _ S (rvObjectDomain E.object.obj)
  have hΓ := gamma_rv_graph_of_global_formula F
    (@SpecialTransformations.DefinableGeometry.Map.id LRV M N _ B.real
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N
        (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity E.object.obj)) B.real)) E.domain_graph (fun _ => rfl)
  have hOrd := hAd.ordinary hκ hs h00 hsmall
  have hw (x : rvObjectDomain E.object.obj) :
      @rvWeight M N (n+1) (@RVObject.value M N S (n+1) E.object.obj x) =
      @rvWeight M N (n+1) (@RVObject.value M N S (n+1) T.object.obj (F x)) := by
    let A := U.object.obj
    let D := V.object.obj
    let Q := R.object.obj
    letI := N
    letI := hN
    obtain ⟨u,s,rfl⟩ := exists_rvPackPair A.domain (positiveRV S) x
    change rvWeight ((IntegrationInACVF.Section6.elementary A i).value
      (rvPackPair A.domain (positiveRV S) u s)) =
      rvWeight ((rvProductObject D Q).value (rvPackPair D.domain Q.domain u s))
    rw [elementary_value,elementaryProjection_pair,elementaryParameter_pair,
      rvProductObject_value_pair,rvWeight_append]
    exact blowupValue_weight_deleted (A.value u) i (s.val 0) (hOrd.nonzero u)
  exact { iso := @isoOfDefinableBijection M N S (n+1) E.object T.object F Function.bijective_id hw, graph := hΓ }

end IntegrationInACVF.Section6.FiniteRV
