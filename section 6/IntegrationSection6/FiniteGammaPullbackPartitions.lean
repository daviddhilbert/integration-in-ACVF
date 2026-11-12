import IntegrationSection6.FiniteGammaPartitionCharts
import IntegrationSection6.FiniteGammaCoproductMaps
import IntegrationSection6.FiniteGammaFormulaIsos
import IntegrationSection6.PullbackPartitions

/-! Gamma charts for the RV data of a genuine partition into pullbacks. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n m : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaPullbackPartitionIsoAt (hBS : B.real ⊆ S)
    {A C E : SpecialTransformations.Section5.DefSet (M := M) S n m}
    (hA : GammaSetDefinable B (carrier A)) (hC : GammaSetDefinable B (carrier C))
    (hE : GammaSetDefinable B (carrier E))
    (hAF : Map.FiniteFibres (rvObjectVolume (pullbackObject A)))
    (hCF : Map.FiniteFibres (rvObjectVolume (pullbackObject C)))
    (hEF : Map.FiniteFibres (rvObjectVolume (pullbackObject E)))
    (hpart : carrier A = carrier C ∪ carrier E)
    (hdisj : Disjoint (carrier C) (carrier E)) (hCP : IsRVPullback (carrier C)) :
    GammaIsoAt (gammaPullbackAt hBS A hA hAF)
      (gammaCoprodAt (gammaPullbackAt hBS C hC hCF) (gammaPullbackAt hBS E hE hEF)) := by
  let U := gammaPullbackAt hBS A hA hAF
  let V := gammaPullbackAt hBS C hC hCF
  let W := gammaPullbackAt hBS E hE hEF
  let L := rvObjectDomain (pullbackObject C)
  have hc := pullbackObject_domain_mono (show carrier C ⊆ carrier A from fun p hp => (Set.ext_iff.mp hpart p).mpr (Or.inl hp))
  let R := gammaRestrictAt U L hc V.domain_graph
  let T := gammaComplementAt U L V.domain_graph
  have hu := pullbackObject_domains_union hpart
  have hd := pullbackObject_domains_disjoint hdisj hCP
  have he : @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain T.object.obj) =
      @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain W.object.obj) := by
    ext r
    constructor
    · rintro ⟨hr,hn⟩
      rcases (Set.ext_iff.mp hu r).mp hr with hr | hr
      · exact False.elim (hn hr)
      · exact hr
    · intro hr
      exact ⟨(Set.ext_iff.mp hu r).mpr (Or.inr hr),fun h => Set.disjoint_left.mp hd h hr⟩
  let eR := @rvIsoOfCarrierEq M N S n (n+m) (rvObjectDomain R.object.obj) (rvObjectDomain V.object.obj)
    (rvObjectVolume R.object.obj) (rvObjectVolume V.object.obj) rfl (fun _ => rfl)
  let eT := @rvIsoOfCarrierEq M N S n (n+m) (rvObjectDomain T.object.obj) (rvObjectDomain W.object.obj)
    (rvObjectVolume T.object.obj) (rvObjectVolume W.object.obj) he (fun _ => rfl)
  let Q := @SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@rawRVSpace M N (n+m)) B.real
  let G := @SpecialTransformations.DefinableGeometry.Map.id LRV M N _ B.real Q
  let fR : GammaIsoAt R V := GammaIsoAt.ofAmbientFormula eR G (fun _ => rfl)
  let fT : GammaIsoAt T W := GammaIsoAt.ofAmbientFormula eT G (fun _ => rfl)
  exact (gammaPartitionIsoAt U L hc V.domain_graph).symm.trans (gammaCoprodIsoAt fR fT)

end IntegrationInACVF.Section6.FiniteRV
