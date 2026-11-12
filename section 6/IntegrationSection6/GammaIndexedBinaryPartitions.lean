import IntegrationSection6.GammaSchemaIndexedRestrictionIso
import IntegrationSection6.GammaGraphPresentationRestriction
import IntegrationSection6.GammaUniversalSubsets
import IntegrationSection6.IndexedSetPartitions
import IntegrationSection6.FiniteGammaPartitionCharts
import IntegrationSection6.FiniteGammaAdditiveCongruence

/-! Two Gamma-definable index regions glue actual common blowups. The
base volume is preserved on each region, and both indexed objects split
by genuine finite-category partition isomorphisms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Milestone0.sortEval
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)
open FiniteRV

theorem gammaIndexed_binary_isp {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ)
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv)) (G : GammaFiniteRVSchema B p b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (E : Set (Fin p → RV (M := M))) (hET : E ⊆ T)
    (hEΓ : GammaSetDefinable B {t : Point (M := M) 0 p | t.2 ∈ E})
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP) :
    let BPA := BP.restrictDomain E hET hEΓ
    let BPC := BP.restrictDomain (T \ E) (fun _ h => h.1) ((gammaLogicInput B).sdiff BP.domain_graph hEΓ)
    ∀ (PA : F.IndexedPresentation BPA) (QA : G.IndexedPresentation BPA)
      (PC : F.IndexedPresentation BPC) (QC : G.IndexedPresentation BPC),
    GammaIspAt hκ hs h00 hreal (gammaUniversalObject PA.toGamma) (gammaUniversalObject QA.toGamma) →
    GammaIspAt hκ hs h00 hreal (gammaUniversalObject PC.toGamma) (gammaUniversalObject QC.toGamma) →
    GammaIspAt hκ hs h00 hreal (gammaUniversalObject P.toGamma) (gammaUniversalObject Q.toGamma) := by
  dsimp only
  let BPA := BP.restrictDomain E hET hEΓ
  let BPC := BP.restrictDomain (T \ E) (fun _ h => h.1) ((gammaLogicInput B).sdiff BP.domain_graph hEΓ)
  intro PA QA PC QC hInside hOutside
  let UP := gammaUniversalObject P.toGamma
  let UQ := gammaUniversalObject Q.toGamma
  obtain ⟨AP,hAP⟩ := exists_gammaUniversalDefSet
    (indexedDomain E (fun t => F.rowDomain (fun j => (t j).val))) (F.indexed_domain_graph BPA)
  obtain ⟨AQ,hAQ⟩ := exists_gammaUniversalDefSet
    (indexedDomain E (fun t => G.rowDomain (fun j => (t j).val))) (G.indexed_domain_graph BPA)
  have hΓAP : GammaSetDefinable B {w : Point (M := M) 0 (p+a) |
      w.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ AP} := by
    convert F.indexed_domain_graph BPA using 1
    exact Set.ext (fun w => Set.ext_iff.mp hAP w.2)
  have hΓAQ : GammaSetDefinable B {w : Point (M := M) 0 (p+b) |
      w.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ AQ} := by
    convert G.indexed_domain_graph BPA using 1
    exact Set.ext (fun w => Set.ext_iff.mp hAQ w.2)
  have hSubAP : @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ AP ⊆
      @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ (rvObjectDomain UP.object.obj) := by
    intro w hw
    apply (Set.ext_iff.mp P.domain_eq w).mpr
    exact indexedDomain_mono hET _ ((Set.ext_iff.mp hAP w).mp hw)
  have hSubAQ : @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ AQ ⊆
      @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ (rvObjectDomain UQ.object.obj) := by
    intro w hw
    apply (Set.ext_iff.mp Q.domain_eq w).mpr
    exact indexedDomain_mono hET _ ((Set.ext_iff.mp hAQ w).mp hw)
  let CP := @complement M N Set.univ (d+k) UP.object.obj AP
  let CQ := @complement M N Set.univ (d+k) UQ.object.obj AQ
  have hCP : @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ CP =
      indexedDomain (T \ E) (fun t => F.rowDomain (fun j => (t j).val)) := by
    change (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ (rvObjectDomain UP.object.obj) \
      @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ AP) = _
    have hP : @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ (rvObjectDomain UP.object.obj) =
        indexedDomain T (fun t => F.rowDomain (fun j => (t j).val)) := P.domain_eq
    rw [hP,hAP,indexedDomain_sdiff]
  have hCQ : @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ CQ =
      indexedDomain (T \ E) (fun t => G.rowDomain (fun j => (t j).val)) := by
    change (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ (rvObjectDomain UQ.object.obj) \
      @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ AQ) = _
    have hQ : @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ (rvObjectDomain UQ.object.obj) =
        indexedDomain T (fun t => G.rowDomain (fun j => (t j).val)) := Q.domain_eq
    rw [hQ,hAQ,indexedDomain_sdiff]
  let ePA := F.indexedRestrictionIso BP BPA (BP.restrictDomain_totalVolume E hET hEΓ) P PA AP hSubAP hAP hΓAP
  let eQA := G.indexedRestrictionIso BP BPA (BP.restrictDomain_totalVolume E hET hEΓ) Q QA AQ hSubAQ hAQ hΓAQ
  have ePC : GammaIsoAt (gammaComplementAt UP AP hΓAP) (gammaUniversalObject PC.toGamma) :=
    F.indexedRestrictionIso BP BPC
      (BP.restrictDomain_totalVolume (T \ E) (fun _ h => h.1) ((gammaLogicInput B).sdiff BP.domain_graph hEΓ))
      P PC CP (@complement_subset M N hN Set.univ (d+k) UP.object.obj AP) hCP
      ((gammaLogicInput B).sdiff UP.domain_graph hΓAP)
  have eQC : GammaIsoAt (gammaComplementAt UQ AQ hΓAQ) (gammaUniversalObject QC.toGamma) :=
    G.indexedRestrictionIso BP BPC
      (BP.restrictDomain_totalVolume (T \ E) (fun _ h => h.1) ((gammaLogicInput B).sdiff BP.domain_graph hEΓ))
      Q QC CQ (@complement_subset M N hN Set.univ (d+k) UQ.object.obj AQ) hCQ
      ((gammaLogicInput B).sdiff UQ.domain_graph hΓAQ)
  have hA := hInside.corollary_6_6 ePA eQA
  have hC := hOutside.corollary_6_6 ePC eQC
  exact (hA.coprod hC).corollary_6_6
    (gammaPartitionIsoAt UP AP hSubAP hΓAP).symm (gammaPartitionIsoAt UQ AQ hSubAQ hΓAQ).symm

end IntegrationInACVF.Section6
