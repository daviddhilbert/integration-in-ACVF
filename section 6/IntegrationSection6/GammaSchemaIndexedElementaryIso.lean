import IntegrationSection6.GammaSchemaIndexedElementaryVolumes
import IntegrationSection6.GammaSchemaIndexedAdmissibility

/-! Indexed assembly commutes with a native elementary blowup. Every
object lies in the finite-volume category, and the chart keeps its complete
original-base Gamma graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def GammaFiniteAdmissibilitySchema.indexedElementaryIso {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (A : GammaFiniteAdmissibilitySchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (hvalid : ∀ t ∈ T, A.valid (fun j => (t j).val))
    (P : A.object.IndexedPresentation BP) (EP : (A.object.elementaryFormula A.coordinate).IndexedPresentation BP) :
    GammaRVIso EP.toGamma.toGammaRVObject
      (gammaFiniteElementaryBasic hκ hs h00 hreal P.toGamma (Fin.natAdd d A.coordinate)
        (A.indexed_admissible BP hvalid P)).toGammaRVObject := by
  let E := gammaFiniteElementaryBasic hκ hs h00 hreal P.toGamma (Fin.natAdd d A.coordinate)
    (A.indexed_admissible BP hvalid P)
  let H := fun (w : Fin (p+(a+1)) → RV (M := M)) (y : Fin ((p+a)+1) → RV (M := M)) =>
    w ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ EP.codes EP.domain ∧ indexedElementaryLabels w = y
  have hDomain (w : Fin (p+(a+1)) → RV (M := M)) :
      w ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ EP.codes EP.domain ↔
      indexedElementaryLabels w ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ E.codes (rvObjectDomain E.object) :=
    (Set.ext_iff.mp EP.domain_eq w).trans (A.object.indexed_elementary_domain BP P A.coordinate w)
  have hΓ : GammaGraphDefinable B (fun (w : Point (M := M) 0 (p+(a+1)))
      (y : Point (M := M) 0 ((p+a)+1)) => H w.2 y.2) := by
    let f := rvCoordinatePointMap (indexedElementaryCoordinates p a) B.real
    have h := (gammaLogicInput B).restrict_graph EP.toGamma.domain_graph (gamma_global_map_graph f)
    apply GammaGraphDefinable.congr h
    intro w y
    change (_ ∧ (Fin.elim0,indexedElementaryLabels w.2) = y) ↔ (_ ∧ indexedElementaryLabels w.2 = y.2)
    constructor
    · rintro ⟨hw,he⟩
      cases he
      exact ⟨hw,rfl⟩
    · rintro ⟨hw,he⟩
      exact ⟨hw,Prod.ext (Subsingleton.elim _ _) he⟩
  refine FiniteRV.gammaIsoOfFiniteRelation EP.toGamma E H hΓ ?_ ?_ ?_ ?_ ?_
  · intro w y hw
    refine ⟨⟨⟨w,hw.1⟩,rfl⟩,⟨⟨y,?_⟩,rfl⟩⟩
    rw [← hw.2]
    exact (hDomain w).mp hw.1
  · intro u
    let v : rvObjectDomain E.object := ⟨indexedElementaryLabels u.val,(hDomain u.val).mp u.property⟩
    refine ⟨v,⟨u.property,rfl⟩,?_⟩
    intro v' hv'
    exact Subtype.ext hv'.2.symm
  · intro u u' v huv hu'v
    exact Subtype.ext ((indexedElementaryTupleEquiv (RV (M := M)) p a).injective (huv.2.trans hu'v.2.symm))
  · intro v
    let w := (indexedElementaryTupleEquiv (RV (M := M)) p a).symm v.val
    have hw : indexedElementaryLabels w = v.val := (indexedElementaryTupleEquiv (RV (M := M)) p a).apply_symm_apply v.val
    have hD : w ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ EP.codes EP.domain := by
      apply (hDomain w).mpr
      rw [hw]
      exact v.property
    exact ⟨⟨w,hD⟩,hD,hw⟩
  · intro u v huv
    change rawWeight (fun j => ((EP.volume u).val j).val) = rawWeight (fun j => ((rvObjectVolume E.object v).val j).val)
    apply congrArg (fun y : Fin (d+k) → RV (M := M) => rawWeight (fun j => (y j).val))
    have hw := (Set.ext_iff.mp EP.domain_eq u.val).mp u.property
    have hA := hvalid (indexedLeft u.val) hw.1
    have hF := A.object.finiteRow_of_valid _ hA.1
    have hE := A.elementary_finiteRow hκ hs h00 hreal _ hA
    have hRow := A.object.rowValue_elementary _ (fun j => (indexedLeft u.val j).property) A.coordinate
      hF hE (indexedRight u.val) hw.2
    have hSource := ((EP.graph_iff u.val (EP.volume u).val).mp ⟨u,rfl,rfl⟩).2.2.symm
    have hTarget := A.object.indexed_elementary_volume BP P A.coordinate u.val v huv.2.symm
    change (rvObjectVolume E.object v).val = _ at hTarget
    change (EP.volume u).val = _
    rw [hSource,hTarget]
    change Fin.append _ _ = Fin.append _ _
    exact congrArg (fun y : Fin k → RV (M := M) => Fin.append (BP.totalVolume (indexedLeft u.val)) y) hRow

end IntegrationInACVF.Section6
