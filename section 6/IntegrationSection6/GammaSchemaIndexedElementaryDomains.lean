import IntegrationSection6.GammaSchemaIndexedPresentations
import IntegrationSection6.IndexedElementaryLabels

/-! The indexed elementary domain is exactly the native elementary domain
after reassociating the index, old labels and new parameter. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem GammaFiniteRVSchema.indexed_elementary_domain
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv)) (BP : GammaFiniteGraphPresentation B p d T R)
    (P : F.IndexedPresentation BP) (i : Fin k) (w : Fin (p+(a+1)) → RV (M := M)) :
    w ∈ indexedDomain T (fun t => (F.elementaryFormula i).rowDomain (fun j => (t j).val)) ↔
      indexedElementaryLabels w ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ P.codes
        (rvObjectDomain (gammaElementaryObject P.toGamma.toGammaRVObject (Fin.natAdd d i)).object) := by
  have hE := @elementary_domain_formula M N hN P.codes (d+k) P.toGamma.object (Fin.natAdd d i)
    (indexedElementaryLabels w)
  change _ ↔ _ ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ P.codes
    (rvObjectDomain (@elementary M N hN P.codes (d+k) P.toGamma.object (Fin.natAdd d i)))
  rw [hE]
  change _ ↔ ((indexedElementaryLabels w ∘ Fin.castAdd 1) ∈
    @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ P.codes P.domain ∧
    (indexedElementaryLabels w ∘ Fin.natAdd (p+a)) ∈
      @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ P.codes (@positiveRV M N P.codes))
  rw [indexedElementaryLabels_head,indexedElementaryLabels_parameter]
  rw [P.domain_eq]
  change (indexedLeft w ∈ T ∧ (indexedRight w) ∈ (F.elementaryFormula i).rowDomain _) ↔
    ((Fin.append (indexedLeft w) (indexedRight w ∘ Fin.castAdd 1)) ∈ indexedDomain T
      (fun t => F.rowDomain (fun j => (t j).val)) ∧ _)
  rw [F.elementary_row_domain_formula i _ (fun j => (indexedLeft w j).property) (indexedRight w) P.codes]
  simp only [indexedDomain,Set.mem_ofPred_eq,indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right]
  tauto

end IntegrationInACVF.Section6
