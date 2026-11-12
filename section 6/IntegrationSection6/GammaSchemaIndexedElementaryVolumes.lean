import IntegrationSection6.GammaSchemaIndexedElementaryDomains
import IntegrationSection6.GammaSchemaElementaryRowValues

/-! The native elementary volume of an indexed object keeps its index
volume prefix and applies the actual elementary program to the fibre. -/
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

theorem GammaFiniteRVSchema.indexed_elementary_volume
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv)) (BP : GammaFiniteGraphPresentation B p d T R)
    (P : F.IndexedPresentation BP) (i : Fin k) (w : Fin (p+(a+1)) → RV (M := M))
    (v : rvObjectDomain (gammaElementaryObject P.toGamma.toGammaRVObject (Fin.natAdd d i)).object)
    (hv : v.val = indexedElementaryLabels w) :
    (rvObjectVolume (gammaElementaryObject P.toGamma.toGammaRVObject (Fin.natAdd d i)).object v).val =
      Fin.append (BP.totalVolume (indexedLeft w))
        (@blowupValue M N hN k i (F.rowValue (fun j => (indexedLeft w j).val) (indexedRight w ∘ Fin.castAdd 1))
          (indexedRight w (Fin.natAdd a 0))) := by
  let pr := @elementaryProjection M N hN P.codes (d+k) P.toGamma.object (Fin.natAdd d i) v
  have hPr : pr.val = Fin.append (indexedLeft w) (indexedRight w ∘ Fin.castAdd 1) := by
    exact (@elementaryProjection_labels M N hN P.codes (d+k) P.toGamma.object (Fin.natAdd d i) v).trans
      ((congrArg (fun x => x ∘ Fin.castAdd 1) hv).trans (indexedElementaryLabels_head w))
  have hP : (P.volume pr).val = indexedVolume BP.totalVolume
      (fun t => F.rowValue (fun j => (t j).val)) pr.val :=
    ((P.graph_iff pr.val (P.volume pr).val).mp ⟨pr,rfl,rfl⟩).2.2.symm
  have hOld : (P.volume pr).val = Fin.append (BP.totalVolume (indexedLeft w))
      (F.rowValue (fun j => (indexedLeft w j).val) (indexedRight w ∘ Fin.castAdd 1)) := by
    rw [hP,hPr]
    simp only [indexedVolume,indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right]
  have hParam : (@elementaryParameter M N hN P.codes (d+k) P.toGamma.object (Fin.natAdd d i) v).val 0 =
      indexedRight w (Fin.natAdd a 0) := by
    exact (congrFun (@elementaryParameter_labels M N hN P.codes (d+k) P.toGamma.object (Fin.natAdd d i) v) 0).trans
      ((congrFun hv (Fin.natAdd (p+a) 0)).trans (congrFun (indexedElementaryLabels_parameter w) 0))
  have hValue := @elementary_value M N hN P.codes (d+k) P.toGamma.object (Fin.natAdd d i) v
  change (rvObjectVolume (gammaElementaryObject P.toGamma.toGammaRVObject (Fin.natAdd d i)).object v).val =
    @blowupValue M N hN (d+k) (Fin.natAdd d i) (P.volume pr).val
      ((@elementaryParameter M N hN P.codes (d+k) P.toGamma.object (Fin.natAdd d i) v).val 0) at hValue
  rw [hOld,hParam] at hValue
  exact hValue.trans (@blowupValue_append_right M N hN k d i _ _ _)

end IntegrationInACVF.Section6
