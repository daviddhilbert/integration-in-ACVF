import IntegrationSection6.GammaFamilyCoordinates

/-! Elementary blowup formulas uniformly in the VF parameter block. The
actual positive RV factor and actual volume multiplication program are
used, retaining all original-Gamma graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def familyBlowupVolumeMap (S : Set M) (i : Fin k) :
    Map (PresentedSet.univ (pointSpace (M := M) 0 (k+1)) S)
      (PresentedSet.univ (pointSpace (M := M) 0 k) S) :=
  @mapRVLabels M sM hM 0 (k+1) k S (@oldVolumeParameterBlowupMap M N hN k S i)

theorem familyBlowupVolumeMap_value (S : Set M) (i : Fin k)
    (x : PresentedSet.univ (pointSpace (M := M) 0 (k+1)) S) :
    (familyBlowupVolumeMap S i x).val.2 =
      (@oldVolumeParameterBlowupMap M N hN k S i ⟨x.val.2,Set.mem_univ _⟩).val := rfl

def GammaRVFamilyFormula.elementary (F : GammaRVFamilyFormula B p a k) (i : Fin k) :
    GammaRVFamilyFormula B p (a+1) k := by
  let L := gammaLogicInput B
  let head := familyOldLabelsMap B.real p a
  let param := familyNewParameterMap B.real p a
  let hv := rvCoordinatePointMap (Fin.castAdd 1 : Fin k → Fin (k+1)) B.real
  let sv := rvCoordinatePointMap (Fin.natAdd k : Fin 1 → Fin (k+1)) B.real
  let blow := familyBlowupVolumeMap B.real i
  let Pos : Set (Point (M := M) 0 1) := {q | q.2 ∈
    @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ B.real (@positiveRV M N B.real)}
  let D : Set (Point (M := M) p (a+1)) :=
    {x | (head ⟨x,Set.mem_univ _⟩).val ∈ F.domain ∧ (param ⟨x,Set.mem_univ _⟩).val ∈ Pos}
  have hD : GammaSetDefinable B D :=
    L.inter (gamma_global_preimage head F.domain_definable) (gamma_global_preimage param gamma_positiveRV)
  let R := fun (x : Point (M := M) p (a+1)) (r : Point (M := M) 0 (k+1)) =>
    F.volume (head ⟨x,Set.mem_univ _⟩).val (hv ⟨r,Set.mem_univ _⟩).val ∧
      (param ⟨x,Set.mem_univ _⟩).val = (sv ⟨r,Set.mem_univ _⟩).val
  have hR : GammaGraphDefinable B R :=
    (F.volume_definable.preimage_maps head hv).inter
      ((gamma_global_map_graph param).preimage_maps
        (@Map.id M sM _ B.real (PresentedSet.univ (pointSpace (M := M) p (a+1)) B.real)) sv)
  let VE := fun (x : Point (M := M) p (a+1)) (y : Point (M := M) 0 k) =>
    ∃ r : Point (M := M) 0 (k+1), (x ∈ D ∧ R x r) ∧ (blow ⟨r,Set.mem_univ _⟩).val = y
  have hVE : GammaGraphDefinable B VE :=
    L.comp_graph (L.restrict_graph hD hR) (gamma_global_map_graph blow)
  exact ⟨D,hD,VE,hVE⟩

theorem GammaRVFamilyFormula.elementary_domain (F : GammaRVFamilyFormula B p a k)
    (i : Fin k) (x : Point (M := M) p (a+1)) :
    x ∈ (F.elementary i).domain ↔
      (x.1,fun j => x.2 (Fin.castAdd 1 j)) ∈ F.domain ∧
      (fun j : Fin 1 => x.2 (Fin.natAdd a j)) ∈
        @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ B.real (@positiveRV M N B.real) := by
  have hh := @familyOldLabelsMap_value M sM hM B.real p a ⟨x,Set.mem_univ _⟩
  have hp := @familyNewParameterMap_value M sM hM B.real p a ⟨x,Set.mem_univ _⟩
  change ((_ ∈ F.domain) ∧ (_ ∈
    @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ B.real (@positiveRV M N B.real))) ↔ _
  exact and_congr (Iff.of_eq (congrArg (fun q : Point (M := M) p a => q ∈ F.domain) hh))
    (Iff.of_eq (congrArg (fun r : Fin 1 → RV (M := M) => r ∈
      @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ B.real (@positiveRV M N B.real)) hp))

end IntegrationInACVF.Section6
