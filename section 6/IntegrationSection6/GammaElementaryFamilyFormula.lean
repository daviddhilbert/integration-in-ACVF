import IntegrationSection6.GammaElementaryFamilies
import IntegrationSection6.GammaFamilyRows
import IntegrationSection6.ElementaryGraphFormulas

/-! Literal typed-row formula for the uniform elementary family. -/
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

theorem GammaRVFamilyFormula.elementary_row_volume (F : GammaRVFamilyFormula B p a k)
    (i : Fin k) (z : Fin p → VF (M := M))
    (x : Fin (a+1) → RV (M := M)) (y : Fin k → RV (M := M)) :
    (F.elementary i).rowVolume z x y ↔
      x ∈ (F.elementary i).rowDomain z ∧
      ∃ v : Fin k → RV (M := M), F.rowVolume z (fun j => x (Fin.castAdd 1 j)) v ∧
        (@oldVolumeParameterBlowupMap M N hN k B.real i
          ⟨Fin.append v (fun j => x (Fin.natAdd a j)),Set.mem_univ _⟩).val = y := by
  constructor
  · rintro ⟨r,⟨hd,hf,hp⟩,hg⟩
    let v : Fin k → RV (M := M) := fun j => r.2 (Fin.castAdd 1 j)
    have hh := @familyOldLabelsMap_value M sM hM B.real p a ⟨(z,x),Set.mem_univ _⟩
    have hv : (rvCoordinatePointMap (Fin.castAdd 1 : Fin k → Fin (k+1)) B.real
        ⟨r,Set.mem_univ _⟩).val = (Fin.elim0,v) := rfl
    have hf' : F.rowVolume z (fun j => x (Fin.castAdd 1 j)) v :=
      (Iff.of_eq (congrArg₂ F.volume hh hv)).mp hf
    have hparam := @familyNewParameterMap_value M sM hM B.real p a ⟨(z,x),Set.mem_univ _⟩
    have hs : (fun j : Fin 1 => x (Fin.natAdd a j)) = (fun j => r.2 (Fin.natAdd k j)) :=
      hparam.symm.trans (congrArg Prod.snd hp)
    have hpack : Fin.append v (fun j => x (Fin.natAdd a j)) = r.2 := by
      rw [hs]
      exact Fin.append_castAdd_natAdd
    have hblow := @familyBlowupVolumeMap_value M sM hM k B.real i ⟨r,Set.mem_univ _⟩
    refine ⟨hd,v,hf',?_⟩
    have hG := congrArg (fun t : Fin (k+1) → RV (M := M) =>
      (@oldVolumeParameterBlowupMap M N hN k B.real i ⟨t,Set.mem_univ _⟩).val) hpack
    exact hG.trans (hblow.symm.trans (congrArg Prod.snd hg))
  · rintro ⟨hd,v,hf,hg⟩
    let s : Fin 1 → RV (M := M) := fun j => x (Fin.natAdd a j)
    let r : Point (M := M) 0 (k+1) := (Fin.elim0,Fin.append v s)
    have hh := @familyOldLabelsMap_value M sM hM B.real p a ⟨(z,x),Set.mem_univ _⟩
    have hv : (rvCoordinatePointMap (Fin.castAdd 1 : Fin k → Fin (k+1)) B.real
        ⟨r,Set.mem_univ _⟩).val = (Fin.elim0,v) := by
      apply Prod.ext (Subsingleton.elim _ _)
      funext j
      exact Fin.append_left v s j
    have hf' : F.volume (familyOldLabelsMap B.real p a ⟨(z,x),Set.mem_univ _⟩).val
        (rvCoordinatePointMap (Fin.castAdd 1 : Fin k → Fin (k+1)) B.real ⟨r,Set.mem_univ _⟩).val :=
      (Iff.of_eq (congrArg₂ F.volume hh hv)).mpr hf
    have hp : (familyNewParameterMap B.real p a ⟨(z,x),Set.mem_univ _⟩).val =
        (rvCoordinatePointMap (Fin.natAdd k : Fin 1 → Fin (k+1)) B.real ⟨r,Set.mem_univ _⟩).val := by
      apply Prod.ext (Subsingleton.elim _ _)
      have hparam := @familyNewParameterMap_value M sM hM B.real p a ⟨(z,x),Set.mem_univ _⟩
      refine hparam.trans ?_
      funext j
      exact (Fin.append_right v s j).symm
    have hblow : (familyBlowupVolumeMap B.real i ⟨r,Set.mem_univ _⟩).val = (Fin.elim0,y) := by
      apply Prod.ext (Subsingleton.elim _ _)
      exact (@familyBlowupVolumeMap_value M sM hM k B.real i ⟨r,Set.mem_univ _⟩).trans hg
    exact ⟨r,⟨hd,hf',hp⟩,hblow⟩

end IntegrationInACVF.Section6
