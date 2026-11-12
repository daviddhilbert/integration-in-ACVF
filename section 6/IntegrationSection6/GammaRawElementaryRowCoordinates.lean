import IntegrationSection6.GammaRawElementarySchemata

/-! Row identities for the native coordinate programs used in sorted
families. The absorbing point is retained by the positive factor. -/
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
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem rawPositiveDomain_tuple_iff (B : Base (M := M)) (S : Set M)
    (x : Fin 1 → RV (M := M)) :
    (fun j => (x j).val) ∈ rawPositiveDomain B ↔
      x ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (@positiveRV M N S) := by
  constructor
  · rintro ⟨u,hu⟩
    have he : u.val = x := by
      funext j
      exact Subtype.ext (congrFun hu j)
    exact he ▸ u.property
  · intro hx
    exact ⟨⟨x,hx⟩,rfl⟩

theorem rawBlowupVolumeGraph_tuple_iff (B : Base (M := M)) {k : ℕ} (i : Fin k)
    (r : Fin (k+1) → RV (M := M)) (y : Fin k → RV (M := M)) :
    Fin.append (fun j => (r j).val) (fun j => (y j).val) ∈ rawBlowupVolumeGraph B i ↔
      (@oldVolumeParameterBlowupMap M N hN k B.real i ⟨r,Set.mem_univ _⟩).val = y := by
  have hh := gammaRawRVGraph_append_iff
    (fun r q => (familyBlowupVolumeMap B.real i ⟨r,Set.mem_univ _⟩).val = q)
    (Fin.elim0,r) (Fin.elim0,y)
  rw [rawBlowupVolumeGraph,hh]
  change (familyBlowupVolumeMap B.real i ⟨(Fin.elim0,r),Set.mem_univ _⟩).val = (Fin.elim0,y) ↔ _
  constructor
  · exact fun h => congrArg Prod.snd h
  · intro h
    exact Prod.ext (Subsingleton.elim _ _) h

theorem rawElementaryOldVolumeCoordinates_append {Y : Type*} {p a k : ℕ}
    (z : Fin p → Y) (x : Fin (a+1) → Y) (y v : Fin k → Y) :
    Fin.append (Fin.append (Fin.append z x) y) v ∘ rawElementaryOldVolumeCoordinates p a k =
      Fin.append (Fin.append z (x ∘ Fin.castAdd 1)) v := by
  funext j
  refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · refine Fin.addCases (fun m => ?_) (fun m => ?_) l <;>
      simp only [Function.comp_apply,rawElementaryOldVolumeCoordinates,Fin.addCases_left,
        Fin.addCases_right,Fin.append_left,Fin.append_right]
  · simp only [Function.comp_apply,rawElementaryOldVolumeCoordinates,Fin.addCases_right,Fin.append_right]

theorem rawElementaryBlowupCoordinates_append {Y : Type*} {p a k : ℕ}
    (z : Fin p → Y) (x : Fin (a+1) → Y) (y v : Fin k → Y) :
    Fin.append (Fin.append (Fin.append z x) y) v ∘ rawElementaryBlowupCoordinates p a k =
      Fin.append (Fin.append v (x ∘ Fin.natAdd a)) y := by
  funext j
  refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · refine Fin.addCases (fun m => ?_) (fun m => ?_) l <;>
      simp only [Function.comp_apply,rawElementaryBlowupCoordinates,Fin.addCases_left,
        Fin.addCases_right,Fin.append_left,Fin.append_right]
  · simp only [Function.comp_apply,rawElementaryBlowupCoordinates,Fin.addCases_right,Fin.append_left,Fin.append_right]

theorem sorted_append_RV {p a : ℕ} (sp : Fin p → SortTag) (z : Fin p → M)
    (hz : ∀ j, sortEval (sp j) (z j)) (x : Fin a → RV (M := M)) :
    Fin.append z (fun j => (x j).val) ∈ sortedUniverse (Fin.append sp (fun _ : Fin a => .rv)) := by
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simpa only [Fin.append_left] using hz i
  · simpa only [Fin.append_right,sortEval,iRV] using (x i).property

end IntegrationInACVF.Section6
