import IntegrationSection6.GammaRawElementaryRowCoordinates
import IntegrationSection6.ElementaryGraphFormulas

/-! Every proper sorted row of the raw elementary formulas is the native
elementary construction on that row. This is uniform in VF, RV, and mixed
parameter blocks, without adding representative codes to the base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem GammaFiniteRVSchema.elementary_row_domain_formula (F : GammaFiniteRVSchema B p a k sp)
    (i : Fin k) (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    (x : Fin (a+1) → RV (M := M)) (S : Set M) :
    x ∈ (F.elementaryFormula i).rowDomain z ↔
      (x ∘ Fin.castAdd 1) ∈ F.rowDomain z ∧
      (x ∘ Fin.natAdd a) ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (@positiveRV M N S) := by
  change ((Fin.append z (fun j => (x j).val) ∘ rawElementaryHead p a ∈ F.domain) ∧
    (Fin.append z (fun j => (x j).val) ∘ rawElementaryParameter p a ∈ rawPositiveDomain B) ∧ _) ↔ _
  rw [rawElementaryHead_append,rawElementaryParameter_append]
  have hp := sorted_append_RV sp z hz x
  have hs := rawPositiveDomain_tuple_iff B S (x ∘ Fin.natAdd a)
  exact ⟨fun h => ⟨h.1,hs.mp h.2.1⟩,fun h => ⟨h.1,hs.mpr h.2,hp⟩⟩

theorem GammaFiniteRVSchema.elementary_row_volume_formula (F : GammaFiniteRVSchema B p a k sp)
    (i : Fin k) (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    (x : Fin (a+1) → RV (M := M)) (y : Fin k → RV (M := M)) :
    (F.elementaryFormula i).rowVolume z x y ↔
      x ∈ (F.elementaryFormula i).rowDomain z ∧
      ∃ v : Fin k → RV (M := M), F.rowVolume z (x ∘ Fin.castAdd 1) v ∧
        (@oldVolumeParameterBlowupMap M N hN k B.real i
          ⟨Fin.append v (x ∘ Fin.natAdd a),Set.mem_univ _⟩).val = y := by
  let xx : Fin (p+(a+1)) → M := Fin.append z (fun j => (x j).val)
  let w : Fin ((p+(a+1))+k) → M := Fin.append xx (fun j => (y j).val)
  let st := Fin.append (Fin.append (Fin.append sp (fun _ : Fin (a+1) => SortTag.rv))
    (fun _ : Fin k => .rv)) (fun _ : Fin k => .rv)
  have hHead : w ∘ Fin.castAdd k = xx := by
    funext j
    exact Fin.append_left _ _ j
  have hOld (v : Fin k → M) : Fin.append w v ∘ rawElementaryOldVolumeCoordinates p a k =
      Fin.append (Fin.append z (fun j => (x (Fin.castAdd 1 j)).val)) v :=
    rawElementaryOldVolumeCoordinates_append z _ _ v
  have hBlow (v : Fin k → M) : Fin.append w v ∘ rawElementaryBlowupCoordinates p a k =
      Fin.append (Fin.append v (fun j => (x (Fin.natAdd a j)).val)) (fun j => (y j).val) :=
    rawElementaryBlowupCoordinates_append z _ _ v
  have hProper (v : Fin k → RV (M := M)) : Fin.append w (fun j => (v j).val) ∈ sortedUniverse st :=
    sorted_append_RV _ w (sorted_append_RV _ xx (sorted_append_RV sp z hz x) y) v
  have hVals (v : Fin k → RV (M := M)) :
      (fun j => (Fin.append v (x ∘ Fin.natAdd a) j).val) =
        Fin.append (fun j => (v j).val) (fun j => (x (Fin.natAdd a j)).val) := by
    funext j
    refine Fin.addCases (fun l => ?_) (fun l => ?_) j <;>
      simp only [Fin.append_left,Fin.append_right,Function.comp_apply]
  change (∃ v : Fin k → M, (_ ∧ _) ∧ (_ ∧ _) ∧ (_ ∧ _)) ↔ _
  constructor
  · rintro ⟨v,⟨hv,hp⟩,⟨hg,_⟩,⟨hd,_⟩⟩
    have hvs (j : Fin k) : iRV (v j) := by
      simpa only [st,Fin.append_right,sortEval,iRV] using hp (Fin.natAdd ((p+(a+1))+k) j)
    let vt : Fin k → RV (M := M) := fun j => ⟨v j,hvs j⟩
    refine ⟨?_,vt,?_,?_⟩
    · change xx ∈ F.elementaryDomain
      change w ∘ Fin.castAdd k ∈ F.elementaryDomain at hd
      rw [hHead] at hd
      exact hd
    · change Fin.append (Fin.append z (fun j => (x (Fin.castAdd 1 j)).val)) v ∈ F.volume
      exact hOld v ▸ hv
    · apply (rawBlowupVolumeGraph_tuple_iff B i (Fin.append vt (x ∘ Fin.natAdd a)) y).mp
      rw [hVals vt]
      exact hBlow v ▸ hg
  · rintro ⟨hd,v,hv,hg⟩
    refine ⟨fun j => (v j).val,⟨?_,hProper v⟩,⟨?_,hProper v⟩,⟨?_,hProper v⟩⟩
    · rw [hOld]
      exact hv
    · rw [hBlow]
      simpa only [hVals v] using
        (rawBlowupVolumeGraph_tuple_iff B i (Fin.append v (x ∘ Fin.natAdd a)) y).mpr hg
    · rw [hHead]
      exact hd

end IntegrationInACVF.Section6
