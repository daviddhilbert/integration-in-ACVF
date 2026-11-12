import IntegrationSection6.CollapsedRVObjects
import IntegrationSection6.NormalizedLifts
import IntegrationSection6.FullFocusBlowup

/-! The RV image object supplied by the released focus/canonical-map
construction, with its second normalization collapsed without changing labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def nativeFocusObject
    {A : @DefSet M N hN S n m} {i : Fin n} {k : Fin m}
    (D : @Focus M N hN S n m A i k) :
    @SpecialTransformations.Section4.RVObject M N S n := by
  letI := N
  letI := hN
  exact @collapseRVObject M sM S n (@pullbackObject M N hN S n m D.etaImage)

/-- All canonical labels, including every old RV coordinate, are retained. -/
theorem nativeFocusObject_mem
    {A : @DefSet M N hN S n m} {i : Fin n} {k : Fin m}
    (D : @Focus M N hN S n m A i k) (r : Fin (n+m) → CanonicalRV.RVSort M) :
    letI : LRV.Structure M := N
    letI : M ⊨ Axioms.ACVF := hN
    r ∈ (@nativeFocusObject M sM hM S n m A i k D).domain.carrier ↔
      ∃ a : A, Fin.append (fun j => rv ((D.toFocusGeometry.eta a.val).1 j)) a.val.2 = r := by
  letI := N
  letI := hN
  change (∃ b : D.etaImage, (rawKeyMap D.etaImage b).val = r) ↔ _
  constructor
  · rintro ⟨b,hb⟩
    obtain ⟨a,ha⟩ := b.property
    refine ⟨a,?_⟩
    have he : b.val = D.toFocusGeometry.eta a.val := ha.symm
    rw [rawKeyMap_apply,he,D.toFocusGeometry.eta_labels] at hb
    exact hb
  · rintro ⟨a,ha⟩
    let b : D.etaImage := Map.toImage D.etaMap a
    refine ⟨b,?_⟩
    rw [rawKeyMap_apply]
    change Fin.append (fun j => rv ((D.toFocusGeometry.eta a.val).1 j))
      (D.toFocusGeometry.eta a.val).2 = r
    rw [D.toFocusGeometry.eta_labels]
    exact ha

end IntegrationInACVF.Section6
