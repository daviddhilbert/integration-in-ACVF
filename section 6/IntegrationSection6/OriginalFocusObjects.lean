import IntegrationSection6.NormalizedFocus
import IntegrationSection6.NativeFocusBlowup

/-! The original-model post-focus RV object agrees with the one used in
the normalized blowup proof. This keeps the original Gamma graph context. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def originalFocusObject {A : DefSet (M := M) S n m} {i : Fin n} {k : Fin m}
    (D : Focus A i k) := pullbackObject D.etaImage

theorem originalFocusObject_mem {A : DefSet (M := M) S n m} {i : Fin n} {k : Fin m}
    (D : Focus A i k) (r : Fin (n+m) → CanonicalRV.RVSort M) :
    r ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N
      (@SpecialTransformations.Section4.rawRVSpace M N (n+m)) S
      (@SpecialTransformations.Section4.RVObject.domain M N S n (originalFocusObject D)) ↔
      ∃ a : A, Fin.append (fun j => rv ((D.toFocusGeometry.eta a.val).1 j)) a.val.2 = r := by
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

/-- The isomorphism is the identity on the full RV key tuple and therefore
preserves its entire projected volume tuple. -/
def originalNativeFocusIso {A : DefSet (M := M) S n m} {i : Fin n} {k : Fin m}
    (D : Focus A i k) :
    letI : LRV.Structure M := N
    letI : M ⊨ Axioms.ACVF := hN
    (@originalFocusObject M sM hM S n m A i k D) ≅
      (@nativeFocusObject M sM hM S n m
        (@normalizedPointSet M sM hM S n m A) i k (@normalizedFocus M sM hM S n m A i k D)) := by
  let C := originalFocusObject D
  let DN := normalizedFocus D
  let Q := @nativeFocusObject M sM hM S n m (normalizedPointSet A) i k DN
  have ho := @originalFocusObject_mem M sM hM S n m A i k D
  have hn := @nativeFocusObject_mem M sM hM S n m (normalizedPointSet A) i k DN
  have hkey (a : A) :
      Fin.append (fun j => @rv M N hN
        ((@FocusGeometry.eta M N hN n m (carrier A) i k (normalizedFocusGeometry D.toFocusGeometry) a.val).1 j)) a.val.2 =
      Fin.append (fun j => rv ((D.toFocusGeometry.eta a.val).1 j)) a.val.2 := by
    apply congrArg₂ Fin.append ?_ rfl
    funext j
    rw [focusGeometry_eta_normalize]
    exact rv_normalize _
  letI := N
  letI := hN
  have hc : C.domain.carrier = Q.domain.carrier := by
    ext r
    refine (ho r).trans (Iff.trans ?_ (hn r).symm)
    constructor
    · rintro ⟨a,ha⟩
      exact ⟨⟨a.val,a.property⟩,(hkey a).trans ha⟩
    · rintro ⟨a,ha⟩
      let b : A := ⟨a.val,a.property⟩
      exact ⟨b,(hkey b).symm.trans ha⟩
  exact SpecialTransformations.Section4.rvIsoOfCarrierEq C.domain Q.domain C.volume Q.volume hc (fun _ => rfl)

end IntegrationInACVF.Section6
