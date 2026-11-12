import IntegrationSection6.GammaDefinableBaseReduction
import IntegrationSection6.FiniteGammaEquivalence

/-! Definable-name elimination preserves actual finite blowups, all
internal charts, exact chain lengths and common-blowup witnesses. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B C : Base (M := M)} {S : Set M} {n : ℕ}
open FiniteRV

def GammaDefinableBaseReduction.isoAt (H : GammaDefinableBaseReduction C B)
    {U V : GammaObjectAt C S n} (e : GammaIsoAt U V) : GammaIsoAt (H.objectAt U) (H.objectAt V) :=
  ⟨e.iso,H.definable e.graph⟩

def GammaDefinableBaseReduction.blowupAt (H : GammaDefinableBaseReduction C B)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hB : Cardinal.mk B.real < κ) (hC : Cardinal.mk C.real < κ)
    {U V : GammaObjectAt C S n} (F : GammaBlowupAt hκ hs h00 hC U V) :
    GammaBlowupAt hκ hs h00 hB (H.objectAt U) (H.objectAt V) where
  center := H.objectAt F.center
  remainder := H.objectAt F.remainder
  coordinate := F.coordinate
  admissible := H.admissible F.center.toGamma F.coordinate F.admissible
  source := H.isoAt F.source
  result := H.isoAt F.result

theorem GammaDefinableBaseReduction.chainAt (H : GammaDefinableBaseReduction C B)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hB : Cardinal.mk B.real < κ) (hC : Cardinal.mk C.real < κ)
    {r : ℕ} {U V : GammaObjectAt C S n} (F : GammaIteratedBlowup hκ hs h00 hC r U V) :
    GammaIteratedBlowup hκ hs h00 hB r (H.objectAt U) (H.objectAt V) := by
  induction F with
  | zero he => exact .zero (he.map H.isoAt)
  | cons he tail ih => exact .cons (he.map (H.blowupAt hκ hs h00 hB hC)) ih

theorem GammaDefinableBaseReduction.commonAt (H : GammaDefinableBaseReduction C B)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hB : Cardinal.mk B.real < κ) (hC : Cardinal.mk C.real < κ)
    {U V : GammaObjectAt C S n} (F : GammaIspAt hκ hs h00 hC U V) :
    GammaIspAt hκ hs h00 hB (H.objectAt U) (H.objectAt V) := by
  obtain ⟨r,s,A,D,hU,hV,he⟩ := F
  exact ⟨r,s,H.objectAt A,H.objectAt D,H.chainAt hκ hs h00 hB hC hU,
    H.chainAt hκ hs h00 hB hC hV,he.map H.isoAt⟩

theorem GammaDefinableBaseReduction.common (H : GammaDefinableBaseReduction C B)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hB : Cardinal.mk B.real < κ) (hC : Cardinal.mk C.real < κ)
    {U V : GammaRVFiniteObject C n} (F : GammaIsp hκ hs h00 hC U V) :
    GammaIsp hκ hs h00 hB (H.finiteObject U) (H.finiteObject V) := by
  obtain ⟨R,hUR,hVR,F⟩ := F
  exact ⟨R,hUR,hVR,H.commonAt hκ hs h00 hB hC F⟩

end IntegrationInACVF.Section6
