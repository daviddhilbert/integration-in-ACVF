import Integration7.DefinableNameMapDescent
import Integration7.HKZeroCoefficientExtensions

/-! Definable parameter names do not identify new exact weighted-zero
classes. The actual finite label bijection descends with its density equation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def ZeroRVVolumeIso.descendDefinableNames {S T : Set M} (hST : S ⊆ T)
    (hT : ∀ t ∈ T, S.Definable₁ LRV {t}) {U V : ZeroRVVolumeObject (M := M) S}
    (e : ZeroRVVolumeIso (U.extend hST) (V.extend hST)) : ZeroRVVolumeIso U V :=
  ZeroRVVolumeIso.ofBijection (mapDescendDefinableNames hST hT (finiteIsoMap e.iso))
    (finiteIsoMap_bijective e.iso) e.density

theorem zero_volume_coefficient_extend_injective_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M))
    (hD : ∀ d ∈ (D.base : Set M), (C.base : Set M).Definable₁ LRV {d}) :
    Function.Injective (zeroVolumeCoefficientExtend hc C D hCD) := by
  intro u v
  induction u using Quotient.inductionOn with
  | h U =>
    induction v using Quotient.inductionOn with
    | h V =>
      intro h
      obtain ⟨e⟩ := (rvVolumeBlowupClass_eq_iff hc D (n := 0)).mp h
      exact Quotient.sound ⟨e.descendDefinableNames hCD hD⟩

end IntegrationInACVF.Section7.HK
