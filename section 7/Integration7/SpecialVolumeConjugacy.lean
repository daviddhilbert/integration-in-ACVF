import Integration7.SpecialVolumeJacobians
import Integration7.RawVFVolumeComposition
import Integration7.RawPullbackVolumeLifts
import IntegrationSection5.RelativeLabelPreservation
import IntegrationSection5.UnaryBijectionPreparation

/-! Special preparations preserve the volume equation of the conjugated
bijection. Retained density labels supply the endpoint form identities. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (SpecialBijection IsRVPullback carrier pullbackObject rvObjectVolume)

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem special_retained_volume_density
    (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {k a b : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) S (k+1) a}
    {B : SpecialTransformations.Section5.DefSet (M := M) S (k+1) b}
    (T : SpecialBijection A B) (hB : IsRVPullback (carrier B))
    (hBF : @Map.FiniteFibres LRV M N _ _ S _ _ (rvObjectVolume (pullbackObject B)))
    (δ : Fin a)
    (hδ : ∀ p : B, (p.val.2 (T.chain.labelIndex δ)).val ≠ iRVZero)
    (ω : VolumeForm (rawSpecialSet hc A)) (hω : ∀ p, ω.value p = p.val.2 δ)
    (p : rawSpecialSet hc A) :
    ω.value p = (rawPullbackVolumeForm hc B hB hBF (T.chain.labelIndex δ) hδ).value
      ((rawSpecialMap hc T.toMap) p) := by
  rw [hω, rawPullbackVolumeForm_density]
  exact (T.chain.labelIndex_apply (show A from p) δ).symm

theorem unary_volume_conjugate
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {a b r s : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a}
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
    {A' : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 r}
    {B' : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 s}
    (TA : SpecialBijection A A') (TB : SpecialBijection B B')
    (f : SpecialTransformations.Section5.Map A B) (hf : Function.Bijective f)
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (ω' : VolumeForm (rawSpecialSet hc A')) (π' : VolumeForm (rawSpecialSet hc B'))
    (hω : ∀ p, ω.value p = ω'.value ((rawSpecialMap hc TA.toMap) p))
    (hπ : ∀ p, π.value p = π'.value ((rawSpecialMap hc TB.toMap) p))
    (hMeasure : PreservesVFVolume ω π (rawSpecialMap hc f)) :
    PreservesVFVolume ω' π'
      (rawSpecialMap hc (IntegrationInACVF.Section5.unaryConjugate TA TB f)) := by
  have hTA := (special_preserves_volume hc C (by decide : 0 < 1) TA ω ω' hω).2
  have hTB := (special_preserves_volume hc C (by decide : 0 < 1) TB π π' hπ).1
  have hAi : Function.Injective (rawSpecialMap hc TA.inverseMap) := by
    intro p q he
    have h : TA.toMap (TA.inverseMap (show A' from p)) =
        TA.toMap (TA.inverseMap (show A' from q)) := congrArg TA.toMap he
    rw [TA.apply_inverse, TA.apply_inverse] at h
    exact h
  have hmid := preservesVFVolume_comp hc C (by decide : 0 < 1) ω' ω π
    (rawSpecialMap hc TA.inverseMap) (rawSpecialMap hc f) hAi hTA hMeasure
  exact preservesVFVolume_comp hc C (by decide : 0 < 1) ω' π π'
    ((rawSpecialMap hc f).comp (rawSpecialMap hc TA.inverseMap)) (rawSpecialMap hc TB.toMap)
    (hf.1.comp hAi) hmid hTB

end IntegrationInACVF.Section7
