import Integration7.GammaVolumeGraphPresentations
import Integration7.CanonicalVolumeForms

/-! Convert a full original-Gamma presentation into the actual canonical
volume category. Original graph certificates and finite-extra base are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a k : ℕ}
variable {D : Set (Fin a → RV (M := M))}
variable {R : (Fin a → RV (M := M)) → (Fin k → RV (M := M)) → Prop}
variable {W : (Fin a → RV (M := M)) → (Fin 1 → RV (M := M)) → Prop}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def GammaVolumeGraphPresentation.canonicalData
    (hc : CanonicalStructure.IsCanonical (M := M))
    (P : GammaVolumeGraphPresentation B a k D R W) : RVVolumeData P.finite.codes k where
  underlying := ⟨{
    arity := a
    domain := canonicalRawRVDomain hc P.finite.domain
    volume := canonicalRawRVMap hc P.finite.volume },P.finite.finite_volume⟩
  form := canonicalRawRVForm hc P.form

@[simp] theorem GammaVolumeGraphPresentation.canonicalData_domain
    (hc : CanonicalStructure.IsCanonical (M := M))
    (P : GammaVolumeGraphPresentation B a k D R W) :
    (P.canonicalData hc).underlying.obj.domain.carrier = D := P.finite.domain_eq

theorem GammaVolumeGraphPresentation.canonicalData_volume_iff
    (hc : CanonicalStructure.IsCanonical (M := M))
    (P : GammaVolumeGraphPresentation B a k D R W) (x y) :
    (∃ u : (P.canonicalData hc).underlying.obj.domain,
      u.val = x ∧ ((P.canonicalData hc).underlying.obj.volume u).val = y) ↔ x ∈ D ∧ R x y :=
  P.finite.graph_iff x y

theorem GammaVolumeGraphPresentation.canonicalData_density_iff
    (hc : CanonicalStructure.IsCanonical (M := M))
    (P : GammaVolumeGraphPresentation B a k D R W) (x y) :
    (∃ u : (P.canonicalData hc).underlying.obj.domain,
      u.val = x ∧ ((P.canonicalData hc).form.map u).val = y) ↔ W x y :=
  P.density_iff x y

theorem GammaVolumeGraphPresentation.canonicalData_codes_small
    (P : GammaVolumeGraphPresentation B a k D R W)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hsmall : Cardinal.mk B.real < κ) :
    Cardinal.mk P.finite.codes < κ := P.finite.codes_small hκ hsmall

end IntegrationInACVF.Section7
