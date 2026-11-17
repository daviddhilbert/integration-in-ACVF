module

public import Integration7.CanonicalGammaVolumeIsomorphisms
public import Integration7.CanonicalLiftVolumePresentations
public import Integration7.NormalizedElementaryGeometry
public import IntegrationSection6.FiniteGammaElementaryAt

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Original-Gamma admissibility supplies the actual canonical volume
blowup. Its underlying object is the canonical native elementary object. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem canonicalGammaElementaryAdmissible
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : FiniteRV.GammaObjectAt B (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject (Fin.last k)) :
    BlowupAdmissible
      (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :=
  canonicalRVObject_blowupAdmissible hc U.object
    (hAd.ordinary C.uncountable.le C.saturated C.model00
      ((Cardinal.mk_le_mk_of_subset U.real_contains).trans_lt C.small)) ω

theorem canonical_gamma_elementary_domain
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : FiniteRV.GammaObjectAt B (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject (Fin.last k)) :
    (canonicalFiniteRVObject hc
      (FiniteRV.gammaElementaryAt C.uncountable.le C.saturated C.model00
        ((Cardinal.mk_le_mk_of_subset U.real_contains).trans_lt C.small) U (Fin.last k) hAd).object).obj.domain.carrier =
      (elementaryVolumeObject C
        (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
        (canonicalGammaElementaryAdmissible hc C U ω hAd)).underlying.obj.domain.carrier := by
  have hCone : (canonicalRawRVDomain hc (@Section6.positiveRV M N (C.base : Set M))).carrier =
      (Section6.positiveRV (M := M) (C.base : Set M)).carrier := by
    ext t
    change (¬ @iLe M N (t 0).val (@iRVOne M N)) ↔ ¬ @iLe M sM (t 0).val (@iRVOne M sM)
    rw [SpecialTransformations.Section8.normalize_eq_of_isCanonical hc]
  ext w
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨⟨p.val,⟨p.property.1,(Set.ext_iff.mp hCone _).mp p.property.2⟩⟩,hp⟩
  · rintro ⟨p,hp⟩
    exact ⟨⟨p.val,⟨p.property.1,(Set.ext_iff.mp hCone _).mpr p.property.2⟩⟩,hp⟩

theorem canonical_gamma_elementary_object
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : FiniteRV.GammaObjectAt B (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject (Fin.last k)) :
    canonicalFiniteRVObject hc
      (FiniteRV.gammaElementaryAt C.uncountable.le C.saturated C.model00
        ((Cardinal.mk_le_mk_of_subset U.real_contains).trans_lt C.small) U (Fin.last k) hAd).object =
      (elementaryVolumeObject C
        (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
        (canonicalGammaElementaryAdmissible hc C U ω hAd)).underlying := by
  apply CategoryTheory.ObjectProperty.FullSubcategory.ext
  change canonicalRVObject hc (@Section6.elementary M N hN (C.base : Set M) (k+1)
    U.object.obj (Fin.last k)) =
      Section6.elementary (canonicalRVObject hc U.object.obj) (Fin.last k)
  exact rvObject_eq_of_carrier_coordinates _ _ _ _
    (canonical_elementary_domain hc U.object.obj (Fin.last k))
    (canonical_elementary_coordinates hc U.object.obj (Fin.last k))

end IntegrationInACVF.Section7
