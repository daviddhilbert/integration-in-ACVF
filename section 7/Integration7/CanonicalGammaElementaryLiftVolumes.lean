module

public import Integration7.LiteralElementaryFocusLiftVolumes
public import Integration7.CanonicalGammaElementaryObjects
public import IntegrationSection6.ElementaryLiftDiagram

@[expose] public section

/-! The checked generated-base focus construction supplies the actual
volume-preserving lift of a canonical elementary blowup. The RV density
is arbitrary and no lift or Jacobian premise is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

def canonicalGammaElementaryDensityObject
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : FiniteRV.GammaObjectAt B (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject (Fin.last k)) :
    PositiveRVVolumeObject (M := M) (C.base : Set M) k :=
  ⟨canonicalFiniteRVObject hc (FiniteRV.gammaElementaryAt C.uncountable.le C.saturated C.model00
    ((Cardinal.mk_le_mk_of_subset U.real_contains).trans_lt C.small) U (Fin.last k) hAd).object,
    ω.pullback (canonicalRawRVMap hc (@Section6.elementaryProjection M (@CanonicalStructure.normalize M sM)
      (@CanonicalStructure.normalized_model M sM hM) (C.base : Set M) (k+1) U.object.obj (Fin.last k)))⟩

theorem canonical_gamma_elementary_lift_volume_bijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGenerated : VFGammaGeneratedBase B)
    (U : FiniteRV.GammaObjectAt B (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject (Fin.last k)) :
    Nonempty (VFVolumeBijection
      (rvVolumeLift (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k))
      (rvVolumeLift (canonicalGammaElementaryDensityObject hc C U ω hAd))) := by
  obtain ⟨D⟩ := lemma_6_12 C.uncountable.le C.saturated C.model00
    ((Cardinal.mk_le_mk_of_subset U.real_contains).trans_lt C.small) hGenerated hAd
  let h := normalizedTypedLift_presents U.object.obj
  let hFull := D.full.ge
  refine ⟨⟨elementaryFocusFullLiftMap hc C h D.focus hFull D.admissible,?_,?_⟩⟩
  · exact elementary_focus_full_lift_map_bijective hc C h D.focus hFull D.admissible
      (typedLift_pullback U.object.obj)
  · exact elementary_focus_full_lift_preserves_volume hc C (Nat.zero_lt_succ k) h D.focus hFull
      D.admissible (typedLift_pullback U.object.obj) ω

end IntegrationInACVF.Section7
