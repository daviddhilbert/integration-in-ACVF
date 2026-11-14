import Integration7.GammaCoordinateDensityGraphs
import Integration7.ActualVolumeAdmissibilityPromotion

/-! Original-Gamma admissibility of a native object transfers to any
schema presentation of its canonical volume object. Enlarged real contexts
do not enter the algebraicity base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section7 (gammaVolumeValue)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p k : ℕ} {sp : Fin p → SortTag}

theorem canonical_gamma_admissible_schema_row
    (hc : CanonicalStructure.IsCanonical (M := M))
    (z : Fin p → M)
    (U : FiniteRV.GammaObjectAt ⟨B.real ∪ Set.range z,B.gamma⟩ S (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    (F : GammaRVVolumeSchema B p (canonicalFiniteRVObject hc U.object).obj.arity k sp)
    (PU : RVVolumeSchemaRow
      (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) S k) F z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩
      (canonicalFiniteRVObject hc U.object).obj.arity (k+1)
      (F.object.rowDomain z) (F.object.rowVolume z))
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject (Fin.last k)) :
    GammaAdmissible P.toGamma.toGammaRVObject (Fin.last k) := by
  constructor
  · intro u
    let t := gammaVolumeValue P.toGamma.toGammaRVObject u
    have ht := ((P.graph_iff u.val t).mp ⟨u,rfl,rfl⟩).2
    obtain ⟨v,_,hv⟩ := (PU.volume_iff _ _).mp ht
    change (t (Fin.last k)).val ≠ iRVZero
    rw [← hv]
    exact hAd.nonzero ⟨v.val,v.property⟩
  · intro u
    let t := gammaVolumeValue P.toGamma.toGammaRVObject u
    have ht := ((P.graph_iff u.val t).mp ⟨u,rfl,rfl⟩).2
    obtain ⟨v,_,hv⟩ := (PU.volume_iff _ _).mp ht
    change AlgebraicAtBase
      ⟨coordinateBase (B.real ∪ Set.range z) (Fin.last k) t,B.gamma⟩ .rv (t (Fin.last k)).val
    rw [← hv]
    exact hAd.algebraic ⟨v.val,v.property⟩

end IntegrationInACVF.Section7
