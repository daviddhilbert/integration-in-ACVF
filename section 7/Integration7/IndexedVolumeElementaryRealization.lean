import Integration7.IndexedVolumeElementaryValues
import Integration7.IndexedVolumeFiniteRowPresentations
import Integration7.GammaVolumeRelabelRealization

/-! Indexed assembly commutes with an actual elementary volume blowup,
retaining its pulled-back density and original-Gamma label graph. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

def GammaRVVolumeSchema.indexedElementaryPresentation
    (C : BaseContext M) (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (N : ℕ)
    (hF : ∀ t ∈ T, F.valid (rvValues t))
    (hAd : ∀ t ∈ T,
      (⟨F.object,Fin.last k,N⟩ : GammaFiniteAdmissibilitySchema B p a (k+1) (fun _ => .rv)).valid (rvValues t))
    (hB : B.real ⊆ (C.base : Set M)) : F.elementaryFormula.IndexedPresentation BP := by
  let A : GammaFiniteAdmissibilitySchema B p a (k+1) (fun _ => .rv) := ⟨F.object,Fin.last k,N⟩
  exact F.elementaryFormula.indexedVolumePresentation_finiteRows BP
    (fun t ht => A.elementary_finiteRow C.uncountable.le C.saturated C.model00
      ((Cardinal.mk_le_mk_of_subset hB).trans_lt C.small) _ (hAd t ht))
    (fun t ht => F.elementary_density_valid _ (hF t ht))

theorem GammaRVVolumeSchema.indexedElementaryRealize
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.valid (rvValues t))
    (hE : ∀ t ∈ T, F.elementaryFormula.object.finiteRow (rvValues t))
    (P : F.IndexedPresentation BP) (Q : F.elementaryFormula.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (hAd : BlowupAdmissible (P.inContext hc C hP).toObject) (hB : B.real ⊆ (C.base : Set M)) :
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      Nonempty (RVVolumeIso ((Q.inContext hc C hQ).toObject.extend hCD)
        ((elementaryVolumeObject C (P.inContext hc C hP).toObject hAd).extend hCD)) :=
  gammaVolumeRelabelRealize hc C (indexedVolumeElementaryEquiv hc C F BP P Q hP hQ hAd)
    (indexedVolumeElementaryEquiv_gammaGraph hc C F BP P Q hP hQ hAd)
    (fun u => (indexedVolumeElementaryEquiv_values hc C F BP hF hE P Q hP hQ hAd u).1)
    (fun u => (indexedVolumeElementaryEquiv_values hc C F BP hF hE P Q hP hQ hAd u).2) hB

end IntegrationInACVF.Section7
