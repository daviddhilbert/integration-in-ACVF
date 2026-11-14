import Integration7.IndexedVolumeAdmissibility
import Integration7.IndexedEssentialVolumeDomains
import Integration7.GammaVolumeElementaryFormulas
import Integration7.NormalizedElementaryCoordinates
import IntegrationSection6.IndexedElementaryLabels
import Integration7.GammaVolumeIndexedCharts

/-! Reassociation of an index, old labels and blowup parameter gives
the actual elementary domain, with its full original-Gamma graph. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV Point GammaGraphDefinable gammaLogicInput rvCoordinatePointMap)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem indexedVolume_elementary_domain
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (P : F.IndexedPresentation BP) (Q : F.elementaryFormula.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (hAd : BlowupAdmissible (P.inContext hc C hP).toObject)
    (w : Fin (p+(a+1)) → RV (M := M)) :
    w ∈ (Q.inContext hc C hQ).underlying.obj.domain.carrier ↔
      indexedElementaryLabels w ∈
        (elementaryVolumeObject C (P.inContext hc C hP).toObject hAd).underlying.obj.domain.carrier := by
  have hS := Set.ext_iff.mp (GammaVolumeGraphPresentation.inContext_domain hc C Q hQ) w
  have hRow := F.object.elementary_row_domain_formula (Fin.last k) (rvValues (indexedLeft w))
    (fun i => (indexedLeft w i).property) (indexedRight w) (C.base : Set M)
  have hHead := indexedVolume_domain_iff hc C P hP
    (Fin.append (indexedLeft w) (indexedRight w ∘ Fin.castAdd 1))
  simp only [indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right] at hHead
  have hTarget := Section6.elementary_domain_formula (P.inContext hc C hP).underlying.obj
    (Fin.last (d+k)) (indexedElementaryLabels w)
  change (indexedElementaryLabels w ∈
    (elementaryVolumeObject C (P.inContext hc C hP).toObject hAd).underlying.obj.domain.carrier) ↔
    ((indexedElementaryLabels w ∘ Fin.castAdd 1) ∈ (P.inContext hc C hP).underlying.obj.domain.carrier ∧
      (indexedElementaryLabels w ∘ Fin.natAdd (p+a)) ∈ (Section6.positiveRV (C.base : Set M)).carrier) at hTarget
  rw [indexedElementaryLabels_head,indexedElementaryLabels_parameter] at hTarget
  have hCone := positiveRV_normalize (C.base : Set M) (indexedRight w ∘ Fin.natAdd a)
  exact hS.trans ((and_congr Iff.rfl hRow).trans
    (and_assoc.symm.trans ((and_congr hHead.symm hCone).trans hTarget.symm)))

def indexedVolumeElementaryEquiv
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (P : F.IndexedPresentation BP) (Q : F.elementaryFormula.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (hAd : BlowupAdmissible (P.inContext hc C hP).toObject) :
    (Q.inContext hc C hQ).underlying.obj.domain ≃
      (elementaryVolumeObject C (P.inContext hc C hP).toObject hAd).underlying.obj.domain where
  toFun u := ⟨indexedElementaryLabels u.val,
    (indexedVolume_elementary_domain hc C F BP P Q hP hQ hAd u.val).mp u.property⟩
  invFun v := ⟨(indexedElementaryTupleEquiv (RV (M := M)) p a).symm v.val,by
    apply (indexedVolume_elementary_domain hc C F BP P Q hP hQ hAd _).mpr
    exact ((indexedElementaryTupleEquiv (RV (M := M)) p a).apply_symm_apply v.val).symm ▸ v.property⟩
  left_inv u := Subtype.ext ((indexedElementaryTupleEquiv (RV (M := M)) p a).symm_apply_apply u.val)
  right_inv v := Subtype.ext ((indexedElementaryTupleEquiv (RV (M := M)) p a).apply_symm_apply v.val)

theorem indexedVolumeElementaryEquiv_gammaGraph
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (P : F.IndexedPresentation BP) (Q : F.elementaryFormula.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (hAd : BlowupAdmissible (P.inContext hc C hP).toObject) :
    GammaGraphDefinable B (fun (w : Point (M := M) 0 (p+(a+1))) (y : Point (M := M) 0 ((p+a)+1)) =>
      ∃ u : (Q.inContext hc C hQ).underlying.obj.domain, u.val = w.2 ∧
        (indexedVolumeElementaryEquiv hc C F BP P Q hP hQ hAd u).val = y.2) := by
  let f := rvCoordinatePointMap (indexedElementaryCoordinates p a) B.real
  have h := (gammaLogicInput B).restrict_graph Q.finite.domain_graph (gamma_global_map_graph f)
  apply GammaGraphDefinable.congr h
  intro w y
  change (w.2 ∈ indexedDomain T (fun t => F.elementaryFormula.object.rowDomain (rvValues t)) ∧
    (Fin.elim0,indexedElementaryLabels w.2) = y) ↔ _
  constructor
  · rintro ⟨hw,hy⟩
    cases hy
    exact ⟨⟨w.2,(Set.ext_iff.mp (GammaVolumeGraphPresentation.inContext_domain hc C Q hQ) _).mpr hw⟩,
      rfl,rfl⟩
  · rintro ⟨u,hu,hy⟩
    exact ⟨hu ▸ (Set.ext_iff.mp (GammaVolumeGraphPresentation.inContext_domain hc C Q hQ) _).mp u.property,
      Prod.ext (Subsingleton.elim _ _) (by change indexedElementaryLabels w.2 = y.2; exact hu ▸ hy)⟩

end IntegrationInACVF.Section7
