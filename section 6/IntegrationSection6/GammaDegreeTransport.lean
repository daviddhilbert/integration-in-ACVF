import IntegrationSection6.FiniteGammaIsoRealization

/-! Transport actual finite objects and common blowups across an equality
of their natural-number degrees. This changes no mathematical data. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k l : ℕ}

def gammaCastDegree (h : k = l) (U : GammaRVFiniteObject B k) : GammaRVFiniteObject B l := h ▸ U

theorem gammaCastDegree_symm (h : k = l) (U : GammaRVFiniteObject B l) :
    gammaCastDegree h (gammaCastDegree h.symm U) = U := by
  cases h
  rfl

theorem FiniteRV.GammaIsp.castDegree {κ : Cardinal}
    {hκ : Cardinal.aleph0 ≤ κ} {hs : Saturated M κ} {h00 : M ⊨ Axioms.ACVF00}
    {hreal : Cardinal.mk B.real < κ} {U V : GammaRVFiniteObject B k}
    (H : FiniteRV.GammaIsp hκ hs h00 hreal U V) (h : k = l) :
    FiniteRV.GammaIsp hκ hs h00 hreal (gammaCastDegree h U) (gammaCastDegree h V) := by
  cases h
  exact H

def gammaIsoOfEqualDegreeEquiv (h : k = l) (U : GammaRVFiniteObject B k) (V : GammaRVFiniteObject B l)
    (e : rvObjectDomain U.object ≃ rvObjectDomain V.object)
    (hGraph : GammaGraphDefinable B (fun (p : Point (M := M) 0 (rvObjectArity U.object))
      (q : Point (M := M) 0 (rvObjectArity V.object)) => ∃ u : rvObjectDomain U.object, u.val = p.2 ∧ (e u).val = q.2))
    (hWeight : ∀ u, rawWeight (fun j => (gammaVolumeValue U.toGammaRVObject u j).val) =
      rawWeight (fun j => (gammaVolumeValue V.toGammaRVObject (e u) j).val)) :
    GammaRVIso U.toGammaRVObject (gammaCastDegree h.symm V).toGammaRVObject := by
  cases h
  exact FiniteRV.gammaIsoOfFiniteEquiv U V e hGraph hWeight

end IntegrationInACVF.Section6
