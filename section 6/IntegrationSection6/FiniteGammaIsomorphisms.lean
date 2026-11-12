import IntegrationSection6.GammaFiniteElementary

/-! In RV[k], a Gamma-definable weight-preserving bijection has both
finite volume-image conditions automatically. This keeps the full original
Gamma graph while avoiding work on the abandoned larger categories. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {n : ℕ}

abbrev rawVolume (U : GammaRVFiniteObject B n) (u : rvObjectDomain U.object) : Fin n → M :=
  fun j => (gammaVolumeValue U.toGammaRVObject u j).val

theorem rawVolume_fibre_finite (U : GammaRVFiniteObject B n) (t : Fin n → M) :
    {u : rvObjectDomain U.object | rawVolume U u = t}.Finite := by
  by_cases ht : ∃ u : rvObjectDomain U.object, rawVolume U u = t
  · obtain ⟨a,ha⟩ := ht
    have h := U.finite_volume (rvObjectVolume U.object a)
    apply h.subset
    intro b hb
    apply Subtype.ext
    exact @rvValues_injective M (@CanonicalStructure.normalize M sM) n _ _ (hb.trans ha.symm)
  · exact Set.finite_empty.subset (fun u hu => False.elim (ht ⟨u,hu⟩))

def gammaIsoOfFiniteEquiv (U V : GammaRVFiniteObject B n)
    (e : rvObjectDomain U.object ≃ rvObjectDomain V.object)
    (he : GammaGraphDefinable B (gammaRVLabelGraph U.toGammaRVObject V.toGammaRVObject e))
    (hw : ∀ u, rawWeight (rawVolume U u) = rawWeight (rawVolume V (e u))) :
    GammaRVIso U.toGammaRVObject V.toGammaRVObject where
  equiv := e
  graph := he
  weight := hw
  leftFinite b := by
    have h := (rawVolume_fibre_finite V b).image (fun v => rawVolume U (e.symm v))
    apply h.subset
    rintro a ⟨u,hu⟩
    have ha : rawVolume U u = a := by
      funext j
      simpa only [productTuple_left] using congrFun hu (productLeft n n j)
    have hb : rawVolume V (e u) = b := by
      funext j
      simpa only [productTuple_right] using congrFun hu (productRight n n j)
    exact ⟨e u,hb,by simpa only [Equiv.symm_apply_apply] using ha⟩
  rightFinite a := by
    have h := (rawVolume_fibre_finite U a).image (fun u => rawVolume V (e u))
    apply h.subset
    rintro b ⟨u,hu⟩
    have ha : rawVolume U u = a := by
      funext j
      simpa only [productTuple_left] using congrFun hu (productLeft n n j)
    have hb : rawVolume V (e u) = b := by
      funext j
      simpa only [productTuple_right] using congrFun hu (productRight n n j)
    exact ⟨u,ha,hb⟩

end IntegrationInACVF.Section6.FiniteRV
