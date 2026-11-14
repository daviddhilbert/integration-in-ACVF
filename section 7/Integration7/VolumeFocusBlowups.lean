import Integration7.ElementaryBlowupConstruction
import IntegrationSection6.FiniteBlowups
import IntegrationSection6.KeyInverseCoordinates

/-! A full admissible focus gives an actual elementary volume blowup.
Its form is the unchanged density pulled back along the old-label map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5 (Focus carrier)
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}
variable (C : BaseContext M) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
variable {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) U.underlying.obj.arity}
variable (h : Section6.PresentsLift U.underlying.obj A) {j : Fin U.underlying.obj.arity}
variable (D : Focus A (Fin.last k) j) (hfull : carrier A ⊆ D.locus) (hAd : BlowupAdmissible U)

def fullFocusVolumeObject : PositiveRVVolumeObject (M := M) (C.base : Set M) k := by
  let E := Section6.admissibleFullFocusBlowup h D hfull hAd.toOrdinary
  refine { underlying := ⟨Section6.fullFocusObject h D hfull hAd.toOrdinary.rv_nonzero,?_⟩
           form := U.form.pullback ((Section6.elementaryProjection U.underlying.obj (Fin.last k)).comp E.iso.hom.map) }
  exact (Section6.finite_volume_iso E.iso).mpr
    (Section6.elementary_finite_volume C.uncountable.le C.saturated C.small U.underlying.obj
      (Fin.last k) hAd.toOrdinary U.underlying.property)

def fullFocusVolumeBlowup : ElementaryBlowup U (fullFocusVolumeObject C U h D hfull hAd) := by
  let E := Section6.admissibleFullFocusBlowup h D hfull hAd.toOrdinary
  refine { admissible := hAd
           chartMap := (rvUnpack U.underlying.obj.domain (blowupConeSet (C.base : Set M))).comp E.iso.hom.map
           chartMap_bijective := (rvUnpack_bijective _ _).comp (Section6.iso_map_bijective E.iso)
           head := ?_, last := ?_, volume := fun _ => rfl }
  · intro w i
    exact (congrFun (Section6.admissibleFullFocusBlowup_volume h D hfull hAd.toOrdinary w).symm i.castSucc).trans
      (Section6.blowupValue_other _ _ _ _ (Fin.castSucc_ne_last i))
  · intro w
    exact (congrFun (Section6.admissibleFullFocusBlowup_volume h D hfull hAd.toOrdinary w).symm (Fin.last k)).trans
      (Section6.blowupValue_same _ _ _)

theorem fullFocusVolumeBlowup_old_labels
    (w : (fullFocusVolumeObject C U h D hfull hAd).underlying.obj.domain) :
    ((fullFocusVolumeBlowup C U h D hfull hAd).projection w).val =
      w.val ∘ Fin.natAdd (k+1) := by
  let E := Section6.admissibleFullFocusBlowup h D hfull hAd.toOrdinary
  have hk := Section6.elementaryKeyIso_inv_key U.underlying.obj (Fin.last k) hAd.toOrdinary
    ((Section6.fullFocusObjectKeyIso h D hfull hAd.toOrdinary.rv_nonzero).hom.map w)
  funext i
  exact (Fin.append_right _ _ i).symm.trans (congrFun hk (Fin.natAdd (k+1) i))

theorem fullFocusVolumeObject_density_label (δ : Fin U.underlying.obj.arity)
    (hDensity : ∀ u, U.form.value u = u.val δ)
    (w : (fullFocusVolumeObject C U h D hfull hAd).underlying.obj.domain) :
    (fullFocusVolumeObject C U h D hfull hAd).form.value w = w.val (Fin.natAdd (k+1) δ) := by
  exact (hDensity ((fullFocusVolumeBlowup C U h D hfull hAd).projection w)).trans
    (congrFun (fullFocusVolumeBlowup_old_labels C U h D hfull hAd w) δ)

end IntegrationInACVF.Section7
