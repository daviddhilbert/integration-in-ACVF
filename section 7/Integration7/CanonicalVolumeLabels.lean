import Integration7.VolumeRelabeling
import IntegrationSection6.CanonicalRVKeys
import IntegrationSection6.FiniteBlowups
import IntegrationSection6.KeyInverseCoordinates

/-! Canonical RV labels retain the complete positive volume tuple and
the old density. Their inverse is the actual old-label projection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def canonicalVolumeLabels (U : PositiveRVVolumeObject (M := M) S k) :
    PositiveRVVolumeObject (M := M) S k where
  underlying := ⟨Section6.canonicalRVKeyObject U.underlying.obj,
    (Section6.finite_volume_iso (Section6.canonicalRVKeyIso U.underlying.obj)).mp U.underlying.property⟩
  form := U.form.pullback (Section6.canonicalRVKeyIso U.underlying.obj).inv.map

def canonicalVolumeLabelsIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) : RVVolumeIso U (canonicalVolumeLabels U) := by
  let e : U.underlying ≅ (canonicalVolumeLabels U).underlying := rvFiniteIsoOfAmbient (Section6.canonicalRVKeyIso U.underlying.obj)
  apply RVVolumeIso.of_preserving_coordinates_full hc C e
  · exact Section6.canonicalRVKeyIso_volume U.underlying.obj
  · intro u
    change U.form.value ((Section6.canonicalRVKeyIso U.underlying.obj).inv.map
      ((Section6.canonicalRVKeyIso U.underlying.obj).hom.map u)) = U.form.value u
    rw [Section6.iso_hom_inv_apply]

theorem canonicalVolumeLabels_density_label (U : PositiveRVVolumeObject (M := M) S k)
    (δ : Fin U.underlying.obj.arity) (hDensity : ∀ u, U.form.value u = u.val δ)
    (v : (canonicalVolumeLabels U).underlying.obj.domain) :
    (canonicalVolumeLabels U).form.value v = v.val (Fin.natAdd (k+1) δ) :=
  (hDensity ((Section6.canonicalRVKeyIso U.underlying.obj).inv.map v)).trans
    (congrFun (Section6.canonicalRVKeyIso_inv_labels U.underlying.obj v) δ)

theorem canonicalVolumeLabels_coordinates (U : PositiveRVVolumeObject (M := M) S k)
    (v : (canonicalVolumeLabels U).underlying.obj.domain) :
    (canonicalVolumeLabels U).underlying.obj.value v = v.val ∘ Fin.castAdd U.underlying.obj.arity := rfl

end IntegrationInACVF.Section7
