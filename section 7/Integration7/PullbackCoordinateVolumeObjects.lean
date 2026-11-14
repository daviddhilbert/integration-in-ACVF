import Integration7.CanonicalFiniteRVObjects
import Integration7.RVNonzero
import Integration7.CoordinateDensityVolumeObjects
import IntegrationSection6.OriginalFocusObjects

/-! The canonical key object of an actual RV pullback carries any
retained nonzero density label, with its original value unchanged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5 (rvObjectVolume pullbackObject carrier rawKeyMap_apply)
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k a : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem pullbackKey_density_nonzero
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) S (k+1) a)
    (hFinite : @Map.FiniteFibres LRV M N _ _ S _ _ (rvObjectVolume (pullbackObject A)))
    (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero)
    (u : (canonicalFiniteRVObject hc ⟨pullbackObject A,hFinite⟩).obj.domain) :
    u.val (Fin.natAdd (k+1) δ) ≠ 0 := by
  obtain ⟨p,hp⟩ := u.property
  have he := hp
  change (SpecialTransformations.Section5.rawKeyMap A p).val = u.val at he
  rw [rawKeyMap_apply] at he
  have hi := congrFun he (Fin.natAdd (k+1) δ)
  have hv : p.val.2 δ = u.val (Fin.natAdd (k+1) δ) := (Fin.append_right _ _ δ).symm.trans hi
  exact (rv_nonzero_iff_raw _).mpr (fun hz => hδ p ((congrArg Subtype.val hv).trans hz))

def pullbackCoordinateVolumeObject
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) S (k+1) a)
    (hFinite : @Map.FiniteFibres LRV M N _ _ S _ _ (rvObjectVolume (pullbackObject A)))
    (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) : PositiveRVVolumeObject (M := M) S k :=
  coordinateDensityVolumeObject (canonicalFiniteRVObject hc ⟨pullbackObject A,hFinite⟩)
    (Fin.natAdd (k+1) δ) (pullbackKey_density_nonzero hc A hFinite δ hδ)

theorem pullbackCoordinateVolumeObject_density
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) S (k+1) a)
    (hFinite : @Map.FiniteFibres LRV M N _ _ S _ _ (rvObjectVolume (pullbackObject A)))
    (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero)
    (u : (pullbackCoordinateVolumeObject hc A hFinite δ hδ).underlying.obj.domain) :
    (pullbackCoordinateVolumeObject hc A hFinite δ hδ).form.value u = u.val (Fin.natAdd (k+1) δ) := rfl

end IntegrationInACVF.Section7
