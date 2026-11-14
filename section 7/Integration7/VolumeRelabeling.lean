import Integration7.CoordinateRVJacobian
import Integration7.FiniteVolumeIsoMaps
import Section9.GenericRVJacobian

/-! Coordinate- and density-preserving bijections give genuine volume
isomorphisms. The generic Jacobian is obtained from the pinned predecessor
and identified with one, rather than assumed as an input. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def RVVolumeIso.of_preserving_coordinates
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (e : U.essential ≅ V.essential)
    (hcoord : ∀ u, V.essential.obj.value (finiteIsoMap e u) = U.essential.obj.value u)
    (hφ : ∀ u, V.essentialForm.value (finiteIsoMap e u) = U.essentialForm.value u) : RVVolumeIso U V where
  iso := e
  gamma u := by
    have hJ : rvGammaJacobian (U.essential.obj.value u)
        (V.essential.obj.value (finiteIsoMap e u))
        (U.essential_nonzero u) (V.essential_nonzero (finiteIsoMap e u)) = 1 := by
      simpa only [hcoord] using
        (rvGammaJacobian_self (U.essential.obj.value u) (U.essential_nonzero u))
    rw [hφ, hJ, Values.gamma_val_one, mul_one]
  rv := by
    obtain ⟨ω, D, hD, hd, hω⟩ := exists_definable_generic_RVJacobian hc C (Nat.zero_lt_succ k)
      e U.essential_nonzero V.essential_nonzero
    refine ⟨D, hD, hd, ?_⟩
    intro u hu
    have hj := hω u hu
    let R := (volumeCorrespondence (finiteIsoMap e)).carrier
    change IsRVJacobianAt R (U.essential.obj.value u)
      (V.essential.obj.value (finiteIsoMap e u)) ((ω u).val 0) at hj
    have hdiag : ∀ z ∈ R, ∀ i : Fin (k + 1),
        z (productLeft (k + 1) (k + 1) i) = z (productRight (k + 1) (k + 1) i) := by
      rintro z ⟨v, rfl⟩ i
      change productTuple (U.essential.obj.value v) (V.essential.obj.value (finiteIsoMap e v))
        (productLeft (k + 1) (k + 1) i) =
        productTuple (U.essential.obj.value v) (V.essential.obj.value (finiteIsoMap e v))
          (productRight (k + 1) (k + 1) i)
      rw [productTuple_left, productTuple_right, hcoord]
    have hj' : IsRVJacobianAt R (U.essential.obj.value u) (U.essential.obj.value u)
        ((ω u).val 0) := by
      simpa only [hcoord] using hj
    have h1 := rvJacobian_eq_one_of_diagonal R hdiag (U.essential.obj.value u) ((ω u).val 0) hj'
    have hratio : volumeRatio U V e u = 1 := by
      rw [volumeRatio, hφ, div_self (U.essentialForm_nonzero u)]
    rw [hratio]
    simpa only [h1] using hj

def RVVolumeIso.of_preserving_coordinates_full
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (e : U.underlying ≅ V.underlying)
    (hcoord : ∀ u, V.underlying.obj.value (finiteIsoMap e u) = U.underlying.obj.value u)
    (hφ : ∀ u, V.form.value (finiteIsoMap e u) = U.form.value u) : RVVolumeIso U V := by
  apply RVVolumeIso.of_preserving_coordinates hc C (rvFiniteEssentialIso e)
  · intro u
    exact hcoord ⟨u.val, rvEssentialLabels_subset U.underlying.obj u.property⟩
  · intro u
    exact hφ ⟨u.val, rvEssentialLabels_subset U.underlying.obj u.property⟩

def RVVolumeIso.refl (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) : RVVolumeIso U U :=
  RVVolumeIso.of_preserving_coordinates hc C (Iso.refl U.essential) (fun _ => rfl) (fun _ => rfl)

end IntegrationInACVF.Section7
