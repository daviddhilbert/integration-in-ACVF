module

public import Integration7.NativeCoordinateVolumeFamilyRows

@[expose] public section

/-! A literal native coordinate-density family represents any actual
family with the same carrier, selected tuple and retained density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5 (VF RV carrier)
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k : ℕ}

def nativeCoordinateFamilyRowIso
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : SelectedVFVolumeFamily C n a k)
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n a)
    (ρ : Fin (k+1) → Fin a)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (hDomain : F.domain.carrier = carrier A) (hSelected : F.selected=ρ)
    (hDensity : ∀ q : F.domain, F.form.value q = q.val.2 δ)
    (x : Fin n → VF (M := M)) :
    RVVolumeIso ((nativeCoordinateVolumeFamily hc A ρ hfin δ hδ).rowInContext x) (F.rowInContext x) := by
  let U := (nativeCoordinateVolumeFamily hc A ρ hfin δ hδ).rowInContext x
  let V := F.rowInContext x
  let f : Map U.underlying.obj.domain V.underlying.obj.domain :=
    Map.inclusion (fun r hr => (Set.ext_iff.mp hDomain (x,r)).mpr hr)
  have hf : Function.Bijective f := by
    constructor
    · intro u v h
      have he := congrArg Subtype.val h
      exact Subtype.ext he
    · intro v
      exact ⟨⟨v.val,(Set.ext_iff.mp hDomain (x,v.val)).mp v.property⟩,rfl⟩
  have hCoord : ∀ u, V.underlying.obj.value (f u) = U.underlying.obj.value u := by
    intro u
    change u.val ∘ F.selected = u.val ∘ ρ
    rw [hSelected]
  have hForm : ∀ u, V.form.value (f u) = U.form.value u := fun u => hDensity ⟨(x,u.val),(f u).property⟩
  exact RVVolumeIso.of_preserving_coordinates_full hc (vfParameterVolumeContext C x)
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf hCoord)) hCoord hForm

end IntegrationInACVF.Section7
