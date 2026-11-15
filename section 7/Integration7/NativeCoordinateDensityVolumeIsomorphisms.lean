import Integration7.NativeCoordinateDensityVolumeObjects
import Integration7.NativeRawVolumeLabelMaps
import Section4.RVIsoTools

/-! Native bijections preserving the selected tuple and density produce
actual RV volume isomorphisms, with a proved generic RV Jacobian. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (RV carrier)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a b k : ℕ}

def nativeCoordinateDensityVolumeIso (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) {U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 a}
    {V : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 b}
    (ι : Fin (k+1) → Fin a) (κ : Fin (k+1) → Fin b) (δ : Fin a) (ε : Fin b)
    (hU : ∀ t : Fin (k+1) → RV (M := M),
      {r : Fin a → RV (M := M) | (Fin.elim0,r) ∈ carrier U ∧ r ∘ ι = t}.Finite)
    (hV : ∀ t : Fin (k+1) → RV (M := M),
      {r : Fin b → RV (M := M) | (Fin.elim0,r) ∈ carrier V ∧ r ∘ κ = t}.Finite)
    (hδ : ∀ p : U, (p.val.2 δ).val ≠ iRVZero) (hε : ∀ p : V, (p.val.2 ε).val ≠ iRVZero)
    (f : SpecialTransformations.Section5.Map U V) (hf : Function.Bijective f)
    (hcι : ∀ p, (f p).val.2 ∘ κ = p.val.2 ∘ ι)
    (hφε : ∀ p, (f p).val.2 ε = p.val.2 δ) :
    RVVolumeIso (nativeCoordinateDensityVolumeObject hc C U ι δ hU hδ)
      (nativeCoordinateDensityVolumeObject hc C V κ ε hV hε) := by
  let A := nativeCoordinateDensityVolumeObject hc C U ι δ hU hδ
  let B := nativeCoordinateDensityVolumeObject hc C V κ ε hV hε
  let g : Map A.underlying.obj.domain B.underlying.obj.domain := rawVolumeLabelMap hc f
  have hg : Function.Bijective g := raw_volume_label_map_bijective hc f hf
  have hcoord : ∀ u, B.underlying.obj.value (g u) = A.underlying.obj.value u := by
    intro u
    change (rawVolumeLabelMap hc f u).val ∘ κ = u.val ∘ ι
    rw [raw_volume_label_map_value]
    exact hcι _
  have hφ : ∀ u, B.form.value (g u) = A.form.value u := by
    intro u
    change (rawVolumeLabelMap hc f u).val ε = u.val δ
    rw [raw_volume_label_map_value]
    exact hφε _
  exact RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection g hg hcoord)) hcoord hφ

end IntegrationInACVF.Section7
