import Integration7.SelectedRVVFTailLifts
import Integration7.NativeVolumeDomains
import Integration7.NativeVolumeMapRealization
import Integration7.GammaMixedCoordinatePredicates

/-! Native presentations of selected-label VF tail lifts retain the
original Gamma base and require no additional real or Gamma names. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point VF RV carrier GammaSetDefinable gammaLogicInput setDefinable)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n a d : ℕ}

def nativeSelectedRVVFTailLift (hc : CanonicalStructure.IsCanonical (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) S n a) (ρ : Fin d → Fin a) :
    SpecialTransformations.Section5.DefSet (M := M) S (n+d) a :=
  nativeMixedVolumeDomain hc (selectedRVVFTailLift (rawSpecialSet hc A) ρ)

theorem native_selected_rv_vf_tail_lift_carrier
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) S n a) (ρ : Fin d → Fin a)
    (p : Point (M := M) (n+d) a) :
    p ∈ carrier (nativeSelectedRVVFTailLift hc A ρ) ↔
      (p.1 ∘ Fin.castAdd d,p.2) ∈ carrier A ∧
        SpecialTransformations.Section4.tupleRV (p.1 ∘ Fin.natAdd n) = p.2 ∘ ρ :=
  mem_selected_rv_vf_tail_lift (rawSpecialSet hc A) ρ p

theorem gamma_native_selected_rv_vf_tail_lift
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) S n a) (ρ : Fin d → Fin a)
    (hA : GammaSetDefinable G (carrier A)) :
    GammaSetDefinable G (carrier (nativeSelectedRVVFTailLift hc A ρ)) := by
  let R := nativeMixedVolumeDomain hc (selectedRVVFTailConstraint G.real n ρ)
  have hR : GammaSetDefinable G (carrier R) := (gammaLogicInput G).real_set _ (setDefinable R)
  have hP := gamma_mixed_coordinate_preimage hA (Fin.castAdd d) (id : Fin a → Fin a)
  convert (gammaLogicInput G).inter hP hR using 1
  ext p
  exact native_selected_rv_vf_tail_lift_carrier hc A ρ p

theorem native_selected_rv_vf_tail_lift_finite_labels
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) S n a) (ρ : Fin d → Fin a)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin d → RV (M := M)),
      {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (x : Fin (n+d) → VF (M := M)) :
    {r | (x,r) ∈ carrier (nativeSelectedRVVFTailLift hc A ρ)}.Finite :=
  selected_rv_vf_tail_lift_finite_labels (rawSpecialSet hc A) ρ hfin x

def nativeSelectedRVVFTailProjection
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) S n a) (ρ : Fin d → Fin a) :
    SpecialTransformations.Section5.Map (nativeSelectedRVVFTailLift hc A ρ) A :=
  nativeMixedVolumeMap hc (selectedRVVFTailProjection (rawSpecialSet hc A) ρ)

theorem native_selected_rv_vf_tail_projection_surjective
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) S n a) (ρ : Fin d → Fin a) :
    Function.Surjective (nativeSelectedRVVFTailProjection hc A ρ) :=
  selected_rv_vf_tail_projection_surjective (rawSpecialSet hc A) ρ

end IntegrationInACVF.Section7
