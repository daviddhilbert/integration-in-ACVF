module

public import Integration7.GammaRVLabelCuts
public import IntegrationSection5.RVProjectionNormalization
public import IntegrationSection5.StandardContractionLift

@[expose] public section

/-! Normalizing a pure-RV target commutes with cutting its retained
labels. The cut is read from the literal old-label suffix after the
volume tuple is prepended. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n l k : ℕ}
variable (Y : DefSet (M := M) S 0 l) (hY : GammaSetDefinable G (carrier Y))
variable (ρ : Fin k → Fin l) (R : Set (Point (M := M) 0 k)) (hR : GammaSetDefinable G R)
variable (hNames : commonRealNames G ⊆ S)

theorem raw_label_cut_image_mem (s : Fin l → RV (M := M)) :
    s ∈ carrier (Map.image (rawLabelMap (rvLabelCut Y hY ρ R hR hNames))) ↔
      s ∈ carrier (Map.image (rawLabelMap Y)) ∧ (Fin.elim0,s ∘ ρ) ∈ R := by
  constructor
  · rintro ⟨b,hb⟩
    have he : b.val.2 = s := hb
    have h := b.property.2
    change (Fin.elim0,b.val.2 ∘ ρ) ∈ R at h
    rw [he] at h
    exact ⟨⟨⟨b.val,b.property.1⟩,he⟩,h⟩
  · rintro ⟨⟨a,ha⟩,hs⟩
    have he : a.val.2 = s := ha
    refine ⟨⟨a.val,a.property,?_⟩,ha⟩
    change (Fin.elim0,a.val.2 ∘ ρ) ∈ R
    rw [he]
    exact hs

theorem first_volume_label_cut_mem (ν : Fin n → Fin l) (r : Fin (n+l) → RV (M := M)) :
    r ∈ carrier (rvObjectDomain (firstVolumeObject
      (Map.image (rawLabelMap (rvLabelCut Y hY ρ R hR hNames))) ν)) ↔
    r ∈ carrier (rvObjectDomain (firstVolumeObject (Map.image (rawLabelMap Y)) ν)) ∧
      (Fin.elim0,r ∘ (Fin.natAdd n ∘ ρ)) ∈ R := by
  have old_labels (u : Fin l → RV (M := M))
      (hu : u ∘ prependVolumeIndex ν = r) : r ∘ (Fin.natAdd n ∘ ρ) = u ∘ ρ := by
    funext i
    have h := congrFun hu (Fin.natAdd n (ρ i))
    change u (prependVolumeIndex ν (Fin.natAdd n (ρ i))) = r (Fin.natAdd n (ρ i)) at h
    rw [prependVolumeIndex,Fin.addCases_right] at h
    exact h.symm
  constructor
  · rintro ⟨u,hu⟩
    have hCut := (raw_label_cut_image_mem Y hY ρ R hR hNames u.val).mp u.property
    let v : Map.image (rawLabelMap Y) := ⟨u.val,hCut.1⟩
    have hValue : u.val ∘ prependVolumeIndex ν = r := hu
    refine ⟨⟨v,hu⟩,?_⟩
    exact Eq.mp (congrArg (fun s : Fin k → RV (M := M) => (Fin.elim0,s) ∈ R)
      (old_labels u.val hValue).symm) hCut.2
  · rintro ⟨⟨u,hu⟩,hCut⟩
    have hValue : u.val ∘ prependVolumeIndex ν = r := hu
    have hLabels := Eq.mp (congrArg (fun s : Fin k → RV (M := M) => (Fin.elim0,s) ∈ R)
      (old_labels u.val hValue)) hCut
    let v : Map.image (rawLabelMap (rvLabelCut Y hY ρ R hR hNames)) :=
      ⟨u.val,(raw_label_cut_image_mem Y hY ρ R hR hNames u.val).mpr ⟨u.property,hLabels⟩⟩
    exact ⟨v,hu⟩

end IntegrationInACVF.Section7
