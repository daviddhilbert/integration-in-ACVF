module

public import Integration7.PureVFCoordinateImages

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Coordinate images compose as the actual tuple projections do. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] {S : Set M} {a b c : ℕ}

theorem pure_vf_coordinate_image_id (X : DefSet (rawVFSpace (M := M) a) S) :
    pureVFCoordinateImage X id = X := by
  apply DefSet.eq_of_carrier_eq
  ext x
  rw [mem_pure_vf_coordinate_image]
  exact ⟨fun ⟨y,hy,he⟩ => he ▸ hy,fun hx => ⟨x,hx,rfl⟩⟩

theorem pure_vf_coordinate_image_comp (X : DefSet (rawVFSpace (M := M) a) S)
    (ρ : Fin b → Fin a) (τ : Fin c → Fin b) :
    pureVFCoordinateImage (pureVFCoordinateImage X ρ) τ = pureVFCoordinateImage X (ρ ∘ τ) := by
  apply DefSet.eq_of_carrier_eq
  ext z
  simp only [mem_pure_vf_coordinate_image]
  constructor
  · rintro ⟨y,⟨x,hx,rfl⟩,hz⟩
    exact ⟨x,hx,hz⟩
  · rintro ⟨x,hx,hz⟩
    exact ⟨x ∘ ρ,⟨x,hx,rfl⟩,hz⟩

theorem pure_vf_coordinate_image_mono (X Y : DefSet (rawVFSpace (M := M) a) S)
    (h : X.carrier ⊆ Y.carrier) (ρ : Fin b → Fin a) :
    (pureVFCoordinateImage X ρ).carrier ⊆ (pureVFCoordinateImage Y ρ).carrier := by
  intro z hz
  obtain ⟨x,hx,rfl⟩ := (mem_pure_vf_coordinate_image X ρ z).mp hz
  exact (mem_pure_vf_coordinate_image Y ρ (x ∘ ρ)).mpr ⟨x,h hx,rfl⟩
end IntegrationInACVF.Section7
