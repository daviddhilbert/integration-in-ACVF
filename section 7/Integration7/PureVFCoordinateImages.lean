import Section4.CoordinateMaps
import Section4.Products

/-! Actual definable images of pure VF coordinate projections, over the
unchanged real parameter set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] {S : Set M} {a b : ℕ}

def pureVFCoordinateSelectMap (S : Set M) (ρ : Fin b → Fin a) :
    Map (DefSet.univ (rawVFSpace (M := M) a) S) (DefSet.univ (rawVFSpace (M := M) b) S) := by
  letI : Nonempty (rawRVSpace (M := M) 0).Carrier := ⟨fun i => Fin.elim0 i⟩
  letI : Subsingleton (rawRVSpace (M := M) 0).Carrier := ⟨fun f g => funext (fun i => Fin.elim0 i)⟩
  let X := DefSet.univ (rawVFSpace (M := M) a) S
  let R := DefSet.univ (rawRVSpace (M := M) 0) S
  let f := (Map.id X).pair (Map.toSubsingleton X (rawRVSpace (M := M) 0))
  let g := vfSelect (r := 0) ρ (X.prod R)
  exact (Map.fst (rawVFSpace (M := M) b) (rawRVSpace 0) S
    (DefSet.univ (rawMixedSpace (M := M) b 0) S)).comp (g.comp f)

theorem pure_vf_coordinate_select_value (ρ : Fin b → Fin a)
    (q : DefSet.univ (rawVFSpace (M := M) a) S) : (pureVFCoordinateSelectMap S ρ q).val=q.val ∘ ρ := rfl

def pureVFCoordinateImage (X : DefSet (rawVFSpace (M := M) a) S) (ρ : Fin b → Fin a) :
    DefSet (rawVFSpace (M := M) b) S := ((pureVFCoordinateSelectMap S ρ).restrict (Set.subset_univ X.carrier)).image

theorem mem_pure_vf_coordinate_image (X : DefSet (rawVFSpace (M := M) a) S) (ρ : Fin b → Fin a)
    (y : (rawVFSpace (M := M) b).Carrier) :
    y ∈ (pureVFCoordinateImage X ρ).carrier ↔ ∃ x ∈ X.carrier, x ∘ ρ=y := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨x.val,x.property,hx⟩
  · rintro ⟨x,hx,he⟩
    exact ⟨⟨x,hx⟩,he⟩
end IntegrationInACVF.Section7
