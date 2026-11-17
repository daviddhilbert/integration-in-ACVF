module

public import Integration7.GammaSelectedRVVFTailMaps
public import IntegrationSection5.RelativeFibreMaps

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! An active-coordinate fibre of a selected VF realization is the
original coordinate fibre cut by one fixed selected RV tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a b d : ℕ}

theorem selected_vf_tail_insert_prefix (i : Fin n) (u : Fin (n+d) → VF (M := M))
    (p : Point (M := M) 1 a) :
    ((coordinateInsert (Fin.castAdd d i) u p).1 ∘ Fin.castAdd d,p.2) =
      coordinateInsert i (u ∘ Fin.castAdd d) p := by
  change (Function.update u (Fin.castAdd d i) (vfAt p 0) ∘ Fin.castAdd d,p.2) =
    (Function.update (u ∘ Fin.castAdd d) i (vfAt p 0),p.2)
  refine Prod.ext ?_ rfl
  funext j
  change Function.update u (Fin.castAdd d i) (vfAt p 0) (Fin.castAdd d j) =
    Function.update (u ∘ Fin.castAdd d) i (vfAt p 0) j
  by_cases hj : j = i
  · subst j
    rw [Function.update_self,Function.update_self]
  · rw [Function.update_of_ne (fun he => hj (Fin.castAdd_inj.mp he)),Function.update_of_ne hj]
    rfl

theorem selected_vf_tail_insert_tail (i : Fin n) (u : Fin (n+d) → VF (M := M))
    (p : Point (M := M) 1 a) :
    (coordinateInsert (Fin.castAdd d i) u p).1 ∘ Fin.natAdd n = u ∘ Fin.natAdd n := by
  funext j
  have hne : Fin.natAdd n j ≠ Fin.castAdd d i := by
    intro he
    have hv := congrArg Fin.val he
    have hi := i.isLt
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  exact Function.update_of_ne hne _ _

theorem selected_vf_tail_coordinate_fibre_base (i : Fin n) (u : Fin (n+d) → VF (M := M)) :
    coordinateFibreBase S i (u ∘ Fin.castAdd d) ⊆ coordinateFibreBase S (Fin.castAdd d i) u := by
  rintro z (hz | ⟨j,rfl⟩)
  · exact Or.inl hz
  · exact Or.inr ⟨⟨Fin.castAdd d j.val,fun he => j.property (Fin.castAdd_inj.mp he)⟩,rfl⟩

theorem selected_vf_tail_coordinate_fibre
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) S n a) (ρ : Fin d → Fin a)
    (i : Fin n) (u : Fin (n+d) → VF (M := M)) (p : Point (M := M) 1 a) :
    p ∈ carrier (coordinateFibre (nativeSelectedRVVFTailLift hc A ρ) (Fin.castAdd d i) u) ↔
      p ∈ carrier (coordinateFibre A i (u ∘ Fin.castAdd d)) ∧
        SpecialTransformations.Section4.tupleRV (u ∘ Fin.natAdd n) = p.2 ∘ ρ := by
  change coordinateInsert (Fin.castAdd d i) u p ∈ carrier (nativeSelectedRVVFTailLift hc A ρ) ↔ _
  rw [native_selected_rv_vf_tail_lift_carrier]
  change (((coordinateInsert (Fin.castAdd d i) u p).1 ∘ Fin.castAdd d,p.2) ∈ carrier A ∧
    SpecialTransformations.Section4.tupleRV ((coordinateInsert (Fin.castAdd d i) u p).1 ∘ Fin.natAdd n) = p.2 ∘ ρ) ↔ _
  rw [selected_vf_tail_insert_prefix,selected_vf_tail_insert_tail]
  rfl

theorem selected_vf_tail_coordinate_fibre_map
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (f : Map A B) (ρ : Fin d → Fin a) (σ : Fin d → Fin b)
    (hLabels : ∀ p : A, (f p).val.2 ∘ σ = p.val.2 ∘ ρ)
    (i : Fin n) (hi : UnaryRelative f i) (u : Fin (n+d) → VF (M := M))
    (p : coordinateFibre (nativeSelectedRVVFTailLift hc A ρ) (Fin.castAdd d i) u) :
    (coordinateFibreMap (nativeSelectedRVVFTailMap hc f ρ σ hLabels) (Fin.castAdd d i)
      (native_selected_rv_vf_tail_map_unary_relative hc f ρ σ hLabels i hi) u p).val =
      (coordinateFibreMap f i hi (u ∘ Fin.castAdd d)
        ⟨p.val,((selected_vf_tail_coordinate_fibre hc A ρ i u p.val).mp p.property).1⟩).val := by
  let q : nativeSelectedRVVFTailLift hc A ρ :=
    ⟨coordinateInsert (Fin.castAdd d i) u p.val,p.property⟩
  let r : A := ⟨coordinateInsert i (u ∘ Fin.castAdd d) p.val,
    ((selected_vf_tail_coordinate_fibre hc A ρ i u p.val).mp p.property).1⟩
  have hProj : nativeSelectedRVVFTailProjection hc A ρ q = r :=
    Subtype.ext (selected_vf_tail_insert_prefix i u p.val)
  have h := congrArg (fun t : B => coordinateProject i t.val)
    (native_selected_rv_vf_tail_map_projection hc f ρ σ hLabels q)
  rw [hProj] at h
  rw [coordinateFibreMap_apply,coordinateFibreMap_apply]
  exact h

end IntegrationInACVF.Section7
