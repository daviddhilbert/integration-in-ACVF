module

public import Integration7.VolumeFamilyHeadIntegrals
public import Integration7.GeometricVolumeCommonOnObjects
public import Integration7.CommonContextVolumeDescent

@[expose] public section

/-! Full coordinate-and-density row semantics for literal native
families. Original-Gamma geometric comparisons descend to their genuine
finite VF parameter contexts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {C : BaseContext M} {B : Base (M := M)} {n a b k : ℕ}

theorem vf_parameter_volume_context_contains_common_names
    (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (x : Fin n → VF (M := M)) :
    commonRealNames (⟨(C.base : Set M) ∪ Set.range (fun j => (x j).val),Ξ⟩ : Base (M := M)) ⊆
      ((vfParameterVolumeContext C x).base : Set M) := by
  rintro y (hy | hy)
  · exact vfParameterVolumeContext_contains C x hy
  · exact vfParameterVolumeContext_contains C x (Or.inl (hNames (Or.inr hy)))

theorem SelectedVFVolumeFamily.rowInContext_gamma
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (F : SelectedVFVolumeFamily C n a k)
    (x : Fin n → VF (M := M)) :
    VolumeObjectGamma (F.rowInContext x)
      (⟨(C.base : Set M) ∪ Set.range (fun j => (x j).val),Ξ⟩ : Base (M := M)) :=
  .of_term_context hc (vfParameterVolumeContext C x) rfl _

theorem native_coordinate_volume_family_schema_row
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) (C.base : Set M) n a) (hA : GammaSetDefinable B (carrier A))
    (ρ : Fin (k+1) → Fin a)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (x : Fin n → VF (M := M)) :
    RVVolumeSchemaRow ((nativeCoordinateVolumeFamily hc A ρ hfin δ hδ).rowInContext x)
      (gammaSelectedVolumeSchema A hA ρ δ) (fun j => (x j).val) := by
  constructor
  · intro r t
    change (gammaSelectedLabelSchema A hA ρ).rowVolume _ r t ↔ _
    rw [gammaSelectedLabelSchema_volume]
    exact ⟨fun h => ⟨⟨r,h.1⟩,rfl,h.2⟩,by rintro ⟨u,rfl,rfl⟩; exact ⟨u.property,rfl⟩⟩
  · intro r y
    rw [gammaSelectedVolumeSchema_density A hA ρ δ hδ]
    constructor
    · rintro ⟨hr,hy⟩
      exact ⟨⟨r,hr⟩,rfl,hy⟩
    · rintro ⟨u,rfl,rfl⟩
      exact ⟨u.property,rfl⟩

theorem volume_family_geometric_rows_descend
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (L : GammaRVVolumeSchema (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) n a k (fun _ => .vf))
    (R : GammaRVVolumeSchema (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) n b k (fun _ => .vf))
    (x : Fin n → VF (M := M))
    (PL : RVVolumeSchemaRow (F.rowInContext x) L (fun j => (x j).val))
    (PR : RVVolumeSchemaRow (G.rowInContext x) R (fun j => (x j).val))
    (h : L.commonByGammaGeometry R (fun j => (x j).val)) :
    VolumeBlowupEquivalent (F.rowInContext x) (G.rowInContext x) := by
  let D := vfParameterVolumeContext C x
  let Bx : Base (M := M) := ⟨(C.base : Set M) ∪ Set.range (fun j => (x j).val),Ξ⟩
  let hF := F.rowInContext_gamma hc Ξ x
  let hG := G.rowInContext_gamma hc Ξ x
  obtain ⟨E,hDE,hCommon⟩ := GammaRVVolumeSchema.commonByGammaGeometry_on_objects hc D
    (F.rowInContext x) (G.rowInContext x) L R _ PL PR hF hG
    (vfParameterVolumeContext_contains C x) h
  have hContext : CommonContextVolumeEquivalent Bx D
      ⟨F.rowInContext x,hF⟩ ⟨G.rowInContext x,hG⟩ := ⟨E,hDE,hCommon⟩
  exact (hContext.descend hc D (vf_parameter_volume_context_contains_common_names Ξ hNames x)).toOrdinary hc D Bx

end IntegrationInACVF.Section7
