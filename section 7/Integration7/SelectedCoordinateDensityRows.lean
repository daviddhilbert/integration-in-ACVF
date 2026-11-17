module

public import Integration7.GammaSelectedVolumeSchemata
public import Integration7.GammaVolumeSliceAssemblyGeometry
public import Integration7.GammaGeometricCommonRowTransport
public import IntegrationSection6.GammaSelectedLabelFibrePresentations

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! An arbitrary finite presentation of a selected fibre, equipped with
its actual retained label density, realizes the full volume schema row. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Milestone0.sortEval
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p a k : ℕ}

theorem selected_fibre_retained_density_nonzero
    (U : DefSet (M := M) S p a) (ρ : Fin (k+1) → Fin a) (δ : Fin a)
    (hδ : ∀ q ∈ carrier U, (q.2 δ).val ≠ iRVZero)
    (x : Fin p → VF (M := M)) (P : SelectedLabelFibrePresentation B U ρ x) :
    ∀ u : P.domain, (u.val δ).val ≠ iRVZero :=
  fun u => hδ (x,u.val) (P.domain_eq.le u.property)

theorem selected_coordinate_density_schema_row
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : DefSet (M := M) S p a) (hU : GammaSetDefinable B (carrier U))
    (ρ : Fin (k+1) → Fin a) (δ : Fin a)
    (hδ : ∀ q ∈ carrier U, (q.2 δ).val ≠ iRVZero)
    (x : Fin p → VF (M := M)) (P : SelectedLabelFibrePresentation B U ρ x)
    (hP : P.codes ⊆ (C.base : Set M)) :
    RVVolumeSchemaRow
      (gammaCoordinateDensityObject (e := k) (k := 0) hc C P.toGamma hP δ
        (selected_fibre_retained_density_nonzero U ρ δ hδ x P))
      (gammaSelectedVolumeSchema U hU ρ δ) (fun j => (x j).val) := by
  constructor
  · intro r y
    have hV := gammaSelectedLabelSchema_volume U hU ρ x r y
    constructor
    · intro h
      have hr := hV.mp h
      obtain ⟨u,hu,hv⟩ := (P.graph_iff r y).mpr ⟨hr.1,hr⟩
      exact ⟨⟨u.val,u.property⟩,hu,hv⟩
    · rintro ⟨u,hu,hv⟩
      exact hV.mpr ((P.graph_iff r y).mp ⟨⟨u.val,u.property⟩,hu,hv⟩).2
  · intro r w
    have hD := gammaSelectedVolumeSchema_density U hU ρ δ hδ x r w
    constructor
    · intro h
      have hr := hD.mp h
      exact ⟨⟨r,P.domain_eq.ge hr.1⟩,rfl,hr.2⟩
    · rintro ⟨u,hu,hw⟩
      have hr : (x,r) ∈ carrier U := hu ▸ P.domain_eq.le u.property
      apply hD.mpr
      refine ⟨hr,?_⟩
      change (fun _ : Fin 1 => r δ) = w
      change (fun _ : Fin 1 => u.val δ) = w at hw
      rw [hu] at hw
      exact hw

end IntegrationInACVF.Section7
