module

public import Integration7.GammaVolumeObjectGraphs
public import Integration7.GammaVolumePresentationContexts
public import Integration7.GammaVolumeRestrictionIdentities

@[expose] public section

/-! A full Gamma volume presentation in any containing context has
its original coordinate and density graphs in the actual volume category.
Changing the internal presentation retains its Gamma label identity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (RV Point GammaGraphDefinable)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a k : ℕ}
variable {D : Set (Fin a → RV (M := M))}
variable {R : (Fin a → RV (M := M)) → (Fin (k+1) → RV (M := M)) → Prop}
variable {W : (Fin a → RV (M := M)) → (Fin 1 → RV (M := M)) → Prop}

theorem GammaVolumeGraphPresentation.gamma_object
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : GammaVolumeGraphPresentation B a (k+1) D R W) (hP : P.finite.codes ⊆ (C.base : Set M)) :
    VolumeObjectGamma (P.inContext hc C hP).toObject B := by
  constructor
  · apply GammaGraphDefinable.congr P.finite.volume_graph
    intro p q
    constructor
    · rintro ⟨u,hu,hv⟩
      exact ⟨⟨u.val,u.property⟩,hu,hv⟩
    · rintro ⟨u,hu,hv⟩
      exact ⟨⟨u.val,u.property⟩,hu,hv⟩
  · apply GammaGraphDefinable.congr P.density_graph
    intro p q
    exact (P.canonicalData_density_iff hc p.2 q.2).symm

theorem gamma_volume_presentation_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P Q : GammaVolumeGraphPresentation B a (k+1) D R W)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M)) :
    (gammaVolumePresentationIso hc C P Q hP hQ).GammaDefinable B :=
  gamma_volume_iso_of_label_identity hc _ (P.gamma_object hc C hP) rfl (fun _ => rfl)

end IntegrationInACVF.Section7
