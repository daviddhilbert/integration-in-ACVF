module

public import Integration7.GammaVolumeSliceDensityAssembly
public import Integration7.VolumeSchemaDomainSemantics
public import Integration7.VolumeChainSchemaRealization

@[expose] public section

/-! A label-density schema row is realized by the actual retained-label
volume form on every containing real presentation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a : ℕ} {sp : Fin p → SortTag}

theorem gamma_label_density_coordinate_row
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaRVVolumeSchema B p a 0 sp) (z : Fin p → M) (hF : F.valid z)
    (P : GammaVolumeGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a 1
      (F.object.rowDomain z) (F.object.rowVolume z) (F.rowDensity z))
    (hP : P.finite.codes ⊆ (C.base : Set M)) (δ : Fin a)
    (hRow : ∀ x w, F.rowDensity z x w ↔ x ∈ F.object.rowDomain z ∧ w 0 = x δ)
    (hNZ : ∀ u : P.finite.domain, (u.val δ).val ≠ iRVZero) :
    RVVolumeSchemaRow (gammaCoordinateDensityObject (e := 0) (k := 0) hc C P.finite.toGamma hP δ hNZ) F z := by
  have PS := P.inContext_schemaRow hc C F z hF hP
  constructor
  · exact PS.volume_iff
  · intro x w
    rw [hRow]
    constructor
    · rintro ⟨hx,hw⟩
      have hp := (PS.domain_iff hF x).mp hx
      refine ⟨⟨x,hp⟩,rfl,?_⟩
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact hw.symm
    · rintro ⟨u,hu,hw⟩
      refine ⟨(PS.domain_iff hF x).mpr (hu ▸ u.property),?_⟩
      exact (congrFun hw 0).symm.trans (congrFun hu δ)

end IntegrationInACVF.Section7
