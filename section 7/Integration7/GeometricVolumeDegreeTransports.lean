import Integration7.GammaGeometricCommonRowTransport

/-! Transport the degree of a geometric schema comparison together with
its full volume rows. Density and label tuples remain part of the rows. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k l : ℕ} {sp : Fin p → SortTag}

theorem GammaRVVolumeSchema.commonByGammaGeometry_transport_degree
    (h : k=l) (F : GammaRVVolumeSchema B p a k sp) (G : GammaRVVolumeSchema B p b k sp)
    (F' : GammaRVVolumeSchema B p a l sp) (G' : GammaRVVolumeSchema B p b l sp) (z : Fin p → M)
    (hFV : ∀ r y, F.object.rowVolume z r (y ∘ (finCongr (congrArg Nat.succ h))) ↔ F'.object.rowVolume z r y)
    (hFD : ∀ r w, F.rowDensity z r w ↔ F'.rowDensity z r w)
    (hGV : ∀ r y, G.object.rowVolume z r (y ∘ (finCongr (congrArg Nat.succ h))) ↔ G'.object.rowVolume z r y)
    (hGD : ∀ r w, G.rowDensity z r w ↔ G'.rowDensity z r w)
    (hGeom : F.commonByGammaGeometry G z) : F'.commonByGammaGeometry G' z := by
  cases h
  exact GammaRVVolumeSchema.commonByGammaGeometry_transport_rows rfl
    (fun r y => by simpa only [finCongr_refl,Equiv.coe_refl,Function.comp_id] using hFV r y)
    hFD (fun r y => by simpa only [finCongr_refl,Equiv.coe_refl,Function.comp_id] using hGV r y) hGD hGeom

end IntegrationInACVF.Section7
