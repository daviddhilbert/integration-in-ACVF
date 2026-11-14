import Integration7.GammaGeometricCommonWitnesses
import Integration7.GammaVolumeBaseEquality

/-! A geometric common witness depends on the actual coordinate/density
rows and the parameter base, including after a VF tuple is frozen. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B B' : Base (M := M)} {S : Set M} {p q a b k : ℕ}
variable {sp : Fin p → SortTag} {sq : Fin q → SortTag}

theorem RVVolumeSchemaRow.transport_rows
    {U : PositiveRVVolumeObject (M := M) S k}
    {F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp}
    {G : GammaRVVolumeSchema B' q U.underlying.obj.arity k sq}
    {z : Fin p → M} {t : Fin q → M} (P : RVVolumeSchemaRow U F z)
    (hV : ∀ r y, F.object.rowVolume z r y ↔ G.object.rowVolume t r y)
    (hD : ∀ r w, F.rowDensity z r w ↔ G.rowDensity t r w) : RVVolumeSchemaRow U G t :=
  ⟨fun r y => (hV r y).symm.trans (P.volume_iff r y),
    fun r w => (hD r w).symm.trans (P.density_iff r w)⟩

theorem GammaRVVolumeSchema.commonByGammaGeometry_transport_rows
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B p b k sp}
    {F' : GammaRVVolumeSchema B' q a k sq} {G' : GammaRVVolumeSchema B' q b k sq}
    {z : Fin p → M} {t : Fin q → M}
    (hBase : (⟨B.real ∪ Set.range z,B.gamma⟩ : Base (M := M)) = ⟨B'.real ∪ Set.range t,B'.gamma⟩)
    (hFV : ∀ r y, F.object.rowVolume z r y ↔ F'.object.rowVolume t r y)
    (hFD : ∀ r w, F.rowDensity z r w ↔ F'.rowDensity t r w)
    (hGV : ∀ r y, G.object.rowVolume z r y ↔ G'.object.rowVolume t r y)
    (hGD : ∀ r w, G.rowDensity z r w ↔ G'.rowDensity t r w)
    (h : F.commonByGammaGeometry G z) : F'.commonByGammaGeometry G' t := by
  obtain ⟨C,U,V,ha,hb,PU,PV,h⟩ := h
  subst a b
  let U' : GammaVolumeObjects ⟨B'.real ∪ Set.range t,B'.gamma⟩ (C.base : Set M) k :=
    ⟨U.val,hBase ▸ U.property⟩
  let V' : GammaVolumeObjects ⟨B'.real ∪ Set.range t,B'.gamma⟩ (C.base : Set M) k :=
    ⟨V.val,hBase ▸ V.property⟩
  refine ⟨C,U',V',rfl,rfl,PU.transport_rows hFV hFD,PV.transport_rows hGV hGD,?_⟩
  exact h.rebase hBase

end IntegrationInACVF.Section7
