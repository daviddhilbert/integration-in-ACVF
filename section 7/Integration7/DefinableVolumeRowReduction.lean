import Integration7.DefinableVolumeBaseReduction
import Integration7.GammaGeometricCommonRowTransport
import Integration7.ContractionParameterExtension

/-! Full geometric rows descend along a genuine elimination of definable
parameter names. The actual volume objects and every forward blowup are
kept; only their definability certificates change. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B D : Base (M := M)} {S : Set M} {n a b : ℕ}

theorem gamma_program_mono (hBD : B.real ⊆ D.real) (hΓ : B.gamma ⊆ D.gamma)
    {U : DefSet (M := M) S n a} {V : DefSet (M := M) S 0 b}
    (T : OrderedContractionProgram S U V) (hT : GammaProgramDefinable B T) :
    GammaProgramDefinable D T := by
  induction T with
  | zero U => exact hT.mono hBD hΓ
  | step T tail ih => exact ⟨hT.1.mono hBD hΓ,hT.2.1.mono hBD hΓ,ih hT.2.2⟩

theorem GammaRVVolumeSchema.commonByGammaGeometry_reduce_rows
    {p q a b k : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}
    {F : GammaRVVolumeSchema D p a k sp} {G : GammaRVVolumeSchema D p b k sp}
    {F' : GammaRVVolumeSchema B q a k sq} {G' : GammaRVVolumeSchema B q b k sq}
    {z : Fin p → M} {t : Fin q → M}
    (H : GammaDefinableBaseReduction ⟨D.real ∪ Set.range z,D.gamma⟩ ⟨B.real ∪ Set.range t,B.gamma⟩)
    (hFV : ∀ r y, F.object.rowVolume z r y ↔ F'.object.rowVolume t r y)
    (hFD : ∀ r w, F.rowDensity z r w ↔ F'.rowDensity t r w)
    (hGV : ∀ r y, G.object.rowVolume z r y ↔ G'.object.rowVolume t r y)
    (hGD : ∀ r w, G.rowDensity z r w ↔ G'.rowDensity t r w)
    (h : F.commonByGammaGeometry G z) : F'.commonByGammaGeometry G' t := by
  obtain ⟨C,U,V,ha,hb,PU,PV,h⟩ := h
  subst a b
  exact ⟨C,H.volumeObjects U,H.volumeObjects V,rfl,rfl,
    PU.transport_rows hFV hFD,PV.transport_rows hGV hGD,H.volumeCommon h⟩

end IntegrationInACVF.Section7
