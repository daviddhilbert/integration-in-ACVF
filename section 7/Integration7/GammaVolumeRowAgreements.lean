import Integration7.IndexedVolumeEqualRowPresentations
import Integration7.GammaWeightedVolumeSchemata
import Integration7.EssentialFiniteVolumeSchemata
import IntegrationSection6.GammaRowOperationAgreement
import IntegrationSection6.GammaSchemaValidityTransport

/-! Literal coordinate-and-density row agreement across parameter
sorts and arities. It preserves the geometric formula operations. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a b k : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def GammaVolumeRowAgreement (F : GammaRVVolumeSchema B p a k sp) (z : Fin p → M)
    (G : GammaRVVolumeSchema B q a k sq) (t : Fin q → M) : Prop :=
  GammaSchemaRowAgreement F.object z G.object t ∧
    GammaSchemaRowAgreement F.densityTemplate z G.densityTemplate t

theorem GammaVolumeRowAgreement.symm
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B q a k sq}
    {z : Fin p → M} {t : Fin q → M} (h : GammaVolumeRowAgreement F z G t) :
    GammaVolumeRowAgreement G t F z :=
  ⟨GammaSchemaRowAgreement.symm h.1,GammaSchemaRowAgreement.symm h.2⟩

theorem GammaVolumeRowAgreement.density
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B q a k sq}
    {z : Fin p → M} {t : Fin q → M} (h : GammaVolumeRowAgreement F z G t)
    (x : Fin a → RV (M := M)) (ω : Fin 1 → RV (M := M)) :
    F.rowDensity z x ω ↔ G.rowDensity t x ω := h.2.2 (rvValues x) (rvValues ω)

theorem gammaVolumeRowAgreement_of_typed
    (F : GammaRVVolumeSchema B p a k sp) (z : Fin p → M)
    (G : GammaRVVolumeSchema B q a k sq) (t : Fin q → M)
    (hV : GammaSchemaRowAgreement F.object z G.object t)
    (hρ : ∀ (x : Fin a → RV (M := M)) (ω : Fin 1 → RV (M := M)),
      F.rowDensity z x ω ↔ G.rowDensity t x ω) : GammaVolumeRowAgreement F z G t :=
  ⟨hV,gammaSchemaRowAgreement_of_typed F.densityTemplate z G.densityTemplate t
    (fun x => hV.1 (rvValues x)) hρ⟩

theorem GammaVolumeRowAgreement.valid
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B q a k sq}
    {z : Fin p → M} {t : Fin q → M} (h : GammaVolumeRowAgreement F z G t)
    (ht : ∀ i, sortEval (sq i) (t i)) (hBound : F.object.bound = G.object.bound) (hF : F.valid z) : G.valid t := by
  refine ⟨F.object.valid_of_rowAgreement G.object z t ht hBound h.1 hF.1,ht,?_,?_⟩
  · intro x hx
    obtain ⟨y,hy,hu⟩ := hF.2.2.1 x ((h.1.1 x).mpr hx)
    exact ⟨y,(h.2.2 x y).mp hy,fun y' hy' => hu y' ((h.2.2 x y').mpr hy')⟩
  · intro x y hy
    exact (h.1.1 x).mp (hF.2.2.2 x y ((h.2.2 x y).mpr hy))

theorem gammaVolumeSameRow_of_agreement
    {F H : GammaRVVolumeSchema B p a k sp} {G K : GammaRVVolumeSchema B q a k sq}
    {z : Fin p → M} {t : Fin q → M} (ht : ∀ i, sortEval (sq i) (t i))
    (hF : GammaVolumeRowAgreement F z G t) (hH : GammaVolumeRowAgreement H z K t)
    (h : F.sameRow H z) : G.sameRow K t :=
  ⟨gammaSchemaSameRow_of_agreement ht hF.1 hH.1 h.1,
    gammaSchemaSameRow_of_agreement ht hF.2 hH.2 h.2⟩

theorem GammaVolumeRowAgreement.coprod
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B q a k sq}
    {H : GammaRVVolumeSchema B p b k sp} {K : GammaRVVolumeSchema B q b k sq}
    {z : Fin p → M} {t : Fin q → M}
    (hF : GammaVolumeRowAgreement F z G t) (hH : GammaVolumeRowAgreement H z K t)
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i)) :
    GammaVolumeRowAgreement (F.coprodFormula H) z (G.coprodFormula K) t := by
  apply gammaVolumeRowAgreement_of_typed _ z _ t (hF.1.coprod hH.1 hz ht)
  intro w ω
  rw [F.coprod_rowDensity H z hz w ω,G.coprod_rowDensity K t ht w ω]
  exact or_congr (exists_congr (fun x => and_congr (hF.density x ω) Iff.rfl))
    (exists_congr (fun x => and_congr (hH.density x ω) Iff.rfl))

theorem GammaVolumeRowAgreement.elementary
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B q a k sq}
    {z : Fin p → M} {t : Fin q → M} (h : GammaVolumeRowAgreement F z G t)
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i)) :
    GammaVolumeRowAgreement F.elementaryFormula z G.elementaryFormula t := by
  have hV := h.1.elementary hz ht (Fin.last k)
  apply gammaVolumeRowAgreement_of_typed _ z _ t hV
  intro w ω
  rw [F.elementary_rowDensity z hz w ω,G.elementary_rowDensity t ht w ω]
  exact and_congr (h.density (w ∘ Fin.castAdd 1) ω) (hV.1 (rvValues w))

theorem essentialFiniteVolumeSchema_rowAgreement {d : ℕ}
    {F : GammaFiniteRVSchema B p a d sp} {G : GammaFiniteRVSchema B q a d sq}
    {z : Fin p → M} {t : Fin q → M} (h : GammaSchemaRowAgreement F z G t) :
    GammaSchemaRowAgreement (essentialFiniteVolumeSchema F) z (essentialFiniteVolumeSchema G) t := by
  apply gammaSchemaRowAgreement_of_typed
  · intro x
    rw [essentialFiniteVolumeSchema_rowDomain,essentialFiniteVolumeSchema_rowDomain]
    exact exists_congr (fun y => and_congr (h.2 (rvValues x) (rvValues y)) Iff.rfl)
  · intro x y
    rw [essentialFiniteVolumeSchema_rowVolume,essentialFiniteVolumeSchema_rowVolume]
    exact and_congr (h.2 (rvValues x) (rvValues y)) Iff.rfl

theorem GammaVolumeRowAgreement.weighted
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B q a k sq}
    {z : Fin p → M} {t : Fin q → M} (h : GammaVolumeRowAgreement F z G t) :
    GammaSchemaRowAgreement (weightedVolumeSchema F) z (weightedVolumeSchema G) t := by
  apply gammaSchemaRowAgreement_of_typed
  · intro x
    exact h.1.1 (rvValues x)
  · intro x w
    rw [weightedVolumeSchema_rowVolume,weightedVolumeSchema_rowVolume]
    exact and_congr (h.1.2 (rvValues x) (rvValues (w ∘ Fin.castAdd 1)))
      (h.density x (w ∘ Fin.natAdd (k+1)))

end IntegrationInACVF.Section7
