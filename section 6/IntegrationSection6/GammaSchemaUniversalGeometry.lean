import IntegrationSection6.FiniteGammaUniversalCharts
import IntegrationSection6.GammaBlowupSchemata

/-! Uniform schema presentations have their literal native geometry at a
common internal code universe, with all original-base Gamma certificates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}
open FiniteRV

theorem gammaUniversalObject_graphCoprod
    {D : Set (Fin a → RV (M := M))} {E : Set (Fin b → RV (M := M))}
    {R : (Fin a → RV (M := M)) → (Fin k → RV (M := M)) → Prop}
    {T : (Fin b → RV (M := M)) → (Fin k → RV (M := M)) → Prop}
    (P : GammaFiniteGraphPresentation B a k D R) (Q : GammaFiniteGraphPresentation B b k E T) :
    gammaUniversalObject (gammaGraphCoprodAt P Q).toGamma =
      gammaCoprodAt (gammaUniversalObject P.toGamma) (gammaUniversalObject Q.toGamma) := by
  rfl

theorem GammaFiniteRVSchema.universal_coprodPresentation (F : GammaFiniteRVSchema B p a k sp)
    (G : GammaFiniteRVSchema B p b k sp) (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    (hF : ∀ x y, F.rowVolume z x y → x ∈ F.rowDomain z)
    (hG : ∀ x y, G.rowVolume z x y → x ∈ G.rowDomain z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z))
    (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ b k
      (G.rowDomain z) (G.rowVolume z)) :
    gammaUniversalObject (F.coprodPresentation G z hz hF hG P Q).toGamma =
      gammaCoprodAt (gammaUniversalObject P.toGamma) (gammaUniversalObject Q.toGamma) := by
  unfold GammaFiniteRVSchema.coprodPresentation
  rw [GammaFiniteGraphPresentation.congrFormula_toGamma]
  exact gammaUniversalObject_graphCoprod P Q

theorem GammaFiniteRVSchema.universal_elementaryPresentation {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z)) (i : Fin k)
    (hAd : GammaAdmissible P.toGamma.toGammaRVObject i) :
    gammaUniversalObject (F.elementaryPresentation hκ hs h00 hreal z hz P i hAd).toGamma =
      gammaElementaryAt hκ hs h00 (small_union_range hκ B.real hreal z)
        (gammaUniversalObject P.toGamma) i (gammaUniversalObject_admissible P.toGamma hAd) := by
  rfl

end IntegrationInACVF.Section6
