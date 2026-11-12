import IntegrationSection6.GammaChainSchemata
import IntegrationSection6.GammaBlowupRealization
import IntegrationSection6.FiniteGammaIterations

/-! Valid finite chain schemata reconstruct genuine native forward
blowups of exactly their encoded length. Every intermediate row remains
an actual finite-volume RV object at the common internal code universe. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k r : ℕ} {sp : Fin p → SortTag}
variable {U : GammaFiniteRVSchema B p a k sp} {V : GammaFiniteRVSchema B p b k sp}
open FiniteRV

theorem GammaFiniteChainSchema.realize {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (H : GammaFiniteChainSchema U V r) (z : Fin p → M) :
    ∀ (hz : H.valid z)
      (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
        (U.rowDomain z) (U.rowVolume z))
      (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ b k
        (V.rowDomain z) (V.rowVolume z)),
    GammaIteratedBlowup hκ hs h00 (small_union_range hκ B.real hreal z)
      r (gammaUniversalObject P.toGamma) (gammaUniversalObject Q.toGamma) := by
  induction H with
  | iso chart =>
    intro hz P Q
    have e := chart.realizeBetween _ _ z hz.1 hz.2.1 hz.2.2 P Q
    exact .zero (gammaUniversalIso P.toGamma Q.toGamma e)
  | step W head tail ih =>
    intro hz P Q
    obtain ⟨WP⟩ := W.realize z hz.1
    exact .cons (head.realizeBlowup hκ hs h00 hreal z hz.2.1 P WP) (ih hz.2.2 WP Q)

end IntegrationInACVF.Section6
