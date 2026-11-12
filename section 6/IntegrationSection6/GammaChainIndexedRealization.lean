import IntegrationSection6.GammaBlowupIndexedRealization
import IntegrationSection6.GammaChainSchemata
import IntegrationSection6.FiniteGammaIterations

/-! A uniformly valid finite chain glues over an actual RV[d] base to a
native RV[d+k] forward chain of exactly the same length. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k r : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
variable {F : GammaFiniteRVSchema B p a k (fun _ => .rv)} {G : GammaFiniteRVSchema B p b k (fun _ => .rv)}
open FiniteRV

theorem GammaFiniteChainSchema.indexedRealize {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (H : GammaFiniteChainSchema F G r)
    (BP : GammaFiniteGraphPresentation B p d T R) :
    ∀ (hvalid : ∀ t ∈ T, H.valid (fun j => (t j).val))
      (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP),
    GammaIteratedBlowup hκ hs h00 hreal r (gammaUniversalObject P.toGamma) (gammaUniversalObject Q.toGamma) := by
  induction H with
  | iso chart =>
    intro hvalid P Q
    have e := chart.indexedIsoBetween _ _ BP
      (fun t ht => (hvalid t ht).1) (fun t ht => (hvalid t ht).2.1) (fun t ht => (hvalid t ht).2.2) P Q
    exact .zero (gammaUniversalIso P.toGamma Q.toGamma e)
  | step W head tail ih =>
    intro hvalid P Q
    let WP := W.indexedPresentation BP (fun t ht => (hvalid t ht).1)
    exact .cons (head.indexedRealize hκ hs h00 hreal BP (fun t ht => (hvalid t ht).2.1) P WP)
      (ih (fun t ht => (hvalid t ht).2.2) WP Q)

end IntegrationInACVF.Section6
