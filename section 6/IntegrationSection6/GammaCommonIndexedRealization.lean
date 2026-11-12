import IntegrationSection6.GammaChainIndexedRealization
import IntegrationSection6.GammaCommonBlowupSchemata
import IntegrationSection6.FiniteGammaCommonBlowups

/-! Uniform finite common-blowup witnesses glue to actual original-Gamma
common forward blowups over an RV[d] base, in RV[d+k]. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
variable {F : GammaFiniteRVSchema B p a k (fun _ => .rv)} {G : GammaFiniteRVSchema B p b k (fun _ => .rv)}
open FiniteRV

theorem GammaFiniteCommonSchema.indexedRealizeAt {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (H : GammaFiniteCommonSchema F G)
    (BP : GammaFiniteGraphPresentation B p d T R) (hvalid : ∀ t ∈ T, H.valid (fun j => (t j).val))
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP) :
    GammaIspAt hκ hs h00 hreal (gammaUniversalObject P.toGamma) (gammaUniversalObject Q.toGamma) := by
  let LP := H.leftObject.indexedPresentation BP (fun t ht => (hvalid t ht).1)
  let RP := H.rightObject.indexedPresentation BP (fun t ht => (hvalid t ht).2.1)
  have hL := H.leftChain.indexedRealize hκ hs h00 hreal BP (fun t ht => (hvalid t ht).2.2.1) P LP
  have hR := H.rightChain.indexedRealize hκ hs h00 hreal BP (fun t ht => (hvalid t ht).2.2.2.1) Q RP
  have e := H.comparison.indexedIsoBetween H.leftObject H.rightObject BP
    (fun t ht => (hvalid t ht).2.2.2.2.1)
    (fun t ht => (hvalid t ht).2.2.2.2.2.1) (fun t ht => (hvalid t ht).2.2.2.2.2.2) LP RP
  exact ⟨H.leftLength,H.rightLength,gammaUniversalObject LP.toGamma,gammaUniversalObject RP.toGamma,
    hL,hR,gammaUniversalIso LP.toGamma RP.toGamma e⟩

theorem GammaFiniteCommonSchema.indexedRealize {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (H : GammaFiniteCommonSchema F G)
    (BP : GammaFiniteGraphPresentation B p d T R) (hvalid : ∀ t ∈ T, H.valid (fun j => (t j).val))
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP) :
    GammaIsp hκ hs h00 hreal P.toGamma Q.toGamma :=
  ⟨Set.univ,Set.subset_univ _,Set.subset_univ _,H.indexedRealizeAt hκ hs h00 hreal BP hvalid P Q⟩

end IntegrationInACVF.Section6
