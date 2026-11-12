import IntegrationSection6.GammaSchemaIndexedCharts
import IntegrationSection6.GammaSchemaIndexedEquality
import IntegrationSection6.GammaSchemaIndexedPresentations
import IntegrationSection6.FiniteGammaIsoComposition

/-! A uniformly valid chart acts on arbitrary finite indexed presentations
of equal source and target rows. All chart composition keeps the original
Gamma base and the actual inherited finite morphism conditions. -/
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

def GammaFiniteRVIsoSchema.indexedIsoBetween
    (H : GammaFiniteRVIsoSchema B p a b k (fun _ => .rv))
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv))
    (G : GammaFiniteRVSchema B p b k (fun _ => .rv)) (BP : GammaFiniteGraphPresentation B p d T R)
    (hvalid : ∀ t ∈ T, H.valid (fun j => (t j).val))
    (hSource : ∀ t ∈ T, H.source.sameRow F (fun j => (t j).val))
    (hTarget : ∀ t ∈ T, H.target.sameRow G (fun j => (t j).val))
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP) :
    GammaRVIso P.toGamma.toGammaRVObject Q.toGamma.toGammaRVObject := by
  let SP := H.source.indexedPresentation BP (fun t ht => (hvalid t ht).1)
  let TP := H.target.indexedPresentation BP (fun t ht => (hvalid t ht).2.1)
  let eP := H.source.indexedRowIso F BP hSource SP P
  let eH := H.indexedIso BP hvalid SP TP
  let eQ := H.target.indexedRowIso G BP hTarget TP Q
  exact FiniteRV.gammaFiniteIsoTrans P.toGamma SP.toGamma Q.toGamma
    (FiniteRV.gammaFiniteIsoSymm SP.toGamma P.toGamma eP)
    (FiniteRV.gammaFiniteIsoTrans SP.toGamma TP.toGamma Q.toGamma eH eQ)

end IntegrationInACVF.Section6
