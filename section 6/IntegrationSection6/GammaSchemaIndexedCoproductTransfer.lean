import IntegrationSection6.GammaSchemaIndexedCoproductIso

/-! The native indexed-coproduct chart applies directly to any finite
presentation of the uniform coproduct formula, before domain recoding. -/
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

def GammaFiniteRVSchema.indexedCoprodIsoFromRows
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv))
    (G : GammaFiniteRVSchema B p b k (fun _ => .rv)) (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.finiteRow (fun j => (t j).val))
    (hG : ∀ t ∈ T, G.finiteRow (fun j => (t j).val))
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (S : (F.coprodFormula G).IndexedPresentation BP) :
    GammaRVIso S.toGamma.toGammaRVObject (P.coprod Q).toGamma.toGammaRVObject := by
  have hD : indexedDomain T (fun t => (F.coprodFormula G).rowDomain (fun j => (t j).val)) =
      indexedDomain T (fun t => graphCoprodDomain (F.rowDomain (fun j => (t j).val)) (G.rowDomain (fun j => (t j).val))) := by
    apply Set.ext
    intro w
    exact and_congr Iff.rfl (F.coprod_row_domain_formula G _ (fun j => (indexedLeft w j).property) (indexedRight w))
  let Z := S.congrFormula hD (fun w y => and_congr (Iff.of_eq (congrArg (fun D => w ∈ D) hD)) Iff.rfl)
  have e := F.indexedCoprodIso G BP hF hG P Q Z
  rw [GammaFiniteGraphPresentation.congrFormula_toGamma] at e
  exact e

end IntegrationInACVF.Section6
