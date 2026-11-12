import IntegrationSection6.GammaSchemaIndexedObjects
import IntegrationSection6.GammaSchemaFiniteRowPresentations

/-! Named types for genuine finite indexed presentations and their native
fibre coproducts. Numerical bounds are not part of these types. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

abbrev GammaFiniteRVSchema.IndexedPresentation
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv)) (BP : GammaFiniteGraphPresentation B p d T R) :=
  GammaFiniteGraphPresentation B (p+a) (d+k)
    (indexedDomain T (fun t => F.rowDomain (fun j => (t j).val)))
    (fun w y => w ∈ indexedDomain T (fun t => F.rowDomain (fun j => (t j).val)) ∧
      indexedVolume BP.totalVolume (fun t => F.rowValue (fun j => (t j).val)) w = y)

def GammaFiniteRVSchema.indexedPresentation_finiteRows
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv)) (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.finiteRow (fun j => (t j).val)) : F.IndexedPresentation BP :=
  Classical.choice (F.exists_indexedPresentation_of_finiteRows BP hF)

abbrev GammaFiniteRVSchema.IndexedCoprodPresentation
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv))
    (G : GammaFiniteRVSchema B p b k (fun _ => .rv)) (BP : GammaFiniteGraphPresentation B p d T R) :=
  GammaFiniteGraphPresentation B (p+(1+(a+b))) (d+k)
    (indexedDomain T (fun t => graphCoprodDomain (F.rowDomain (fun j => (t j).val)) (G.rowDomain (fun j => (t j).val))))
    (fun w y => w ∈ indexedDomain T
      (fun t => graphCoprodDomain (F.rowDomain (fun j => (t j).val)) (G.rowDomain (fun j => (t j).val))) ∧
      indexedVolume BP.totalVolume (fun t => (F.coprodFormula G).rowValue (fun j => (t j).val)) w = y)

def GammaFiniteRVSchema.indexedCoprodPresentation
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv))
    (G : GammaFiniteRVSchema B p b k (fun _ => .rv)) (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.finiteRow (fun j => (t j).val))
    (hG : ∀ t ∈ T, G.finiteRow (fun j => (t j).val)) : F.IndexedCoprodPresentation G BP := by
  let P := (F.coprodFormula G).indexedPresentation_finiteRows BP
    (fun t ht => F.finiteRow_coprod G _ (fun j => (t j).property) (hF t ht) (hG t ht))
  have hD : indexedDomain T (fun t => (F.coprodFormula G).rowDomain (fun j => (t j).val)) =
      indexedDomain T (fun t => graphCoprodDomain (F.rowDomain (fun j => (t j).val)) (G.rowDomain (fun j => (t j).val))) := by
    apply Set.ext
    intro w
    exact and_congr Iff.rfl (F.coprod_row_domain_formula G _ (fun j => (indexedLeft w j).property) (indexedRight w))
  exact P.congrFormula hD (fun w y => and_congr (Iff.of_eq (congrArg (fun S => w ∈ S) hD)) Iff.rfl)

end IntegrationInACVF.Section6
