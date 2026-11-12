import IntegrationSection6.GammaSchemaIndexedGraphs

/-! Assemble all valid schema rows over an actual RV[d] base into an
actual RV[d+k] object. Fibre finiteness uses both the index volume fibres
and the row volume fibres, allowing an infinite index set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem GammaFiniteRVSchema.exists_indexedPresentation_of_finiteRows
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv))
    (P : GammaFiniteGraphPresentation B p d T R)
    (hvalid : ∀ t ∈ T, F.finiteRow (fun j => (t j).val)) :
    Nonempty (GammaFiniteGraphPresentation B (p+a) (d+k)
      (indexedDomain T (fun t => F.rowDomain (fun j => (t j).val)))
      (fun w y => w ∈ indexedDomain T (fun t => F.rowDomain (fun j => (t j).val)) ∧
        indexedVolume P.totalVolume (fun t => F.rowValue (fun j => (t j).val)) w = y)) :=
  exists_gammaIndexedFinitePresentation T (fun t => F.rowDomain (fun j => (t j).val))
    P.totalVolume (fun t => F.rowValue (fun j => (t j).val))
    (F.indexed_domain_graph P) (F.indexed_volume_graph P hvalid) P.totalVolume_finite_fibres
    (fun t ht y => F.rowValue_finite_of_finiteRow _ (hvalid t ht) y)

theorem GammaFiniteRVSchema.exists_indexedPresentation
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv))
    (P : GammaFiniteGraphPresentation B p d T R)
    (hvalid : ∀ t ∈ T, F.valid (fun j => (t j).val)) :
    Nonempty (GammaFiniteGraphPresentation B (p+a) (d+k)
      (indexedDomain T (fun t => F.rowDomain (fun j => (t j).val)))
      (fun w y => w ∈ indexedDomain T (fun t => F.rowDomain (fun j => (t j).val)) ∧
        indexedVolume P.totalVolume (fun t => F.rowValue (fun j => (t j).val)) w = y)) :=
  exists_gammaIndexedFinitePresentation T (fun t => F.rowDomain (fun j => (t j).val))
    P.totalVolume (fun t => F.rowValue (fun j => (t j).val))
    (F.indexed_domain_graph P) (F.indexed_volume_graph P (fun t ht => F.finiteRow_of_valid _ (hvalid t ht))) P.totalVolume_finite_fibres
    (fun t ht y => F.rowValue_finite_fibres _ (hvalid t ht) y)

def GammaFiniteRVSchema.indexedPresentation
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv))
    (P : GammaFiniteGraphPresentation B p d T R)
    (hvalid : ∀ t ∈ T, F.valid (fun j => (t j).val)) :
    GammaFiniteGraphPresentation B (p+a) (d+k)
      (indexedDomain T (fun t => F.rowDomain (fun j => (t j).val)))
      (fun w y => w ∈ indexedDomain T (fun t => F.rowDomain (fun j => (t j).val)) ∧
        indexedVolume P.totalVolume (fun t => F.rowValue (fun j => (t j).val)) w = y) :=
  Classical.choice (F.exists_indexedPresentation P hvalid)

end IntegrationInACVF.Section6
