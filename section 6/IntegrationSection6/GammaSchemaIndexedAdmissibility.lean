import IntegrationSection6.GammaSchemaIndexedObjects
import IntegrationSection6.GammaSchemaRowImages
import IntegrationSection6.GammaIndexedAdmissibility

/-! Valid admissibility rows glue to actual Gamma admissibility in the
finite-volume indexed object. The index set may be infinite; fixing its
volume leaves only finitely many rows. -/
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

theorem GammaFiniteAdmissibilitySchema.indexed_admissible
    (F : GammaFiniteAdmissibilitySchema B p a k (fun _ => .rv))
    (P : GammaFiniteGraphPresentation B p d T R)
    (hvalid : ∀ t ∈ T, F.valid (fun j => (t j).val))
    (Q : GammaFiniteGraphPresentation B (p+a) (d+k)
      (indexedDomain T (fun t => F.object.rowDomain (fun j => (t j).val)))
      (fun w y => w ∈ indexedDomain T (fun t => F.object.rowDomain (fun j => (t j).val)) ∧
        indexedVolume P.totalVolume (fun t => F.object.rowValue (fun j => (t j).val)) w = y)) :
    GammaAdmissible Q.toGamma.toGammaRVObject (Fin.natAdd d F.coordinate) :=
  gammaIndexed_admissible T (fun t => F.object.rowDomain (fun j => (t j).val))
    P.totalVolume (fun t => F.object.rowValue (fun j => (t j).val)) Q F.coordinate
    P.totalVolume_finite_fibres
    (fun t ht y => F.rowValue_finite_slices _ (hvalid t ht) y)
    (fun t ht x hx => F.rowValue_nonzero _ (hvalid t ht) x hx)

end IntegrationInACVF.Section6
