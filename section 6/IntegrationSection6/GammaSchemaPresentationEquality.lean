import IntegrationSection6.GammaSchemaRowEquality

/-! Equality of schema rows induces the actual label-identity isomorphism
between their arbitrary native finite presentations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

def GammaFiniteRVSchema.sameRowIso (F G : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (h : F.sameRow G z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z))
    (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
      (G.rowDomain z) (G.rowVolume z)) :
    GammaRVIso P.toGamma.toGammaRVObject Q.toGamma.toGammaRVObject := by
  let P' := P.congrFormula (F.sameRow_domains G h)
    (fun x y => h.2.2 (fun j => (x j).val) (fun j => (y j).val))
  have e := gammaGraphPresentationIso P' Q
  have he : P'.toGamma = P.toGamma := P.congrFormula_toGamma _ _
  rw [he] at e
  exact e

theorem GammaFiniteRVSchema.valid_row_support (F : GammaFiniteRVSchema B p a k sp)
    {z : Fin p → M} (hz : F.valid z) (x : Fin a → RV (M := M)) (y : Fin k → RV (M := M))
    (hxy : F.rowVolume z x y) : x ∈ F.rowDomain z :=
  hz.2.2.1 _ _ hxy

end IntegrationInACVF.Section6
