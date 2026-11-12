import IntegrationSection6.GammaSchemaPresentationEquality
import IntegrationSection6.GammaIsomorphismRealization

/-! A valid chart schema acts on any native presentations of equal source
and target rows. Equality is a checked formula condition, not a new choice
of isomorphism or an assumed uniformity statement. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

def GammaFiniteRVIsoSchema.realizeBetween (H : GammaFiniteRVIsoSchema B p a b k sp)
    (F : GammaFiniteRVSchema B p a k sp) (G : GammaFiniteRVSchema B p b k sp)
    (z : Fin p → M) (hz : H.valid z)
    (hF : H.source.sameRow F z) (hG : H.target.sameRow G z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z))
    (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ b k
      (G.rowDomain z) (G.rowVolume z)) :
    GammaRVIso P.toGamma.toGammaRVObject Q.toGamma.toGammaRVObject := by
  let A := P.congrFormula (H.source.sameRow_domains F hF).symm
    (fun x y => (hF.2.2 (fun j => (x j).val) (fun j => (y j).val)).symm)
  let C := Q.congrFormula (H.target.sameRow_domains G hG).symm
    (fun x y => (hG.2.2 (fun j => (x j).val) (fun j => (y j).val)).symm)
  have e := H.realizeChart z hz A C
  have hA : A.toGamma = P.toGamma := P.congrFormula_toGamma _ _
  have hC : C.toGamma = Q.toGamma := Q.congrFormula_toGamma _ _
  rw [hA,hC] at e
  exact e

end IntegrationInACVF.Section6
