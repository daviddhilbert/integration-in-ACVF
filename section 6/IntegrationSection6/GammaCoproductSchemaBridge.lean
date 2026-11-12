import IntegrationSection6.GammaCoproductFamilyRows
import IntegrationSection6.GammaGraphCoproducts
import IntegrationSection6.GammaGraphFormulaCongruence
import IntegrationSection6.GammaFamilyRowRealization

/-! The uniform coproduct family specializes to the actual finite native
coproduct at a common internal code base. Its global formulas have a valid
finite bound at every represented finite row. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ}

def GammaRVFamilyFormula.coprodPresentation
    (F : GammaRVFamilyFormula B p a k) (G : GammaRVFamilyFormula B p b k)
    (z : Fin p → VF (M := M))
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (z j).val),B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z))
    (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (z j).val),B.gamma⟩ b k
      (G.rowDomain z) (G.rowVolume z)) :
    GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (z j).val),B.gamma⟩ (1+(a+b)) k
      ((F.coprod G).rowDomain z) ((F.coprod G).rowVolume z) :=
  (P.coprod Q).congrFormula
    (Set.ext (fun w => (F.coprod_row_domain G z w).symm))
    (fun w v => (F.coprod_row_volume G z w v).symm)

theorem GammaRVFamilyFormula.coprodPresentation_toGamma
    (F : GammaRVFamilyFormula B p a k) (G : GammaRVFamilyFormula B p b k)
    (z : Fin p → VF (M := M))
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (z j).val),B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z))
    (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (z j).val),B.gamma⟩ b k
      (G.rowDomain z) (G.rowVolume z)) :
    (F.coprodPresentation G z P Q).toGamma = (gammaGraphCoprodAt P Q).toGamma := by
  exact (GammaFiniteGraphPresentation.congrFormula_toGamma (P.coprod Q) _ _).trans rfl

theorem GammaRVFamilyFormula.exists_valid_coprod_schema {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaRVFamilyFormula B p a k) (G : GammaRVFamilyFormula B p b k)
    (z : Fin p → VF (M := M))
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (z j).val),B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z))
    (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (z j).val),B.gamma⟩ b k
      (G.rowDomain z) (G.rowVolume z)) :
    ∃ bound : ℕ, ((F.coprod G).schema bound).valid (fun j => (z j).val) := by
  let C := F.coprodPresentation G z P Q
  exact (F.coprod G).exists_valid_schema hκ hs hreal hgamma z (F.coprod_row_support G z) C

end IntegrationInACVF.Section6
