import IntegrationSection6.GammaRawCoproductSchemata
import IntegrationSection6.GammaSchemaPresentationEquality

/-! Arbitrary sorted coproduct rows have their actual native finite
coproduct presentations. Genuine uniform volume bounds make these same
formulas valid, without adding any Section6 uniformity assumption. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

theorem GammaFiniteRVSchema.coprod_row_relation (F : GammaFiniteRVSchema B p a k sp)
    (G : GammaFiniteRVSchema B p b k sp) (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    (hF : ∀ x y, F.rowVolume z x y → x ∈ F.rowDomain z)
    (hG : ∀ x y, G.rowVolume z x y → x ∈ G.rowDomain z)
    (w : Fin (1+(a+b)) → RV (M := M)) (v : Fin k → RV (M := M)) :
    graphCoprodRelation (F.rowDomain z) (G.rowDomain z) (F.rowVolume z) (G.rowVolume z) w v ↔
      (F.coprodFormula G).rowVolume z w v := by
  rw [F.coprod_row_volume_formula G z hz w v]
  constructor
  · rintro (⟨x,_,hx,hv⟩ | ⟨x,_,hx,hv⟩)
    · exact Or.inl ⟨x,hv,hx⟩
    · exact Or.inr ⟨x,hv,hx⟩
  · rintro (⟨x,hv,hx⟩ | ⟨x,hv,hx⟩)
    · exact Or.inl ⟨x,hF x v hv,hx,hv⟩
    · exact Or.inr ⟨x,hG x v hv,hx,hv⟩

def GammaFiniteRVSchema.coprodPresentation (F : GammaFiniteRVSchema B p a k sp)
    (G : GammaFiniteRVSchema B p b k sp) (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    (hF : ∀ x y, F.rowVolume z x y → x ∈ F.rowDomain z)
    (hG : ∀ x y, G.rowVolume z x y → x ∈ G.rowDomain z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z))
    (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ b k
      (G.rowDomain z) (G.rowVolume z)) :
    GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ (1+(a+b)) k
      ((F.coprodFormula G).rowDomain z) ((F.coprodFormula G).rowVolume z) :=
  (P.coprod Q).congrFormula
    (Set.ext (fun w => (F.coprod_row_domain_formula G z hz w).symm))
    (F.coprod_row_relation G z hz hF hG)

theorem GammaFiniteRVSchema.coprod_row_support (F : GammaFiniteRVSchema B p a k sp)
    (G : GammaFiniteRVSchema B p b k sp) (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    (hF : ∀ x y, F.rowVolume z x y → x ∈ F.rowDomain z)
    (hG : ∀ x y, G.rowVolume z x y → x ∈ G.rowDomain z)
    (w : Fin (1+(a+b)) → RV (M := M)) (v : Fin k → RV (M := M))
    (hv : (F.coprodFormula G).rowVolume z w v) : w ∈ (F.coprodFormula G).rowDomain z := by
  apply (F.coprod_row_domain_formula G z hz w).mpr
  rcases (F.coprod_row_volume_formula G z hz w v).mp hv with ⟨x,hv,hx⟩ | ⟨x,hv,hx⟩
  · exact Or.inl ⟨x,hF x v hv,hx⟩
  · exact Or.inr ⟨x,hG x v hv,hx⟩

theorem GammaFiniteRVSchema.exists_valid_coprod_bound {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaFiniteRVSchema B p a k sp) (G : GammaFiniteRVSchema B p b k sp)
    (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    (hF : ∀ x y, F.rowVolume z x y → x ∈ F.rowDomain z)
    (hG : ∀ x y, G.rowVolume z x y → x ∈ G.rowDomain z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z))
    (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ b k
      (G.rowDomain z) (G.rowVolume z)) :
    ∃ bound : ℕ, ((F.coprodFormula G).withBound bound).valid z :=
  (F.coprodFormula G).exists_valid_bound hκ hs hreal hgamma z hz
    (F.coprod_row_support G z hz hF hG) (F.coprodPresentation G z hz hF hG P Q)

end IntegrationInACVF.Section6
