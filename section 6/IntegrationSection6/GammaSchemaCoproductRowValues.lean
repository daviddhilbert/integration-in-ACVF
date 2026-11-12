import IntegrationSection6.GammaSchemaFiniteRowPresentations

/-! The actual row volume of a coproduct agrees with the volume on each
native tagged summand, without any choice of a common finite bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem GammaFiniteRVSchema.rowValue_coprod_left (F : GammaFiniteRVSchema B p a k sp)
    (G : GammaFiniteRVSchema B p b k sp) (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    (hF : F.finiteRow z) (hG : G.finiteRow z) (x : Fin a → RV (M := M)) (hx : x ∈ F.rowDomain z) :
    (F.coprodFormula G).rowValue z (@rvLeftTag M N hN a b x) = F.rowValue z x := by
  have hSum := F.finiteRow_coprod G z hz hF hG
  have hD : @rvLeftTag M N hN a b x ∈ (F.coprodFormula G).rowDomain z :=
    (F.coprod_row_domain_formula G z hz _).mpr (Or.inl ⟨x,hx,rfl⟩)
  apply ((F.coprodFormula G).rowValue_graph_of_finiteRow z hSum _ hD _).mp
  apply (F.coprod_row_volume_formula G z hz _ _).mpr
  exact Or.inl ⟨x,(F.rowValue_graph_of_finiteRow z hF x hx _).mpr rfl,rfl⟩

theorem GammaFiniteRVSchema.rowValue_coprod_right (F : GammaFiniteRVSchema B p a k sp)
    (G : GammaFiniteRVSchema B p b k sp) (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    (hF : F.finiteRow z) (hG : G.finiteRow z) (y : Fin b → RV (M := M)) (hy : y ∈ G.rowDomain z) :
    (F.coprodFormula G).rowValue z (@rvRightTag M N hN b a y) = G.rowValue z y := by
  have hSum := F.finiteRow_coprod G z hz hF hG
  have hD : @rvRightTag M N hN b a y ∈ (F.coprodFormula G).rowDomain z :=
    (F.coprod_row_domain_formula G z hz _).mpr (Or.inr ⟨y,hy,rfl⟩)
  apply ((F.coprodFormula G).rowValue_graph_of_finiteRow z hSum _ hD _).mp
  apply (F.coprod_row_volume_formula G z hz _ _).mpr
  exact Or.inr ⟨y,(G.rowValue_graph_of_finiteRow z hG y hy _).mpr rfl,rfl⟩

end IntegrationInACVF.Section6
