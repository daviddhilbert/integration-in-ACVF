import IntegrationSection6.GammaGraphPresentationIsomorphisms

/-! A presentation may use equivalent full domain/volume formulas without
changing its native object or its original-Gamma certificates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a k : ℕ}
variable {D D' : Set (Fin a → RV (M := M))}
variable {R R' : (Fin a → RV (M := M)) → (Fin k → RV (M := M)) → Prop}

def GammaFiniteGraphPresentation.congrFormula (P : GammaFiniteGraphPresentation B a k D R)
    (hD : D = D') (hR : ∀ x y, R x y ↔ R' x y) : GammaFiniteGraphPresentation B a k D' R' := by
  cases hD
  exact {
    codes := P.codes
    real_contains := P.real_contains
    finite_extra := P.finite_extra
    domain := P.domain
    domain_eq := P.domain_eq
    volume := P.volume
    graph_iff := fun x y => (P.graph_iff x y).trans (and_congr Iff.rfl (hR x y))
    finite_volume := P.finite_volume
    domain_graph := P.domain_graph
    volume_graph := P.volume_graph }

theorem GammaFiniteGraphPresentation.congrFormula_toGamma
    (P : GammaFiniteGraphPresentation B a k D R) (hD : D = D') (hR : ∀ x y, R x y ↔ R' x y) :
    (P.congrFormula hD hR).toGamma = P.toGamma := by
  cases hD
  rfl

end IntegrationInACVF.Section6
