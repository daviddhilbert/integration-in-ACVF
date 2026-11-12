import IntegrationSection6.GammaFiniteGraphObjects
import IntegrationSection6.FiniteGammaCommonBlowups

/-! Equality transport for graph presentations and the actual common-blowup
relation, with no change to its geometric meaning. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B C : Base (M := M)} {a b k : ℕ}
variable {D : Set (Fin a → RV (M := M))} {E : Set (Fin b → RV (M := M))}
variable {R : (Fin a → RV (M := M)) → (Fin k → RV (M := M)) → Prop}
variable {T : (Fin b → RV (M := M)) → (Fin k → RV (M := M)) → Prop}

def GammaFiniteGraphPresentation.rebase (P : GammaFiniteGraphPresentation B a k D R)
    (h : B = C) : GammaFiniteGraphPresentation C a k D R := h ▸ P

theorem gammaIsp_rebase_iff {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hB : Cardinal.mk B.real < κ) (hC : Cardinal.mk C.real < κ)
    (h : B = C) (P : GammaFiniteGraphPresentation B a k D R) (Q : GammaFiniteGraphPresentation B b k E T) :
    FiniteRV.GammaIsp hκ hs h00 hB P.toGamma Q.toGamma ↔
      FiniteRV.GammaIsp hκ hs h00 hC (P.rebase h).toGamma (Q.rebase h).toGamma := by
  cases h
  rfl

end IntegrationInACVF.Section6
