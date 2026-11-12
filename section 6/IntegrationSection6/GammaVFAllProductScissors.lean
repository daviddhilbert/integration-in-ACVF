import IntegrationSection6.GammaVFAllScissorDomains
import IntegrationSection6.GammaVFScissorDomains

/-! Recover literal unions and intersections from the actual packed
VF scissor relation in a common mixed arity. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k n m : ℕ}

theorem gammaVFAllScissor_product_right {A C D E : GammaVFAllFiniteObject B}
    (h : GammaVFAllScissor A C D E) (R : GammaVFAllFiniteObject B) :
    GammaVFAllScissor (gammaVFAllProduct A R) (gammaVFAllProduct C R)
      (gammaVFAllProduct D R) (gammaVFAllProduct E R) := by
  rcases A with ⟨⟨n,a⟩,A,hA,fA⟩
  rcases C with ⟨c,C,hC,fC⟩
  rcases D with ⟨d,D,hD,fD⟩
  rcases E with ⟨e,E,hE,fE⟩
  rcases h with ⟨hc,hd,he,hu,hi⟩
  change (n,a) = c at hc
  change (n,a) = d at hd
  change (n,a) = e at he
  subst c; subst d; subst e
  obtain ⟨rfl,rfl⟩ := (gammaVFAllScissor_domains A C D E hA hC hD hE fA fC fD fE).mp ⟨rfl,rfl,rfl,hu,hi⟩
  apply (gammaVFAllScissor_domains _ _ _ _ _ _ _ _ _ _ _ _).mpr
  constructor
  · ext p
    change ((_ ∨ _) ∧ _) ↔ ((_ ∧ _) ∨ (_ ∧ _))
    tauto
  · ext p
    change ((_ ∧ _) ∧ _) ↔ ((_ ∧ _) ∧ (_ ∧ _))
    tauto

theorem gammaVFAllScissor_product_left {A C D E : GammaVFAllFiniteObject B}
    (h : GammaVFAllScissor A C D E) (R : GammaVFAllFiniteObject B) :
    GammaVFAllScissor (gammaVFAllProduct R A) (gammaVFAllProduct R C)
      (gammaVFAllProduct R D) (gammaVFAllProduct R E) := by
  rcases A with ⟨⟨n,a⟩,A,hA,fA⟩
  rcases C with ⟨c,C,hC,fC⟩
  rcases D with ⟨d,D,hD,fD⟩
  rcases E with ⟨e,E,hE,fE⟩
  rcases h with ⟨hc,hd,he,hu,hi⟩
  change (n,a) = c at hc
  change (n,a) = d at hd
  change (n,a) = e at he
  subst c; subst d; subst e
  obtain ⟨rfl,rfl⟩ := (gammaVFAllScissor_domains A C D E hA hC hD hE fA fC fD fE).mp ⟨rfl,rfl,rfl,hu,hi⟩
  apply (gammaVFAllScissor_domains _ _ _ _ _ _ _ _ _ _ _ _).mpr
  constructor
  · ext p
    change (_ ∧ (_ ∨ _)) ↔ ((_ ∧ _) ∨ (_ ∧ _))
    tauto
  · ext p
    change (_ ∧ (_ ∧ _)) ↔ ((_ ∧ _) ∧ (_ ∧ _))
    tauto

end IntegrationInACVF.Section6.FiniteRV
