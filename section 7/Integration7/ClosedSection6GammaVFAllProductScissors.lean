module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6GammaVFAllScissorDomains
public import IntegrationSection6.GammaVFAllProductScissors
public import IntegrationSection6.GammaVFAllScissorDomains
public import IntegrationSection6.GammaVFScissorDomains

@[expose] public section

/-! Closed generated-base Section6 integration. The former universal
Section5 input is replaced by the canonical-model certificate; its kernel
uses the proved generated-base contraction comparison. Original finite
objects, actual lifting, scissor addition and Cartesian products are retained.
This module keeps the dependent data and consumers in one coherent interface. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace IntegrationInACVF.Section7.CompletedSection6
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

end IntegrationInACVF.Section7.CompletedSection6
