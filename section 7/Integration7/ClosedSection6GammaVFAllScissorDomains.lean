import Integration7.CompletedSection6Kernel
import Integration7.ClosedSection6GammaVFAllFinitePresentation
import IntegrationSection6.GammaVFAllScissorDomains
import IntegrationSection6.GammaVFAllFinitePresentation
import IntegrationSection6.GammaVFScissorDomains

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

theorem packedVFSubset_union (A C : Set (Point (M := M) n m)) :
    packedVFSubset (A ∪ C) = packedVFSubset A ∪ packedVFSubset C := by
  ext z
  constructor
  · rintro ⟨x,rfl⟩
    rcases x.property with ha | hc
    · exact Or.inl ⟨⟨x.val,ha⟩,rfl⟩
    · exact Or.inr ⟨⟨x.val,hc⟩,rfl⟩
  · rintro (⟨x,rfl⟩ | ⟨x,rfl⟩)
    · exact ⟨⟨x.val,Or.inl x.property⟩,rfl⟩
    · exact ⟨⟨x.val,Or.inr x.property⟩,rfl⟩

theorem packedVFSubset_inter (A C : Set (Point (M := M) n m)) :
    packedVFSubset (A ∩ C) = packedVFSubset A ∩ packedVFSubset C := by
  ext z
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨⟨⟨x.val,x.property.1⟩,rfl⟩,⟨⟨x.val,x.property.2⟩,rfl⟩⟩
  · rintro ⟨⟨x,rfl⟩,hy⟩
    exact ⟨⟨x.val,⟨x.property,(packedVFSubset_mem C x.val).mp hy⟩⟩,rfl⟩

theorem gammaVFAllScissor_domains (A C D E : Set (Point (M := M) n m))
    (hA : GammaSetDefinable B A) (hC : GammaSetDefinable B C)
    (hD : GammaSetDefinable B D) (hE : GammaSetDefinable B E)
    (fA : ∀ x, {t | (x,t) ∈ A}.Finite) (fC : ∀ x, {t | (x,t) ∈ C}.Finite)
    (fD : ∀ x, {t | (x,t) ∈ D}.Finite) (fE : ∀ x, {t | (x,t) ∈ E}.Finite) :
    GammaVFAllScissor ⟨(n,m),A,hA,fA⟩ ⟨(n,m),C,hC,fC⟩ ⟨(n,m),D,hD,fD⟩ ⟨(n,m),E,hE,fE⟩ ↔
      D = A ∪ C ∧ E = A ∩ C := by
  constructor
  · intro h
    have hu : packedVFSubset D = packedVFSubset A ∪ packedVFSubset C := h.2.2.2.1
    have hi : packedVFSubset E = packedVFSubset A ∩ packedVFSubset C := h.2.2.2.2
    constructor
    · ext p
      have hp := Iff.of_eq (congrArg (fun Z => Sigma.mk (n,m) p ∈ Z) hu)
      simpa only [Set.mem_union,packedVFSubset_mem] using hp
    · ext p
      have hp := Iff.of_eq (congrArg (fun Z => Sigma.mk (n,m) p ∈ Z) hi)
      simpa only [Set.mem_inter_iff,packedVFSubset_mem] using hp
  · rintro ⟨rfl,rfl⟩
    exact ⟨rfl,rfl,rfl,packedVFSubset_union A C,packedVFSubset_inter A C⟩

end IntegrationInACVF.Section7.CompletedSection6
