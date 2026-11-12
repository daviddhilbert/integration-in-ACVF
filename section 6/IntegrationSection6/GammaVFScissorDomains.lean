import Section7.GammaScissors

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

def packedVFSubset (D : Set (Point (M := M) n m)) : Set (Σ a : ℕ × ℕ, Point (M := M) a.1 a.2) :=
  Set.range (fun x : D => Sigma.mk (n,m) x.val)

theorem packedVFSubset_mem (D : Set (Point (M := M) n m)) (p : Point (M := M) n m) :
    Sigma.mk (n,m) p ∈ packedVFSubset D ↔ p ∈ D := by
  constructor
  · rintro ⟨x,hx⟩
    exact (eq_of_heq (Sigma.mk.inj_iff.mp hx).2) ▸ x.property
  · intro hp
    exact ⟨⟨p,hp⟩,rfl⟩

theorem gammaVFScissor_domains (A C D E : Set (Point (M := M) n m))
    (hA : GammaSetDefinable B A) (hC : GammaSetDefinable B C)
    (hD : GammaSetDefinable B D) (hE : GammaSetDefinable B E)
    (dA : GammaHasVFDimLE B A k) (dC : GammaHasVFDimLE B C k)
    (dD : GammaHasVFDimLE B D k) (dE : GammaHasVFDimLE B E k)
    (h : GammaVFScissor ⟨(n,m),A,hA,dA⟩ ⟨(n,m),C,hC,dC⟩ ⟨(n,m),D,hD,dD⟩ ⟨(n,m),E,hE,dE⟩) :
    D = A ∪ C ∧ E = A ∩ C := by
  have hu : packedVFSubset D = packedVFSubset A ∪ packedVFSubset C := h.2.2.2.1
  have hi : packedVFSubset E = packedVFSubset A ∩ packedVFSubset C := h.2.2.2.2
  constructor
  · ext p
    have hp := congrArg (fun Z => Sigma.mk (n,m) p ∈ Z) hu
    simpa only [Set.mem_union,packedVFSubset_mem] using (Iff.of_eq hp)
  · ext p
    have hp := congrArg (fun Z => Sigma.mk (n,m) p ∈ Z) hi
    simpa only [Set.mem_inter_iff,packedVFSubset_mem] using (Iff.of_eq hp)

end IntegrationInACVF.Section6.FiniteRV
