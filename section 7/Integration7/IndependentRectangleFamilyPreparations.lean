module

public import Integration7.SwappedRectangleProjectionDomains
public import Integration7.RVLabelConstraintHeadProductImages

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Both rectangle orders use the same two independently chosen
labelled unary preparations. Only their carried-label lifts differ. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m r b : ℕ}

theorem gamma_special_cast_both
    {n a c : ℕ} {A A' : DefSet (M := M) S n a} {B B' : DefSet (M := M) S n c}
    (T : SpecialBijection A B) (hA : A = A') (hB : B = B') (hT : GammaChainDefinable G T.chain) :
    GammaChainDefinable G (specialCastBoth T hA hB).chain := by
  cases hA
  cases hB
  exact hT

def swappedRectangleHeadSpecial {H : DefSet (M := M) S 2 m} {E : DefSet (M := M) S 1 b}
    (W : SpecialBijection (Map.image (coordinateProjectMap 1 H)) E) :
    SpecialBijection (Map.image (coordinateProjectMap 0 (vfPermutationImage H (Equiv.swap 0 1)))) E :=
  specialCastBoth W (swapped_rectangle_head_projection H).symm rfl

def swappedRectangleTailSpecial {H : DefSet (M := M) S 2 m} {D : DefSet (M := M) S 1 r}
    (T : SpecialBijection (Map.image (coordinateProjectMap 0 H)) D) :
    SpecialBijection (Map.image (coordinateProjectMap 1 (vfPermutationImage H (Equiv.swap 0 1)))) D :=
  specialCastBoth T (swapped_rectangle_tail_projection H).symm rfl

structure IndependentRectangleFamilyPreparations (G : Base (M := M))
    (H : DefSet (M := M) S 2 m) (hRect : RectangularRVFibres (carrier H)) where
  headArity : ℕ
  tailArity : ℕ
  headTarget : DefSet (M := M) S 1 headArity
  tailTarget : DefSet (M := M) S 1 tailArity
  headSpecial : SpecialBijection (Map.image (coordinateProjectMap 0 H)) headTarget
  tailSpecial : SpecialBijection (Map.image (coordinateProjectMap 1 H)) tailTarget
  headGamma : GammaChainDefinable G headSpecial.chain
  tailGamma : GammaChainDefinable G tailSpecial.chain
  headPullback : IsRVPullback (carrier headTarget)
  tailPullback : IsRVPullback (carrier tailTarget)
  headLift : RVLabelConstraintSpecialPreparation tailSpecial
    (rectangleFamilyHeadPreparation H hRect headSpecial headPullback).contractedSet
    (headImage headTarget) (rectangleHeadOldLabelIndex headSpecial) G
  tailLift : RVLabelConstraintSpecialPreparation (swappedRectangleTailSpecial headSpecial)
    (rectangleFamilyHeadPreparation (vfPermutationImage H (Equiv.swap 0 1))
      (rectangular_rv_fibres_swap H hRect) (swappedRectangleHeadSpecial tailSpecial) tailPullback).contractedSet
    (headImage tailTarget) (rectangleHeadOldLabelIndex (swappedRectangleHeadSpecial tailSpecial)) G

theorem independent_rectangle_family_preparations_exists (C : BaseContext M)
    (hNames : commonRealNames G ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (H : DefSet (M := M) (C.base : Set M) 2 m) (hH : GammaSetDefinable G (carrier H))
    (hRect : RectangularRVFibres (carrier H)) : Nonempty (IndependentRectangleFamilyPreparations G H hRect) := by
  obtain ⟨r,D,T,hT,hD⟩ := gamma_unary_pullback_preparation_over_common_names C hNames γ hγ hγ1
    (Map.image (coordinateProjectMap 0 H)) (gamma_native_head_projection H hH)
  have hX := gamma_vfPermutationImage H hH (Equiv.swap 0 1)
  have hTail : GammaSetDefinable G (carrier (Map.image (coordinateProjectMap 1 H))) := by
    rw [← swapped_rectangle_head_projection H]
    exact gamma_native_head_projection _ hX
  obtain ⟨b,E,W,hW,hE⟩ := gamma_unary_pullback_preparation_over_common_names C hNames γ hγ hγ1
    (Map.image (coordinateProjectMap 1 H)) hTail
  obtain ⟨L⟩ := gamma_rectangle_family_second_stage_preparation_exists H hH hRect T hT hD W hW hE
  obtain ⟨K⟩ := gamma_rectangle_family_second_stage_preparation_exists _ hX
    (rectangular_rv_fibres_swap H hRect) (swappedRectangleHeadSpecial W)
    (gamma_special_cast_both W _ _ hW) hE (swappedRectangleTailSpecial T)
    (gamma_special_cast_both T _ _ hT) hD
  exact ⟨⟨r,b,D,E,T,W,hT,hW,hD,hE,L,K⟩⟩

end IntegrationInACVF.Section7
