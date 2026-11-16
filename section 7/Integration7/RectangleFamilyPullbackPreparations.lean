module

public import Integration7.RectangleFamilySaturationPreservation
public import Integration7.GammaRectangleFamilyHeadPreparations

@[expose] public section

/-! Two actual labelled unary preparations turn an entire rectangle
family into an RV pullback. Saturation from the first coordinate is
preserved during the second preparation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m : ℕ}

structure RectangleFamilyPullbackPreparation (G : Base (M := M)) (H : DefSet (M := M) S 2 m) where
  head : HeadPreparation H
  tail : HeadPreparation (vfPermutationImage head.target (Equiv.swap 0 1))
  head_graph : GammaGraphDefinable G (pointMapGraph head.map)
  head_target : GammaSetDefinable G (carrier head.target)
  tail_graph : GammaGraphDefinable G (pointMapGraph tail.map)
  tail_target : GammaSetDefinable G (carrier tail.target)
  pullback : IsRVPullback (carrier tail.target)

namespace RectangleFamilyPullbackPreparation
variable {H : DefSet (M := M) S 2 m}

def toMap (F : RectangleFamilyPullbackPreparation G H) : Map H F.tail.target :=
  Map.comp F.tail.map (Map.comp (vfPermutationBijection F.head.target (Equiv.swap 0 1)) F.head.map)

theorem bijective (F : RectangleFamilyPullbackPreparation G H) : Function.Bijective F.toMap :=
  F.tail.bijective.comp ((vfPermutationBijection_bijective F.head.target (Equiv.swap 0 1)).comp F.head.bijective)

theorem graph_gamma (F : RectangleFamilyPullbackPreparation G H) :
    GammaGraphDefinable G (pointMapGraph F.toMap) :=
  gamma_composition_graph _ _
    (gamma_composition_graph _ _ F.head_graph (gamma_vfPermutation_graph F.head.target F.head_target (Equiv.swap 0 1)))
    F.tail_graph

end RectangleFamilyPullbackPreparation

theorem rectangle_family_pullback_preparation_exists (C : BaseContext M)
    (hNames : commonRealNames G ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (H : DefSet (M := M) (C.base : Set M) 2 m) (hH : GammaSetDefinable G (carrier H))
    (hRect : RectangularRVFibres (carrier H)) : Nonempty (RectangleFamilyPullbackPreparation G H) := by
  obtain ⟨r,D,T,hT,hD⟩ := gamma_unary_pullback_preparation_over_common_names C hNames γ hγ hγ1
    (Map.image (coordinateProjectMap 0 H)) (gamma_native_head_projection H hH)
  let P := rectangleFamilyHeadPreparation H hRect T hD
  have hP := rectangle_family_head_preparation_map_gamma H hH hRect T hT hD
  have hY := rectangle_family_head_preparation_target_gamma H hH hRect T hT hD
  have hRectY := rectangle_family_prepared_target_rectangular H hRect T hD
  let X := vfPermutationImage P.target (Equiv.swap 0 1)
  have hX := gamma_vfPermutationImage P.target hY (Equiv.swap 0 1)
  have hRectX := rectangular_rv_fibres_swap P.target hRectY
  have hTailX := swapped_tail_saturated_of_head P.target P.saturated
  obtain ⟨s,E,U,hU,hE⟩ := gamma_unary_pullback_preparation_over_common_names C hNames γ hγ hγ1
    (Map.image (coordinateProjectMap 0 X)) (gamma_native_head_projection X hX)
  let Q := rectangleFamilyHeadPreparation X hRectX U hE
  have hQ := rectangle_family_head_preparation_map_gamma X hX hRectX U hU hE
  have hZ := rectangle_family_head_preparation_target_gamma X hX hRectX U hU hE
  have hSat := rectangle_family_prepared_target_tail_saturated X hRectX U hE hTailX
  exact ⟨⟨P,Q,hP,hY,hQ,hZ,is_rv_pullback_of_two_coordinate_saturation Q.saturated hSat⟩⟩

end IntegrationInACVF.Section7
