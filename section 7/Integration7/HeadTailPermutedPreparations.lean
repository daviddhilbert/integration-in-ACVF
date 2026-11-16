module

public import Integration7.HeadTailPermutationSpecialRelative
public import Integration7.HeadTailPermutationHeadImages
public import IntegrationSection5.HeadPreparation

@[expose] public section

/-! A prescribed head preparation can be retained while reordering only
its frozen VF tail. This constructs a genuine special preparation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
open IntegrationInACVF.Section7

namespace IntegrationInACVF.Section5.HeadPreparation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n a : ℕ} {A : DefSet (M := M) S (n+1) a}

def permuteTail (T : HeadPreparation A) (τ : Equiv.Perm (Fin n)) :
    HeadPreparation (vfPermutationImage A (headTailPerm τ)) where
  arity := T.arity
  target := vfPermutationImage T.target (headTailPerm τ)
  map := vfPermutedMap T.map (headTailPerm τ)
  special := head_tail_permutation_special_relative T.map T.special τ
  saturated := by
    apply (headSaturated_iff_coordinateFibre _).mpr
    intro u
    rw [head_tail_permutation_fibre_carrier]
    exact (headSaturated_iff_coordinateFibre T.target).mp T.saturated _

theorem permute_tail_contracted_set (T : HeadPreparation A) (τ : Equiv.Perm (Fin n)) :
    (T.permuteTail τ).contractedSet = vfPermutationImage T.contractedSet τ :=
  head_image_tail_permutation T.target τ

theorem gamma_permute_tail_map (T : HeadPreparation A) (τ : Equiv.Perm (Fin n))
    (hA : GammaSetDefinable G (carrier A)) (hTarget : GammaSetDefinable G (carrier T.target))
    (hT : GammaGraphDefinable G (pointMapGraph T.map)) :
    GammaGraphDefinable G (pointMapGraph (T.permuteTail τ).map) :=
  gamma_vfPermutedMap T.map hA hTarget hT (headTailPerm τ)

theorem gamma_permute_tail_target (T : HeadPreparation A) (τ : Equiv.Perm (Fin n))
    (hTarget : GammaSetDefinable G (carrier T.target)) :
    GammaSetDefinable G (carrier (T.permuteTail τ).target) :=
  gamma_vfPermutationImage T.target hTarget (headTailPerm τ)

end IntegrationInACVF.Section5.HeadPreparation
