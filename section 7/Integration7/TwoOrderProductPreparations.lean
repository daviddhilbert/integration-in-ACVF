module

public import Integration7.RVClassProductOriginalUnaryVolumeComparison

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual preparations of the two translated product domains. The
record stores special chains and pullback targets, rather than assuming
a comparison of contractions. Its RV volume objects are the actual raw
objects of the indicated opposite-order standard contractions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {d : ℕ}

structure TwoOrderProductPreparations
    (X Y : DefSet (M := M) S 2 0) (D E : DefSet (M := M) S 1 0)
    (r t : RV (M := M)) (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ S)
    (P : Base (M := M)) where
  codes : Set M
  contains : S ⊆ codes
  dArity : ℕ
  eArity : ℕ
  dTarget : DefSet (M := M) codes 1 dArity
  eTarget : DefSet (M := M) codes 1 eArity
  dSpecial : SpecialBijection (extendBase D contains) dTarget
  eSpecial : SpecialBijection (extendBase E contains) eTarget
  dGamma : GammaChainDefinable P dSpecial.chain
  eGamma : GammaChainDefinable P eSpecial.chain
  dPullback : IsRVPullback (carrier dTarget)
  ePullback : IsRVPullback (carrier eTarget)
  headSaturated : HeadSaturated (carrier (extendBase X contains))
  tailSaturated : HeadSaturated (carrier (vfPermutationImage (extendBase Y contains) (Equiv.swap 0 1)))
  headPreparation : ConstantRVLabelSpecialPreparation eSpecial
    (headImage (fixedRVLabelDomain (extendBase X contains) z (fun j => contains (hz j))))
    (Fin.append (fun _ : Fin 1 => r) (Fin.append (Fin.elim0 : Fin 0 → RV (M := M)) z)) P
  tailPreparation : ConstantRVLabelSpecialPreparation dSpecial
    (headImage (fixedRVLabelDomain (vfPermutationImage (extendBase Y contains) (Equiv.swap 0 1)) z
      (fun j => contains (hz j))))
    (Fin.append (fun _ : Fin 1 => t) (Fin.append (Fin.elim0 : Fin 0 → RV (M := M)) z)) P

namespace TwoOrderProductPreparations
variable {P : Base (M := M)} {X Y : DefSet (M := M) S 2 0} {D E : DefSet (M := M) S 1 0}
variable {r t : RV (M := M)} {z : Fin d → RV (M := M)} {hz : ∀ j, (z j).val ∈ S}

def headContraction (F : TwoOrderProductPreparations X Y D E r t z hz P) :=
  rvClassProductStandardContraction (extendBase X F.contains) (extendBase E F.contains) F.eTarget
    F.eSpecial F.headSaturated r z (fun j => F.contains (hz j)) F.headPreparation

def tailContraction (F : TwoOrderProductPreparations X Y D E r t z hz P) :=
  swappedRVClassProductStandardContraction (extendBase Y F.contains) (extendBase D F.contains) F.dTarget
    F.dSpecial F.tailSaturated t z (fun j => F.contains (hz j)) F.tailPreparation

def headVolumeObject {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk P.real < κ) (hc : CanonicalStructure.IsCanonical (M := M))
    (F : TwoOrderProductPreparations X Y D E r t z hz P) (hr : r.val ∈ S)
    (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) : PositiveRVVolumeObject (M := M) F.codes 1 :=
  (rvClassProductRawVolumeObject hc (extendBase X F.contains) (extendBase E F.contains) F.eTarget
    F.eSpecial F.headSaturated r (F.contains hr) z (fun j => F.contains (hz j)) F.headPreparation
    (constant_label_prepared_pullback_finite_volume hκ hs hsmall F.headPreparation)).rescale η (F.contains hη) hη0

def tailVolumeObject {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk P.real < κ) (hc : CanonicalStructure.IsCanonical (M := M))
    (F : TwoOrderProductPreparations X Y D E r t z hz P) (ht : t.val ∈ S)
    (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) : PositiveRVVolumeObject (M := M) F.codes 1 :=
  (swappedRVClassProductRawVolumeObject hc (extendBase Y F.contains) (extendBase D F.contains) F.dTarget
    F.dSpecial F.tailSaturated t (F.contains ht) z (fun j => F.contains (hz j)) F.tailPreparation
    (constant_label_prepared_pullback_finite_volume hκ hs hsmall F.tailPreparation)).rescale η (F.contains hη) hη0

end TwoOrderProductPreparations
end IntegrationInACVF.Section7
