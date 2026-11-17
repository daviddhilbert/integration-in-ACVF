module

public import Integration7.HKVolumeClassCoherence
public import Integration7.ZeroCoefficientProductSymmetry
public import Integration7.HKRVProductBridges

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Moving an weighted measured-zero coefficient past a positive factor
introduces no VF coordinate permutation or sign. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem rv_volume_blowup_classes_zero_product_swap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (z : RVBlowupClasses hc C 0) (a : RVBlowupClasses hc C (n+1)) :
    HEq (rvVolumeBlowupClassesProduct hc C 0 (n+1) z a)
      (rvVolumeBlowupClassesProduct hc C (n+1) 0 a z) := by
  induction z using Quotient.inductionOn with
  | h Z =>
    induction a using Quotient.inductionOn with
    | h U =>
      let h := Nat.zero_add n
      let e := ((productZeroPositiveIso hc C Z U).trans hc C
        ((mixedProductSwapIso hc C U Z).symm hc C |>.reindexDegree hc C h)).trans hc C
          ((volumeCastReindexIso hc C (positiveZeroProduct U Z) h).trans hc C
            ((productPositiveZeroIso hc C U Z).symm hc C |>.cast h.symm))
      exact positive_volume_blowup_class_heq_of_cast_iso hc C h
        (product (C.base : Set M) 0 (n+1) Z U)
        (product (C.base : Set M) (n+1) 0 U Z) e

end IntegrationInACVF.Section7.HK
