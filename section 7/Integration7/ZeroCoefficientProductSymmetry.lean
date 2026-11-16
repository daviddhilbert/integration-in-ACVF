module

public import Integration7.AllDegreeVolumeClassCoherence
public import Integration7.ZeroFactorProductBridges

@[expose] public section

/-! Moving an ordinary degree-zero coefficient past a positive factor
introduces no VF coordinate permutation or sign. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem positive_volume_blowup_class_heq_of_cast_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {a b : ℕ} (h : a=b)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) a)
    (V : PositiveRVVolumeObject (M := M) (C.base : Set M) b)
    (e : RVVolumeIso U (V.cast h.symm)) :
    HEq (positiveVolumeBlowupClass hc C U) (positiveVolumeBlowupClass hc C V) := by
  cases h
  exact heq_of_eq (positiveVolumeBlowupClass_iso hc C e)

theorem rv_volume_blowup_classes_zero_product_swap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (z : RVVolumeBlowupClasses hc C 0) (a : RVVolumeBlowupClasses hc C (n+1)) :
    HEq (rvVolumeBlowupClassesProduct hc C 0 (n+1) z a)
      (rvVolumeBlowupClassesProduct hc C (n+1) 0 a z) := by
  induction z using Quotient.inductionOn with
  | h Z =>
    induction a using Quotient.inductionOn with
    | h U =>
      let h := Nat.zero_add n
      let e := ((volumeProductZeroPositiveIso hc C Z U).trans hc C
        ((volumeZeroProductSwapIso hc C U Z).symm hc C |>.reindexDegree hc C h)).trans hc C
          ((volumeCastReindexIso hc C (U.prod_zero Z) h).trans hc C
            ((volumeProductPositiveZeroIso hc C U Z).symm hc C |>.cast h.symm))
      exact positive_volume_blowup_class_heq_of_cast_iso hc C h
        (rvVolumeProduct (C.base : Set M) 0 (n+1) Z U)
        (rvVolumeProduct (C.base : Set M) (n+1) 0 U Z) e

end IntegrationInACVF.Section7
