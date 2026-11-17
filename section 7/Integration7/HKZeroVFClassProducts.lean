module

public import Integration7.HKZeroVFProducts
public import Integration7.HKVolumeClassCoherence

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Concrete Cartesian multiplication on weighted zero VF classes agrees
with the corrected RV multiplication under the actual lift and integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def zeroVFClassesProduct (S : Set M) : ZeroVFVolumeClasses (M := M) S →
    ZeroVFVolumeClasses (M := M) S → ZeroVFVolumeClasses (M := M) S :=
  Quotient.map₂ zeroVFProduct (by
    rintro A A' ⟨f⟩ B B' ⟨g⟩
    exact ⟨zeroVFProductIso f g⟩)

theorem zero_lift_classes_product (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (a b : RVBlowupClasses hc C 0) :
    zeroLiftOnClasses (C.base : Set M) (rvVolumeBlowupClassesProduct hc C 0 0 a b) =
      zeroVFClassesProduct (C.base : Set M) (zeroLiftOnClasses (C.base : Set M) a)
        (zeroLiftOnClasses (C.base : Set M) b) := by
  induction a using Quotient.inductionOn with
  | h U =>
    induction b using Quotient.inductionOn with
    | h V => exact Quotient.sound ⟨(zeroLiftProductIso U V).symm⟩

theorem zero_integration_classes_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (a b : ZeroVFVolumeClasses (M := M) (C.base : Set M)) :
    zeroVolumeIntegrationEquiv hc C (zeroVFClassesProduct (C.base : Set M) a b) =
      rvVolumeBlowupClassesProduct hc C 0 0 (zeroVolumeIntegrationEquiv hc C a)
        (zeroVolumeIntegrationEquiv hc C b) := by
  let E := zeroVolumeIntegrationEquiv hc C
  apply E.symm.injective
  change E.symm (E (zeroVFClassesProduct (C.base : Set M) a b)) =
    zeroLiftOnClasses (C.base : Set M) (rvVolumeBlowupClassesProduct hc C 0 0 (E a) (E b))
  rw [E.symm_apply_apply,zero_lift_classes_product]
  change zeroVFClassesProduct (C.base : Set M) a b =
    zeroVFClassesProduct (C.base : Set M) (E.symm (E a)) (E.symm (E b))
  rw [E.symm_apply_apply,E.symm_apply_apply]

end IntegrationInACVF.Section7.HK
