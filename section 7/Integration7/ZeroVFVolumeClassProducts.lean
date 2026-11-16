module

public import Integration7.OrdinaryFiniteProductIsomorphisms
public import Integration7.VolumeLiftProductDomains
public import Integration7.ZeroVolumeIntegration

@[expose] public section

/-! Multiplication of ordinary VF[0] isomorphism classes is actual
Cartesian product, and the ordinary degree-zero integration preserves it. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def ordinaryZeroLiftProductIso (U V : RVFiniteObject (M := M) S 0) :
    vfFiniteProductObject (rawRVSpace (M := M) 1)
      (rvLiftFiniteObject (rawRVSpace (M := M) 1) U) (rvLiftFiniteObject (rawRVSpace (M := M) 1) V) ≅
      rvLiftFiniteObject (rawRVSpace (M := M) 1) (rvFiniteProductObject U V) := by
  let A := mixedProductDomain (rvLift U.obj) (rvLift V.obj)
  let B := rvLift (rvProductObject U.obj V.obj)
  let f : Map A B := Map.inclusion (fun p hp => (ordinary_lift_product_domain U.obj V.obj p).mpr hp)
  have hf : Function.Bijective f := by
    constructor
    · intro p q h
      exact Subtype.ext (congrArg (fun z : B => z.val) h)
    · intro p
      exact ⟨⟨p.val,(ordinary_lift_product_domain U.obj V.obj p.val).mp p.property⟩,rfl⟩
  apply ObjectProperty.isoMk
  apply ObjectProperty.isoMk
  exact DefinableSetCat.isoOfBijective f hf

def zeroVFVolumeClassesProduct (C : BaseContext M)
    (a b : ZeroVFVolumeIsoClasses C) : ZeroVFVolumeIsoClasses C :=
  Quotient.map₂ (vfFiniteProductObject (rawRVSpace (M := M) 1)) (by
    rintro A A' ⟨f⟩ B B' ⟨g⟩
    exact ⟨ordinaryFiniteProductIso f g⟩) a b

theorem zero_volume_lift_on_classes_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (a b : RVVolumeBlowupClasses hc C 0) :
    zeroVolumeLiftOnClasses hc C (rvVolumeBlowupClassesProduct hc C 0 0 a b) =
      zeroVFVolumeClassesProduct C (zeroVolumeLiftOnClasses hc C a) (zeroVolumeLiftOnClasses hc C b) := by
  induction a using Quotient.inductionOn with
  | h U =>
    induction b using Quotient.inductionOn with
    | h V => exact Quotient.sound ⟨(ordinaryZeroLiftProductIso U V).symm⟩

theorem zero_volume_integration_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (a b : ZeroVFVolumeIsoClasses C) :
    zeroVolumeIntegrationEquiv hc C (zeroVFVolumeClassesProduct C a b) =
      rvVolumeBlowupClassesProduct hc C 0 0 (zeroVolumeIntegrationEquiv hc C a) (zeroVolumeIntegrationEquiv hc C b) := by
  let E := zeroVolumeIntegrationEquiv hc C
  apply E.symm.injective
  change E.symm (E (zeroVFVolumeClassesProduct C a b)) =
    zeroVolumeLiftOnClasses hc C (rvVolumeBlowupClassesProduct hc C 0 0 (E a) (E b))
  rw [E.symm_apply_apply,zero_volume_lift_on_classes_product]
  change zeroVFVolumeClassesProduct C a b = zeroVFVolumeClassesProduct C (E.symm (E a)) (E.symm (E b))
  rw [E.symm_apply_apply,E.symm_apply_apply]

end IntegrationInACVF.Section7
