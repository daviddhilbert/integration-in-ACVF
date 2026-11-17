module

public import Integration7.OrdinaryZeroLiftIsomorphisms
public import Integration7.OrdinaryFiniteLiftSurjectivity
public import Integration7.AllDegreeVolumeClasses

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual ordinary VF[0] isomorphism classes. The ordinary RV[0]
lift, with no density or positive-degree blowup, is a bijection of classes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def zeroVFVolumeIsoSetoid (C : BaseContext M) : Setoid (VFVolumeObject (M := M) (C.base : Set M) 0) where
  r A B := Nonempty (A ≅ B)
  iseqv := ⟨fun A => ⟨Iso.refl A⟩,fun ⟨e⟩ => ⟨e.symm⟩,fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

abbrev ZeroVFVolumeIsoClasses (C : BaseContext M) := Quotient (zeroVFVolumeIsoSetoid C)

def zeroVFVolumeIsoClass (C : BaseContext M) (A : VFVolumeObject (M := M) (C.base : Set M) 0) :
    ZeroVFVolumeIsoClasses C := Quotient.mk _ A

def zeroVolumeLiftOnClasses (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    RVVolumeBlowupClasses hc C 0 → ZeroVFVolumeIsoClasses C :=
  Quotient.lift (fun U => zeroVFVolumeIsoClass C (rvLiftFiniteObject (rawRVSpace (M := M) 1) U)) (by
    rintro U V ⟨e⟩
    exact Quotient.sound ⟨ordinaryZeroLiftIsoOfRVIso e⟩)

theorem zero_volume_lift_on_classes_bijective
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    Function.Bijective (zeroVolumeLiftOnClasses hc C) := by
  constructor
  · intro a b
    induction a using Quotient.inductionOn with
    | h U =>
      induction b using Quotient.inductionOn with
      | h V =>
        intro h
        obtain ⟨e⟩ := Quotient.exact h
        exact Quotient.sound ⟨ordinaryRVIsoOfZeroLiftIso e⟩
  · intro a
    induction a using Quotient.inductionOn with
    | h A =>
      obtain ⟨U,⟨e⟩⟩ := ordinary_finite_lift_presentation_exists hc C A
      exact ⟨rvVolumeBlowupClass hc C (n := 0) U,Quotient.sound ⟨e.symm⟩⟩

def zeroVolumeIntegrationEquiv
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    ZeroVFVolumeIsoClasses C ≃ RVVolumeBlowupClasses hc C 0 :=
  (Equiv.ofBijective (zeroVolumeLiftOnClasses hc C) (zero_volume_lift_on_classes_bijective hc C)).symm

end IntegrationInACVF.Section7
