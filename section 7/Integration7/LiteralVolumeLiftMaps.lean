module

public import Integration7.CanonicalLiftVolumePresentations
public import Integration7.SpecialVolumeJacobians
public import Integration7.VFVolumeLifts
public import IntegrationSection6.CanonicalPullbackPresentation

@[expose] public section

/-! Literal Section6 lift presentations give actual raw mixed maps with
identity coordinates. These are the bridge used with special preparations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem literalLift_carrier_eq
    (hc : CanonicalStructure.IsCanonical (M := M)) (U : RVObject (M := M) S n)
    (A : SpecialTransformations.Section5.DefSet (M := M) S n U.arity)
    (h : Section6.PresentsLift U A) :
    (rawSpecialSet hc A).carrier = (rvLift U).carrier := by
  ext p
  exact h p

def literalVolumeLiftMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (U : RVObject (M := M) S n)
    (A : SpecialTransformations.Section5.DefSet (M := M) S n U.arity)
    (h : Section6.PresentsLift U A) : Map (rawSpecialSet hc A) (rvLift U) :=
  Map.inclusion (literalLift_carrier_eq hc U A h).le

theorem literalVolumeLiftMap_bijective
    (hc : CanonicalStructure.IsCanonical (M := M)) (U : RVObject (M := M) S n)
    (A : SpecialTransformations.Section5.DefSet (M := M) S n U.arity)
    (h : Section6.PresentsLift U A) : Function.Bijective (literalVolumeLiftMap hc U A h) := by
  constructor
  · intro p q he
    exact Subtype.ext (congrArg (fun z : rvLift U => z.val) he)
  · intro p
    exact ⟨⟨p.val, (literalLift_carrier_eq hc U A h).ge p.property⟩, rfl⟩

theorem literalVolumeLiftMap_preserves
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : RVObject (M := M) (C.base : Set M) n)
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n U.arity)
    (h : Section6.PresentsLift U A) (hn : 0 < n)
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rvLift U))
    (hω : ∀ p, ω.value p = π.value (literalVolumeLiftMap hc U A h p)) :
    PreservesVFVolume ω π (literalVolumeLiftMap hc U A h) := by
  apply (vfJacobianOne_of_preservesVF hc C hn (literalVolumeLiftMap hc U A h)
    (fun _ => rfl)).mono
  intro p hJ
  exact ⟨1, hJ, by rw [RVOperations.rv_one, mul_one]; exact hω p⟩

end IntegrationInACVF.Section7
