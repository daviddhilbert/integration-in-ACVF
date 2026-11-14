import Integration7.EssentialVolumeLiftIsomorphisms
import Integration7.VolumeIsomorphismClasses
import Integration7.GradedVolumeProducts
import Section4.EmptyMaps

/-! Actual positive VF volume-isomorphism classes. Smaller-dimensional
objects vanish, and the canonical lift descends from RV isomorphism
classes over the original generated base. No kernel theorem is assumed. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def PositiveVFVolumeObject.empty (S : Set M) (k : ℕ) : PositiveVFVolumeObject (M := M) S k where
  arity := 0
  domain := DefSet.empty (rawMixedSpace (M := M) (k + 1) 0) S
  finite_labels _ := Set.finite_empty
  form := VolumeForm.one _

def vfVolumeIsoOfSmall {U V : PositiveVFVolumeObject (M := M) S k}
    (hU : vfDim (rawRVSpace (M := M) 1) U.domain < k + 1)
    (hV : vfDim (rawRVSpace (M := M) 1) V.domain < k + 1) : VFVolumeIso U V where
  source := DefSet.empty _ S
  target := DefSet.empty _ S
  source_subset := Set.empty_subset _
  target_subset := Set.empty_subset _
  source_complement_small := by
    have he : U.domain.sdiff (DefSet.empty _ S) = U.domain :=
      DefSet.eq_of_carrier_eq Set.sdiff_empty
    rw [he]
    exact hU
  target_complement_small := by
    have he : V.domain.sdiff (DefSet.empty _ S) = V.domain :=
      DefSet.eq_of_carrier_eq Set.sdiff_empty
    rw [he]
    exact hV
  bijection := {
    map := Map.emptyTo _
    bijective := Map.bijective_of_empty _ rfl rfl
    preserves := VFAlmostEverywhere.of_forall (Nat.zero_lt_succ k) (fun p => False.elim p.property) }

abbrev PositiveVFVolumeIsoClasses
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (k : ℕ) :=
  Quotient (positiveVFVolumeIsoSetoid hc C k)

def positiveVFVolumeIsoClass
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {k : ℕ}
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k) :
    PositiveVFVolumeIsoClasses hc C k := Quotient.mk _ U

instance positiveVFVolumeIsoClassesZero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (k : ℕ) :
    Zero (PositiveVFVolumeIsoClasses hc C k) :=
  ⟨positiveVFVolumeIsoClass hc C (.empty (C.base : Set M) k)⟩

theorem positiveVFVolumeIsoClass_eq_iff
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {k : ℕ}
    {U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k} :
    positiveVFVolumeIsoClass hc C U = positiveVFVolumeIsoClass hc C V ↔ Nonempty (VFVolumeIso U V) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound (s := positiveVFVolumeIsoSetoid hc C k) h⟩

theorem positiveVFVolumeIsoClass_small
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {k : ℕ}
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    (hd : vfDim (rawRVSpace (M := M) 1) U.domain < k + 1) :
    positiveVFVolumeIsoClass hc C U = 0 := by
  have he : vfDim (rawRVSpace (M := M) 1)
      (PositiveVFVolumeObject.empty (M := M) (C.base : Set M) k).domain < k + 1 :=
    (Dimension.dim_empty rawVFSpace (AuxiliaryCoordinates.space (rawRVSpace (M := M) 1)) (.rv 0)).trans_lt
      (Nat.zero_lt_succ k)
  exact Quotient.sound ⟨vfVolumeIsoOfSmall hd he⟩

def positiveVolumeLiftOnIsoClasses
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (k : ℕ)
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase ⟨(C.base : Set M), Ξ⟩) :
    PositiveVolumeIsoClasses hc C k → PositiveVFVolumeIsoClasses hc C k :=
  Quotient.lift (fun U => positiveVFVolumeIsoClass hc C (rvVolumeLift U)) (by
    rintro U V ⟨e⟩
    exact Quotient.sound (e.nonempty_full_lift_iso hc C Ξ hGenerated))

@[simp] theorem positiveVolumeLiftOnIsoClasses_class
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (k : ℕ)
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase ⟨(C.base : Set M), Ξ⟩)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    positiveVolumeLiftOnIsoClasses hc C k Ξ hGenerated (positiveVolumeIsoClass hc C U) =
      positiveVFVolumeIsoClass hc C (rvVolumeLift U) := rfl

end IntegrationInACVF.Section7
