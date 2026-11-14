import Integration7.VFVolumeObjects
import Section9.SpecialJacobianGeneric

/-! Original-base conversion from actual raw mixed domains to the
predecessor's Section 5 point presentations. Normalization changes no
parameters or underlying points in a canonical model. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section8
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a : ℕ}

def nativeMixedVolumeDomain (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawMixedSpace (M := M) n a) S) :
    SpecialTransformations.Section5.DefSet (M := M) S n a := by
  let D := (rawMixedSpace (M := M) n a).preimage A.carrier
  let N := CanonicalStructure.normalize (M := M)
  letI : LRV.Structure M := sM
  have hN : @Set.Definable M S LRV N (Fin n ⊕ Fin a) D :=
    Eq.mp (congrArg (fun T : LRV.Structure M =>
      @Set.Definable M S LRV T (Fin n ⊕ Fin a) D)
      (normalize_eq_of_isCanonical hc).symm) A.definable
  have hraw : SpecialTransformations.Section5.SetDefinable
      (SpecialTransformations.Section5.rawPointSpace (M := M) n a) S A.carrier := hN
  let W := SpecialTransformations.Section5.PresentedSet.univ
    (SpecialTransformations.Section5.pointSpace (M := M) n a) S
  let F := SpecialTransformations.Section5.rawPointMap W
  have h := SpecialTransformations.Section5.Map.definable_preimage F hraw
  refine SpecialTransformations.Section5.PresentedSet.mk A.carrier ?_
  convert h using 1
  ext p
  constructor
  · intro hp
    exact ⟨⟨p, Set.mem_univ _⟩, rfl, hp⟩
  · rintro ⟨p, rfl, hp⟩
    exact hp

@[simp] theorem nativeMixedVolumeDomain_carrier
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawMixedSpace (M := M) n a) S) :
    SpecialTransformations.Section5.carrier (nativeMixedVolumeDomain hc A) = A.carrier := rfl

theorem rawSpecialSet_nativeMixedVolumeDomain
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawMixedSpace (M := M) n a) S) :
    rawSpecialSet hc (nativeMixedVolumeDomain hc A) = A :=
  DefSet.eq_of_carrier_eq rfl

def rawVolumeContractionLabels (hc : CanonicalStructure.IsCanonical (M := M))
    (U : SpecialTransformations.Section5.DefSet (M := M) S 0 a) :
    DefSet (rawRVSpace (M := M) a) S :=
  (Map.snd (rawVFSpace (M := M) 0) (rawRVSpace a) S (rawSpecialSet hc U)).image

theorem mem_rawVolumeContractionLabels
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U : SpecialTransformations.Section5.DefSet (M := M) S 0 a)
    (r : Fin a → CanonicalRV.RVSort M) :
    r ∈ (rawVolumeContractionLabels hc U).carrier ↔
      (Fin.elim0, r) ∈ SpecialTransformations.Section5.carrier U := by
  constructor
  · rintro ⟨p, hp⟩
    have hx : p.val.1 = Fin.elim0 := funext (fun i => Fin.elim0 i)
    have he : p.val = (Fin.elim0, r) := Prod.ext hx hp
    exact he ▸ p.property
  · intro hr
    exact ⟨⟨(Fin.elim0, r), hr⟩, rfl⟩

end IntegrationInACVF.Section7
