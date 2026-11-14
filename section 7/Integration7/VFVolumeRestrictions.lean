import Integration7.MixedJacobianRestriction
import Integration7.VFCofullSubdomains

/-! Genuine restrictions of full volume-preserving bijections, to an
actual target preimage or to the actual image of a source subdomain. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def VFVolumeBijection.restrictPreimage
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k}
    (f : VFVolumeBijection U V)
    (K : DefSet (rawMixedSpace (M := M) (k + 1) V.arity) (C.base : Set M))
    (hK : K.carrier ⊆ V.domain.carrier) :
    VFVolumeBijection
      (U.restrict (definableMapPreimage f.map K) (definableMapPreimage_subset f.map K))
      (V.restrict K hK) := by
  let L := definableMapPreimage f.map K
  let hL := definableMapPreimage_subset f.map K
  let F : Map L K := (f.map.restrict hL).corestrict (by
    intro p
    exact (mem_definableMapPreimage f.map K ⟨p.val, hL p.property⟩).mp p.property)
  have hF : Function.Bijective F := by
    constructor
    · intro p q he
      have he' := f.bijective.1 (Subtype.ext (congrArg (fun z : K => z.val) he))
      exact Subtype.ext (congrArg (fun z : U.domain => z.val) he')
    · intro q
      obtain ⟨p, hp⟩ := f.bijective.2 ⟨q.val, hK q.property⟩
      have hpL : p.val ∈ L.carrier :=
        (mem_definableMapPreimage f.map K p).mpr (by rw [hp]; exact q.property)
      exact ⟨⟨p.val, hpL⟩, Subtype.ext (congrArg (fun z : V.domain => z.val) hp)⟩
  refine ⟨F, hF, ?_⟩
  exact preservesVFVolume_of_restriction hc C (Nat.zero_lt_succ k) hL f.map F
    (fun _ => rfl) U.form V.form (U.form.restrict hL) (V.form.restrict hK)
    (fun _ => rfl) (fun _ => rfl) f.preserves

def VFVolumeBijection.restrictImage
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k}
    (f : VFVolumeBijection U V)
    (L : DefSet (rawMixedSpace (M := M) (k + 1) U.arity) (C.base : Set M))
    (hL : L.carrier ⊆ U.domain.carrier) :
    VFVolumeBijection (U.restrict L hL)
      (V.restrict (f.map.restrict hL).image (by
        rintro x ⟨p, rfl⟩
        exact (f.map ⟨p.val, hL p.property⟩).property)) := by
  let F := (f.map.restrict hL).toImage
  have hF : Function.Bijective F := by
    constructor
    · intro p q he
      have he' := f.bijective.1 (Subtype.ext (congrArg (fun z : (f.map.restrict hL).image => z.val) he))
      exact Subtype.ext (congrArg (fun z : U.domain => z.val) he')
    · rintro ⟨q, p, hp⟩
      exact ⟨p, Subtype.ext hp⟩
  refine ⟨F, hF, ?_⟩
  exact preservesVFVolume_of_restriction hc C (Nat.zero_lt_succ k) hL f.map F
    (fun _ => rfl) U.form V.form _ _ (fun _ => rfl) (fun _ => rfl) f.preserves

end IntegrationInACVF.Section7
