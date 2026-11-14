import Integration7.MixedJacobianRestriction

/-! An actual almost-everywhere volume isomorphism consists of a full
volume-preserving bijection between definable subdomains with VF-small
complements. No finiteness or volume law is replaced by a formal relation. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

structure VFVolumeIso (U V : PositiveVFVolumeObject (M := M) S k) where
  source : DefSet (rawMixedSpace (M := M) (k + 1) U.arity) S
  target : DefSet (rawMixedSpace (M := M) (k + 1) V.arity) S
  source_subset : source.carrier ⊆ U.domain.carrier
  target_subset : target.carrier ⊆ V.domain.carrier
  source_complement_small : vfDim (rawRVSpace (M := M) 1) (U.domain.sdiff source) < k + 1
  target_complement_small : vfDim (rawRVSpace (M := M) 1) (V.domain.sdiff target) < k + 1
  bijection : VFVolumeBijection (U.restrict source source_subset) (V.restrict target target_subset)

def VFVolumeIso.of_bijection
    {U V : PositiveVFVolumeObject (M := M) S k} (f : VFVolumeBijection U V) :
    VFVolumeIso U V where
  source := U.domain
  target := V.domain
  source_subset := Set.Subset.refl _
  target_subset := Set.Subset.refl _
  source_complement_small := by
    have he : U.domain.sdiff U.domain = DefSet.empty _ S := by
      apply DefSet.eq_of_carrier_eq
      exact Set.diff_self
    rw [he]
    exact (Dimension.dim_empty rawVFSpace
      (AuxiliaryCoordinates.space (rawRVSpace (M := M) 1)) (.rv U.arity)).trans_lt
        (Nat.zero_lt_succ k)
  target_complement_small := by
    have he : V.domain.sdiff V.domain = DefSet.empty _ S := by
      apply DefSet.eq_of_carrier_eq
      exact Set.diff_self
    rw [he]
    exact (Dimension.dim_empty rawVFSpace
      (AuxiliaryCoordinates.space (rawRVSpace (M := M) 1)) (.rv V.arity)).trans_lt
        (Nat.zero_lt_succ k)
  bijection := ⟨f.map, f.bijective, f.preserves⟩

def VFVolumeIso.refl
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k) : VFVolumeIso U U :=
  .of_bijection (.refl hc C U)

def VFVolumeIso.symm
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k}
    (f : VFVolumeIso U V) : VFVolumeIso V U where
  source := f.target
  target := f.source
  source_subset := f.target_subset
  target_subset := f.source_subset
  source_complement_small := f.target_complement_small
  target_complement_small := f.source_complement_small
  bijection := f.bijection.symm hc C

end IntegrationInACVF.Section7
