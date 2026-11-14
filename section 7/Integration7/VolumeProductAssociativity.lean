import Integration7.VolumeProductPointwise
import Integration7.VolumeDegreeTransport

/-! Rebracketing changes no coordinate order. The actual product
associator preserves both the coordinates and the multiplied density. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

set_option allowUnsafeReducibility true in
attribute [local reducible] PositiveRVVolumeObject.prod rvFiniteProductObject

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m l : ℕ}

theorem positiveProduct_degree_assoc (n m l : ℕ) :
    ((((n+1)+m)+1)+l) = (n+1)+((m+1)+l) := by omega

theorem volumeProductAssoc_density
    (U : PositiveRVVolumeObject (M := M) S n) (V : PositiveRVVolumeObject (M := M) S m)
    (W : PositiveRVVolumeObject (M := M) S l)
    (x : ((U.prod V).prod W).underlying.obj.domain) :
    (U.prod (V.prod W)).form.value
      (rvProductAssocMap U.underlying.obj V.underlying.obj W.underlying.obj x) =
        ((U.prod V).prod W).form.value x := by
  obtain ⟨uv,w,rfl⟩ := exists_rvPackPair (U.prod V).underlying.obj.domain W.underlying.obj.domain x
  obtain ⟨u,v,rfl⟩ := exists_rvPackPair U.underlying.obj.domain V.underlying.obj.domain uv
  rw [rvProductAssocMap_pair]
  rw [positiveProduct_density_pair,positiveProduct_density_pair,
    positiveProduct_density_pair,positiveProduct_density_pair]
  exact (mul_assoc _ _ _).symm

def volumeProductAssocIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) n)
    (V : PositiveRVVolumeObject (M := M) (C.base : Set M) m)
    (W : PositiveRVVolumeObject (M := M) (C.base : Set M) l) :
    RVVolumeIso ((U.prod V).prod W)
      ((U.prod (V.prod W)).reindexDegree (positiveProduct_degree_assoc n m l)) := by
  let e := rvProductAssocReindexedIso U.underlying.obj V.underlying.obj W.underlying.obj
  apply RVVolumeIso.of_preserving_coordinates_full hc C (rvFiniteIsoOfAmbient e)
  · intro x
    obtain ⟨uv,w,rfl⟩ := exists_rvPackPair (U.prod V).underlying.obj.domain W.underlying.obj.domain x
    obtain ⟨u,v,rfl⟩ := exists_rvPackPair U.underlying.obj.domain V.underlying.obj.domain uv
    change (rvProductObject U.underlying.obj (rvProductObject V.underlying.obj W.underlying.obj)).value
      (rvProductAssocMap U.underlying.obj V.underlying.obj W.underlying.obj
        (rvPackPair (U.prod V).underlying.obj.domain W.underlying.obj.domain
          (rvPackPair U.underlying.obj.domain V.underlying.obj.domain u v) w)) ∘
      finCongr (congrArg Nat.succ (positiveProduct_degree_assoc n m l)) = _
    rw [rvProductAssocMap_pair,rvProductObject_value_pair,rvProductObject_value_pair,
      rvProductObject_value_pair,rvProductObject_value_pair]
    exact (Fin.append_assoc (U.underlying.obj.value u) (V.underlying.obj.value v)
      (W.underlying.obj.value w)).symm
  · exact volumeProductAssoc_density U V W

end IntegrationInACVF.Section7
