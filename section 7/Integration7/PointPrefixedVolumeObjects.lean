module

public import Integration7.BasicVolumeRelationObjects
public import Integration7.VolumeProductPointwise
public import Integration7.VolumeRelabeling
public import Integration7.RVVolumeInverse
public import IntegrationSection6.FiniteBlowups
public import Section4.RVIsoTools

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Adjoining the literal volume coordinate one is the genuine product
with the degree-one point. The label domain and density are unchanged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}
variable (C : BaseContext M) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)

private def pointPrefixCoordinates : RVObject (M := M) (C.base : Set M) (1+(k+1)) where
  arity := U.underlying.obj.arity
  domain := U.underlying.obj.domain
  volume := (rvAppendMap (C.base : Set M) 1 (k+1)).comp
    (((rvScalarOne U.underlying.obj.domain).pair U.underlying.obj.volume).toUniv)

private def pointPrefixProjection : Map
    ((degreeOnePointVolumeObject (C.base : Set M)).prod U).underlying.obj.domain U.underlying.obj.domain :=
  (Map.prodSnd (degreeOnePointVolumeObject (C.base : Set M)).underlying.obj.domain U.underlying.obj.domain).comp
    (rvUnpack (degreeOnePointVolumeObject (C.base : Set M)).underlying.obj.domain U.underlying.obj.domain)

private theorem pointPrefixProjection_bijective : Function.Bijective (pointPrefixProjection C U) := by
  let P := degreeOnePointVolumeObject (M := M) (C.base : Set M)
  constructor
  · intro q r h
    apply (rvUnpack_bijective P.underlying.obj.domain U.underlying.obj.domain).1
    apply Subtype.ext
    exact Prod.ext (funext (fun i : Fin 0 => i.elim0)) (congrArg Subtype.val h)
  · intro u
    let p : P.underlying.obj.domain := ⟨Fin.elim0,Set.mem_univ _⟩
    refine ⟨rvPackPair P.underlying.obj.domain U.underlying.obj.domain p u,?_⟩
    change Map.prodSnd _ _ (rvUnpack _ _ (rvPackPair _ _ p u))=u
    rw [rvUnpack_pair]
    rfl

private theorem pointPrefixProjection_coordinates
    (q : ((degreeOnePointVolumeObject (C.base : Set M)).prod U).underlying.obj.domain) :
    (pointPrefixCoordinates C U).value (pointPrefixProjection C U q) =
      ((degreeOnePointVolumeObject (C.base : Set M)).prod U).underlying.obj.value q := by
  let P := degreeOnePointVolumeObject (M := M) (C.base : Set M)
  obtain ⟨p,u,rfl⟩ := exists_rvPackPair P.underlying.obj.domain U.underlying.obj.domain q
  rw [positiveProduct_coordinates_pair,degree_one_point_volume_coordinates]
  change Fin.append (fun _ : Fin 1 => 1)
    (U.underlying.obj.value (Map.prodSnd _ _ (rvUnpack _ _ (rvPackPair _ _ p u)))) = _
  rw [rvUnpack_pair]
  rfl

private def pointPrefixCoordinateIso :
    ((degreeOnePointVolumeObject (C.base : Set M)).prod U).underlying.obj ≅ pointPrefixCoordinates C U :=
  rvIsoOfVolumePreservingBijection (pointPrefixProjection C U) (pointPrefixProjection_bijective C U)
    (pointPrefixProjection_coordinates C U)

def pointPrefixedVolumeObject : PositiveRVVolumeObject (M := M) (C.base : Set M) (1+k) where
  underlying := ⟨pointPrefixCoordinates C U,(finite_volume_iso (pointPrefixCoordinateIso C U)).mp
    ((degreeOnePointVolumeObject (C.base : Set M)).prod U).underlying.property⟩
  form := U.form

theorem point_prefixed_volume_coordinates (u : (pointPrefixedVolumeObject C U).underlying.obj.domain) :
    (pointPrefixedVolumeObject C U).underlying.obj.value u=Fin.append (fun _ : Fin 1 => 1) (U.underlying.obj.value u) := rfl

theorem point_prefixed_volume_density (u : (pointPrefixedVolumeObject C U).underlying.obj.domain) :
    (pointPrefixedVolumeObject C U).form.value u=U.form.value u := rfl

def pointPrefixedVolumeIso (hc : CanonicalStructure.IsCanonical (M := M)) :
    RVVolumeIso (pointPrefixedVolumeObject C U) ((degreeOnePointVolumeObject (C.base : Set M)).prod U) := by
  let P := degreeOnePointVolumeObject (M := M) (C.base : Set M)
  have hForm (q : (P.prod U).underlying.obj.domain) :
      (pointPrefixedVolumeObject C U).form.value (pointPrefixProjection C U q)=(P.prod U).form.value q := by
    obtain ⟨p,u,rfl⟩ := exists_rvPackPair P.underlying.obj.domain U.underlying.obj.domain q
    rw [positiveProduct_density_pair]
    change U.form.value (Map.prodSnd _ _ (rvUnpack _ _ (rvPackPair _ _ p u))) = 1*U.form.value u
    rw [rvUnpack_pair,one_mul]
    rfl
  exact (RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (U := (P.prod U).underlying) (V := (pointPrefixedVolumeObject C U).underlying)
      (pointPrefixCoordinateIso C U)) (pointPrefixProjection_coordinates C U) hForm).symm hc C
end IntegrationInACVF.Section7
