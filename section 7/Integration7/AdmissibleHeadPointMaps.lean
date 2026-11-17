module

public import Integration7.AdmissibleHeadVolumeFactors
public import Integration7.BasicVolumeRelationObjects
public import Integration7.GradedVolumeProducts
public import Section4.RVProduct

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual label bijection from an admissible object to its head
factor times the degree-one point. Its full volume tuple is computed
explicitly; compensating the last coordinate is a density calculation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def admissibleHeadPointPair
    (C : BaseContext M) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) (k+1)) :
    Map U.underlying.obj.domain
      (U.underlying.obj.domain.prod (degreeOnePointVolumeObject (C.base : Set M)).underlying.obj.domain) :=
  (Map.id U.underlying.obj.domain).pair
    ((rvCoordinateSelectMap (C.base : Set M) (Fin.elim0 : Fin 0 → Fin (k+2))).comp U.underlying.obj.volume)

theorem admissible_head_point_pair_bijective
    (C : BaseContext M) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) (k+1)) :
    Function.Bijective (admissibleHeadPointPair C U) := by
  constructor
  · intro u v h
    exact Subtype.ext (congrArg (fun p => p.val.1) h)
  · intro p
    refine ⟨⟨p.val.1,p.property.1⟩,?_⟩
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      exact Fin.elim0 i

def admissibleHeadPointMap
    (C : BaseContext M) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) (k+1))
    (h : BlowupAdmissible U) :
    Map U.underlying.obj.domain
      (((admissibleHeadVolumeFactor C U h).prod (degreeOnePointVolumeObject (C.base : Set M))).underlying.obj.domain) :=
  ((rvPack U.underlying.obj.domain (degreeOnePointVolumeObject (C.base : Set M)).underlying.obj.domain).toImage).comp
    (admissibleHeadPointPair C U)

theorem admissible_head_point_map_bijective
    (C : BaseContext M) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) (k+1))
    (h : BlowupAdmissible U) : Function.Bijective (admissibleHeadPointMap C U h) :=
  (rvPackToImage_bijective _ _).comp (admissible_head_point_pair_bijective C U)

theorem admissible_head_point_unpack
    (C : BaseContext M) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) (k+1))
    (h : BlowupAdmissible U) (u : U.underlying.obj.domain) :
    rvUnpack U.underlying.obj.domain (degreeOnePointVolumeObject (C.base : Set M)).underlying.obj.domain
      (admissibleHeadPointMap C U h u) = admissibleHeadPointPair C U u :=
  rvUnpack_pack _ _ _

theorem admissible_head_point_map_coordinates
    (C : BaseContext M) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) (k+1))
    (h : BlowupAdmissible U) (u : U.underlying.obj.domain) :
    ((admissibleHeadVolumeFactor C U h).prod (degreeOnePointVolumeObject (C.base : Set M))).underlying.obj.value
      (admissibleHeadPointMap C U h u) =
      Fin.append (U.underlying.obj.value u ∘ Fin.castSucc) (fun _ : Fin 1 => 1) := by
  change Fin.append
    (U.underlying.obj.value (Map.prodFst _ _
      (rvUnpack U.underlying.obj.domain (degreeOnePointVolumeObject (C.base : Set M)).underlying.obj.domain
        (admissibleHeadPointMap C U h u))) ∘ Fin.castSucc) (fun _ : Fin 1 => 1) = _
  rw [admissible_head_point_unpack]
  rfl

theorem admissible_head_point_map_density
    (C : BaseContext M) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) (k+1))
    (h : BlowupAdmissible U) (u : U.underlying.obj.domain) :
    ((admissibleHeadVolumeFactor C U h).prod (degreeOnePointVolumeObject (C.base : Set M))).form.value
      (admissibleHeadPointMap C U h u) =
      U.form.value u * U.underlying.obj.value u (Fin.last (k+1)) := by
  change ((admissibleHeadVolumeFactor C U h).form.value
    (Map.prodFst _ _ (rvUnpack U.underlying.obj.domain
      (degreeOnePointVolumeObject (C.base : Set M)).underlying.obj.domain
        (admissibleHeadPointMap C U h u)))) * 1 = _
  rw [admissible_head_point_unpack,mul_one]
  rfl

end IntegrationInACVF.Section7
