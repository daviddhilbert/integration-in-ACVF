module

public import Integration7.HKRVVolumeProducts
public import Integration7.AdmissibleHeadPointIsomorphisms

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The missing degree-one head factor is a genuine weighted zero object.
Dropping the last coordinate retains its contribution in the form. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open scoped BigOperators

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def degreeOneHeadFactor (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) 0) (h : BlowupAdmissible U) :
    ZeroRVVolumeObject (M := M) (C.base : Set M) where
  underlying := admissibleHeadFiniteObject C U h
  form := U.form.mul {
    map := (rvCoordinateSelectMap (C.base : Set M) (fun _ : Fin 1 => Fin.last 0)).comp
      U.underlying.obj.volume
    nonzero u := h.nonzero u }

set_option allowUnsafeReducibility true in
attribute [local reducible] degreeOneHeadFactor zeroProduct multiplyForm
  PositiveRVVolumeObject.zero_prod rvFiniteProductObject admissibleHeadFiniteObject

@[simp] theorem degreeOneHeadFactor_density (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) 0) (h : BlowupAdmissible U)
    (u : U.underlying.obj.domain) :
    (degreeOneHeadFactor C U h).form.value u =
      U.form.value u * U.underlying.obj.value u (Fin.last 0) := rfl

def degreeOneHeadPointPair (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) 0) :
    Map U.underlying.obj.domain
      (U.underlying.obj.domain.prod (degreeOnePointVolumeObject (C.base : Set M)).underlying.obj.domain) :=
  (Map.id U.underlying.obj.domain).pair
    ((rvCoordinateSelectMap (C.base : Set M) (Fin.elim0 : Fin 0 → Fin 1)).comp U.underlying.obj.volume)

theorem degreeOneHeadPointPair_bijective (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) 0) :
    Function.Bijective (degreeOneHeadPointPair C U) := by
  constructor
  · intro u v he
    exact Subtype.ext (congrArg (fun p => p.val.1) he)
  · intro p
    refine ⟨⟨p.val.1, p.property.1⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      exact i.elim0

def degreeOneHeadPointMap (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) 0) (h : BlowupAdmissible U) :
    Map U.underlying.obj.domain
      (zeroProduct (degreeOneHeadFactor C U h) (degreeOnePointVolumeObject (C.base : Set M))).underlying.obj.domain :=
  (rvPack U.underlying.obj.domain (degreeOnePointVolumeObject (C.base : Set M)).underlying.obj.domain).toImage.comp
    (degreeOneHeadPointPair C U)

theorem degreeOneHeadPointMap_bijective (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) 0) (h : BlowupAdmissible U) :
    Function.Bijective (degreeOneHeadPointMap C U h) :=
  (rvPackToImage_bijective _ _).comp (degreeOneHeadPointPair_bijective C U)

theorem degreeOneHeadPointMap_unpack (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) 0) (h : BlowupAdmissible U)
    (u : U.underlying.obj.domain) :
    rvUnpack U.underlying.obj.domain (degreeOnePointVolumeObject (C.base : Set M)).underlying.obj.domain
      (degreeOneHeadPointMap C U h u) = degreeOneHeadPointPair C U u := rvUnpack_pack _ _ _

theorem degreeOneHeadPointMap_coordinates (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) 0) (h : BlowupAdmissible U)
    (u : U.underlying.obj.domain) :
    (zeroProduct (degreeOneHeadFactor C U h) (degreeOnePointVolumeObject (C.base : Set M))).underlying.obj.value
      (degreeOneHeadPointMap C U h u) = fun _ => 1 := by
  rw [zeroProduct_coordinates]
  rfl

theorem degreeOneHeadPointMap_density (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) 0) (h : BlowupAdmissible U)
    (u : U.underlying.obj.domain) :
    (zeroProduct (degreeOneHeadFactor C U h) (degreeOnePointVolumeObject (C.base : Set M))).form.value
      (degreeOneHeadPointMap C U h u) = U.form.value u * U.underlying.obj.value u (Fin.last 0) := by
  rw [zeroProduct_density]
  change (degreeOneHeadFactor C U h).form.value
    (Map.prodFst U.underlying.obj.domain (degreeOnePointVolumeObject (C.base : Set M)).underlying.obj.domain
      (rvUnpack U.underlying.obj.domain (degreeOnePointVolumeObject (C.base : Set M)).underlying.obj.domain
        (degreeOneHeadPointMap C U h u))) * 1 = _
  rw [degreeOneHeadPointMap_unpack, mul_one]
  rfl

theorem degreeOneHeadPointMap_essential (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) 0) (h : BlowupAdmissible U)
    (u : U.underlying.obj.domain) :
    u.val ∈ (rvEssentialLabels U.underlying.obj).carrier ↔
      (degreeOneHeadPointMap C U h u).val ∈ (rvEssentialLabels
        (zeroProduct (degreeOneHeadFactor C U h) (degreeOnePointVolumeObject (C.base : Set M))).underlying.obj).carrier := by
  rw [mem_rvEssentialLabels, mem_rvEssentialLabels, degreeOneHeadPointMap_coordinates]
  constructor
  · intro _ _
    exact (rv_nonzero_iff_raw _).mp one_ne_zero
  · intro _ i
    have hi : i = Fin.last 0 := Fin.fin_one_eq_zero i
    rw [hi]
    exact (rv_nonzero_iff_raw _).mp (h.nonzero u)

def degreeOneHeadPointVolumeIso (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) 0) (h : BlowupAdmissible U) :
    RVVolumeIso U (zeroProduct (degreeOneHeadFactor C U h) (degreeOnePointVolumeObject (C.base : Set M))) := by
  let V := zeroProduct (degreeOneHeadFactor C U h) (degreeOnePointVolumeObject (C.base : Set M))
  let e : U.essential ≅ V.essential := finiteEssentialIsoOfFullBijection (degreeOneHeadPointMap C U h)
    (degreeOneHeadPointMap_bijective C U h) (degreeOneHeadPointMap_essential C U h)
  apply RVVolumeIso.of_gamma_of_lower_rvDim e (admissible_essential_dimension_lt C U h)
  intro u
  apply gammaVolumeEquation_of_weight e u
  let u0 : U.underlying.obj.domain := ⟨u.val, rvEssentialLabels_subset U.underlying.obj u.property⟩
  change RVOperations.absoluteHom (U.form.value u0) * (∏ i, RVOperations.absoluteHom (U.underlying.obj.value u0 i)) =
    RVOperations.absoluteHom (V.form.value (degreeOneHeadPointMap C U h u0)) *
      (∏ i, RVOperations.absoluteHom (V.underlying.obj.value (degreeOneHeadPointMap C U h u0) i))
  rw [degreeOneHeadPointMap_density, degreeOneHeadPointMap_coordinates, map_mul,
    Fin.prod_univ_one, Fin.prod_univ_one, map_one, mul_one]
  rfl

end IntegrationInACVF.Section7.HK
