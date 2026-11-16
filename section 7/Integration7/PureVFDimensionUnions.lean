module

public import Integration7.VFBaseDimensionBounds
public import Section4.VFUnions

@[expose] public section

/-! Finite unions of definable pure VF exceptional sets have the
maximum VF dimension, via their actual constant-RV graph presentations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def pureVFGraphMap (E : DefSet (rawVFSpace (M := M) n) S) :
    Map E (DefSet.univ (rawMixedSpace (M := M) n 1) S) :=
  ((Map.id E).toUniv.pair (rvScalarOne E)).toUniv

theorem pure_vf_graph_map_bijective (E : DefSet (rawVFSpace (M := M) n) S) :
    Function.Bijective (pureVFGraphMap E).toImage := by
  constructor
  · intro x y he
    exact Subtype.ext (congrArg (fun w => w.val.1) he)
  · rintro ⟨p,x,hx⟩
    exact ⟨x,Subtype.ext hx⟩

theorem pure_vf_graph_dimension (E : DefSet (rawVFSpace (M := M) n) S) :
    vfDim (rawRVSpace (M := M) 1) (pureVFGraphMap E).image = vfDim (rawRVSpace (M := M) 1) E := by
  let f := (pureVFGraphMap E).toImage
  have hf := pure_vf_graph_map_bijective E
  have hg : Function.Injective (f.inverse hf) :=
    (Equiv.ofBijective f hf).symm.injective
  exact le_antisymm
    (Dimension.dim_le_of_finiteFibres rawVFSpace (AuxiliaryCoordinates.space (rawRVSpace (M := M) 1))
      (f.inverse hf) (Map.finiteFibres_of_injective hg) ⟨n,pure_vf_has_dimension_bound E⟩)
    (Dimension.dim_le_of_finiteFibres rawVFSpace (AuxiliaryCoordinates.space (rawRVSpace (M := M) 1))
      f (Map.finiteFibres_of_injective hf.1)
      ⟨n,mixed_has_dimension_bound (rawRVSpace (M := M) 1) (pureVFGraphMap E).image⟩)

theorem pure_vf_graph_union (E D : DefSet (rawVFSpace (M := M) n) S) :
    (pureVFGraphMap (E.union D)).image = (pureVFGraphMap E).image.union (pureVFGraphMap D).image := by
  apply DefSet.eq_of_carrier_eq
  ext p
  constructor
  · rintro ⟨x,rfl⟩
    rcases x.property with h | h
    · exact Or.inl ⟨⟨x.val,h⟩,rfl⟩
    · exact Or.inr ⟨⟨x.val,h⟩,rfl⟩
  · rintro (⟨x,rfl⟩ | ⟨x,rfl⟩)
    · exact ⟨⟨x.val,Or.inl x.property⟩,rfl⟩
    · exact ⟨⟨x.val,Or.inr x.property⟩,rfl⟩

theorem pure_vf_dim_union
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (E D : DefSet (rawVFSpace (M := M) n) (C.base : Set M)) :
    vfDim (rawRVSpace (M := M) 1) (E.union D) =
      max (vfDim (rawRVSpace (M := M) 1) E) (vfDim (rawRVSpace (M := M) 1) D) := by
  rw [← pure_vf_graph_dimension (E.union D),pure_vf_graph_union,
    vfDim_union hc C.saturated C.small _ (rawRVSpace_rvCoded 1),
    pure_vf_graph_dimension,pure_vf_graph_dimension]

end IntegrationInACVF.Section7
