module

public import Integration7.OrdinaryFiniteCoproductIsomorphisms
public import Section4.VFProducts

@[expose] public section

/-! Actual ordinary finite VF Cartesian products preserve category
isomorphisms, without changing their ambient VF coordinate tuples. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m : ℕ}

def ordinaryFiniteProductIso
    {A A' : VFFiniteObject (rawRVSpace (M := M) 1) S n}
    {B B' : VFFiniteObject (rawRVSpace (M := M) 1) S m}
    (f : A ≅ A') (g : B ≅ B') :
    vfFiniteProductObject (rawRVSpace (M := M) 1) A B ≅
      vfFiniteProductObject (rawRVSpace (M := M) 1) A' B' := by
  let F := ordinaryFiniteAmbientIso f
  let G := ordinaryFiniteAmbientIso g
  apply ObjectProperty.isoMk
  apply ObjectProperty.isoMk
  refine ⟨vfAllProductHom F.hom G.hom,vfAllProductHom F.inv G.inv,?_,?_⟩
  · rw [← vfAllProductHom_comp,F.hom_inv_id,G.hom_inv_id,vfAllProductHom_id]
    rfl
  · rw [← vfAllProductHom_comp,F.inv_hom_id,G.inv_hom_id,vfAllProductHom_id]
    rfl

end IntegrationInACVF.Section7
