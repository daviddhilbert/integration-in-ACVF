module

public import Integration7.OrdinaryFiniteLiftSurjectivity
public import Section4.VFAllIsomorphismClasses
public import Section4.VFCoproductBounds

@[expose] public section

/-! Genuine ordinary finite VF coproducts respect isomorphisms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

def ordinaryFiniteAmbientIso {S : Set M}
    {A B : VFFiniteObject (rawRVSpace (M := M) 1) S n} (f : A ≅ B) : A.obj.obj ≅ B.obj.obj :=
  (vfDimensionProperty (rawRVSpace (M := M) 1) S n).ι.mapIso
    ((vfBoundedFiniteProperty (rawRVSpace (M := M) 1) S n).ι.mapIso f)

def ordinaryFiniteCoprodIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A A' B B' : VFFiniteObject (rawRVSpace (M := M) 1) (C.base : Set M) n}
    (f : A ≅ A') (g : B ≅ B') :
    vfFiniteCoprodObject hc C.saturated C.small (rawRVSpace (M := M) 1) (rawRVSpace_rvCoded 1) A B ≅
      vfFiniteCoprodObject hc C.saturated C.small (rawRVSpace (M := M) 1) (rawRVSpace_rvCoded 1) A' B' := by
  apply ObjectProperty.isoMk
  apply ObjectProperty.isoMk
  let iA := colimit.isoColimitCocone ⟨_,vfAllCoprodIsColimit A.obj.obj B.obj.obj⟩
  let iB := colimit.isoColimitCocone ⟨_,vfAllCoprodIsColimit A'.obj.obj B'.obj.obj⟩
  exact iA.symm.trans ((coprod.mapIso (ordinaryFiniteAmbientIso f) (ordinaryFiniteAmbientIso g)).trans iB)

end IntegrationInACVF.Section7
