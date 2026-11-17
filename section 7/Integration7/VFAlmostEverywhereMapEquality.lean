module

public import Integration7.VFAlmostEverywhereGenericValues
public import Integration7.DefinableMapPreimages

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Agreement of actual definable maps at every generic full VF tuple
descends to agreement outside one original-base definable VF-small set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}

theorem vf_almost_everywhere_maps_eq_of_generic
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    {Q : Space LRV M} {B : DefSet Q (C.base : Set M)} (f g : Map A B)
    (hGeneric : ∀ p : A, AlgebraicIndependent (vfParameterField (C.base : Set M)) p.val.1 →
      (f p).val = (g p).val) : VFAlmostEverywhere A (fun p => (f p).val = (g p).val) := by
  let D : DefSet (Q.prod Q) (C.base : Set M) := ⟨{q | q.1 ≠ q.2},
    ((Q.definable_prod_iff Q (C.base : Set M) Eq).mpr (Q.relation_eq_definable (C.base : Set M))).compl⟩
  let E := definableMapPreimage (f.pair g) D
  have hEA : E.carrier ⊆ A.carrier := definableMapPreimage_subset _ _
  have hdim : vfDim (rawRVSpace (M := M) 1) E < n := by
    apply mixed_vfDim_lt_of_no_independent hc C.saturated C.small _ (rawRVSpace_rvCoded 1) hn
    intro q hq
    let p : A := ⟨q.val,hEA q.property⟩
    have hNE := (mem_definableMapPreimage (f.pair g) D p).mp q.property
    exact hNE (hGeneric p hq)
  refine ⟨E,hEA,hdim,?_⟩
  intro p hp
  by_contra hNE
  exact hp ((mem_definableMapPreimage (f.pair g) D p).mpr hNE)

end IntegrationInACVF.Section7
