module

public import Integration7.DefinableMapDisagreements
public import Integration7.SmallExtendedRVExceptions

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Almost-everywhere equality of two original-base maps descends from
a containing context, by parameter invariance of the disagreement locus. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a b n : ℕ}

theorem rv_maps_equal_ae_descend
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M))
    {A : DefSet (rawRVSpace (M := M) a) (C.base : Set M)}
    {B : DefSet (rawRVSpace (M := M) b) (C.base : Set M)} (f g : Map A B)
    (h : RVAlmostEverywhere (A.extend hCD) n (fun u => (f ⟨u.val,u.property⟩).val = (g ⟨u.val,u.property⟩).val)) :
    RVAlmostEverywhere A n (fun u => (f u).val = (g u).val) := by
  classical
  obtain ⟨E,hEA,hEd,hE⟩ := h
  let Z := mapDisagreementLocus f g
  have hZA : Z.carrier ⊆ A.carrier := Set.sdiff_subset
  have hZE : Z.carrier ⊆ E.carrier := by
    intro x hx
    by_contra he
    exact (mem_mapDisagreementLocus f g ⟨x,hZA hx⟩).mp hx (hE ⟨x,hZA hx⟩ he)
  have hCsmall : Cardinal.mk (C.base : Set M) < D.κ :=
    (Cardinal.mk_le_mk_of_subset hCD).trans_lt D.small
  have hZd := rvDim_lt_of_small_extended_exception hc D hCD hCsmall D.small Z E hZE hEd
  refine ⟨Z,hZA,hZd,?_⟩
  intro u hu
  by_contra he
  exact hu ((mem_mapDisagreementLocus f g u).mpr he)

end IntegrationInACVF.Section7
