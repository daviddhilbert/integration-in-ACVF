module

public import Integration7.RVMapEqualityDescent
public import Section9.GenericRVJacobian

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! An RV Jacobian equation whose map and prescribed value are defined
over the original base descends from a containing context. Compare with
the original-base generic Jacobian and descend its disagreement locus. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem rv_jacobian_ae_descend
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M)) (hn : 0 < n)
    {U V : RVFiniteObject (M := M) (C.base : Set M) n} (e : U ≅ V)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero)
    (ρ : Map U.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) (C.base : Set M)))
    (h : RVAlmostEverywhere (U.obj.domain.extend hCD) n (fun u =>
      IsRVJacobianAt (volumeCorrespondence (finiteIsoMap e)).carrier
        (U.obj.value ⟨u.val,u.property⟩) (V.obj.value (finiteIsoMap e ⟨u.val,u.property⟩))
        ((ρ ⟨u.val,u.property⟩).val 0))) :
    RVAlmostEverywhere U.obj.domain n (fun u =>
      IsRVJacobianAt (volumeCorrespondence (finiteIsoMap e)).carrier
        (U.obj.value u) (V.obj.value (finiteIsoMap e u)) ((ρ u).val 0)) := by
  obtain ⟨ω,X,hX,hd,hω⟩ := exists_definable_generic_RVJacobian hc C hn e hU hV
  have hGeneric : RVAlmostEverywhere U.obj.domain n (fun u =>
      IsRVJacobianAt (volumeCorrespondence (finiteIsoMap e)).carrier
        (U.obj.value u) (V.obj.value (finiteIsoMap e u)) ((ω u).val 0)) := ⟨X,hX,hd,hω⟩
  have hEqD : RVAlmostEverywhere (U.obj.domain.extend hCD) n
      (fun u => (ω ⟨u.val,u.property⟩).val = (ρ ⟨u.val,u.property⟩).val) := by
    apply ((hGeneric.extend hCD).and hc D h).mono
    intro u hu
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact hu.1.unique hu.2
  have hEq := rv_maps_equal_ae_descend hc C D hCD ω ρ hEqD
  apply (hGeneric.and hc C hEq).mono
  intro u hu
  have hv := congrFun hu.2 0
  exact hv ▸ hu.1

end IntegrationInACVF.Section7
